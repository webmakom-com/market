package keeper

import (
	"encoding/json"
	"errors"

	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
	"go.mongodb.org/mongo-driver/bson"
)

type OrdersType []types.Order
type AccountsType []types.Account

var orders OrdersType
var accounts AccountsType

// SetOrder set a specific order in the store from its index
func (k Keeper) SetOrder(ctx sdk.Context, order types.Order) {
	order, err := k.processOrder(order)
	if err != nil {
		return
	}

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.OrderKey))
	b := k.cdc.MustMarshalBinaryBare(&order)
	store.Set(types.KeyPrefix(order.GetInternalId()), b)
}

// GetOrder returns an order from its index
func (k Keeper) GetOrder(ctx sdk.Context, index string) (val types.Order, found bool) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.OrderKey))
	//
	//b := store.Get(types.KeyPrefix(index))
	//if b == nil {
	//	return val, false
	//}
	//k.cdc.MustUnmarshalBinaryBare(b, &val)

	// Get order from mongo by index (internal_id)
	resultOrders := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"orders",
		SelectString:   bson.M{
			"internal_id": index,
		},
	})
	_ = json.Unmarshal([]byte(resultOrders), &orders)

	if len(orders) == 0 {
		return val, false
	}

	return orders[0], true
}

// RemoveOrder Update order with new status by index and status = Open -> Close
func (k Keeper) RemoveOrder(ctx sdk.Context, index string) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.OrderKey))
	//store.Delete(types.KeyPrefix(index))

	// Update order with new status by index and status = Open -> Close
	order, _ := k.GetOrder(ctx, index)
	order.Status = types.OrderStatus_ORDER_TYPE_CLOSE

	storage.CallSaiStorage("update", storage.Request{
		Collection: 	"orders",
		SelectString:   bson.M{
			"internal_id": index,
			"status": types.OrderStatus_ORDER_TYPE_OPEN,
		},
		Data: bson.M{"$set": order},
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.OrderKey))
	b := k.cdc.MustMarshalBinaryBare(&order)
	store.Set(types.KeyPrefix(order.GetInternalId()), b)
}

// GetOrdersBy returns all orders by select criteria
func (k Keeper) GetOrdersBy(ctx sdk.Context, criteria interface{}) (list []types.Order) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.OrderKey))
	//iterator := sdk.KVStorePrefixIterator(store, []byte{})
	//
	//defer iterator.Close()
	//
	//for ; iterator.Valid(); iterator.Next() {
	//	var val types.Order
	//	k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
	//	list = append(list, val)
	//}

	// Get all orders from mongo by criteria
	resultOrders := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"orders",
		SelectString:   criteria,
	})

	_ = json.Unmarshal([]byte(resultOrders), &orders)

	return orders
}

func (k Keeper) processOrder(order types.Order) (types.Order, error) {
	var amm = float64(47000)
	var criteria bson.M

	if order.ExchangeRate < amm {
		criteria = bson.M {
			"ExchRate": bson.M {
				"$gte": order.ExchangeRate, "$lte": amm,
			},
		}
	} else {
		criteria = bson.M {
			"ExchRate": bson.M {
				"$gte": amm, "$lte": order.ExchangeRate,
			},
		}
	}

	// Get order list
	resultOrders := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"orders",
		SelectString:   criteria,
	})
	_ = json.Unmarshal([]byte(resultOrders), &orders)

	// Possible optimisation: Move logic to code instead of query.
	resultAccounts := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"accounts",
		SelectString:   bson.M {
			"AccountId": order.AccountId,
			"Balance." + order.BidCoin: bson.M {
				"$gte": order.Amount,  // + fee
			},
		},
	})
	_ = json.Unmarshal([]byte(resultAccounts), &accounts)

	if len(accounts) == 0 {
		return order, errors.New("insufficient funds")
	}

	// If during processing order is closed,
	// 1. update order status
	// 2. update account balances

	newBalance := float64(10)
	accounts[0].Balance[order.BidCoin] = newBalance

	response := storage.CallSaiStorage("update", storage.Request{
		Collection: "accounts",
		SelectString:   bson.M {
			"AccountId": order.AccountId,
			"Balance." + order.BidCoin: bson.M {
				"$gte": order.Amount,  // + fee
			},
		},
		Data: bson.M{"$set": accounts[0]},
	})

	if response != "" {
		order.Status = types.OrderStatus_ORDER_TYPE_CLOSE

		// Save order status
		storage.CallSaiStorage("save", storage.Request{
			Collection: "orders",
			Data:       order,
		})

		return order, nil
	}

	return order, errors.New("insufficient funds")
}