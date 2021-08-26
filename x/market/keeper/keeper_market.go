package keeper

import (
	"encoding/json"
	"go.mongodb.org/mongo-driver/bson"
	"sort"
	"strings"

	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

var markets types.MarketsType

// SetMarket set a specific market in the store from its index
func (k Keeper) SetMarket(ctx sdk.Context, market types.Market) {
	storage.CallSaiStorage("save", storage.Request{
		Collection: "markets",
		Data:       market,
	})

	coins := []string{market.GetCoinA(), market.GetCoinB()}
	sort.Strings(coins)

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	b := k.cdc.MustMarshalBinaryBare(&market)
	store.Set(types.KeyPrefix(strings.Join(coins, "_")), b)
}

// GetMarket returns a market from its index
func (k Keeper) GetMarket(ctx sdk.Context, index string) (val types.Market, found bool) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	//
	//b := store.Get(types.KeyPrefix(index))
	//if b == nil {
	//	return val, false
	//}
	//
	//k.cdc.MustUnmarshalBinaryBare(b, &val)
	//return val, true

	resultMarkets := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"markets",
		SelectString:   bson.M{
			"internal_id": index,
		},
	})
	_ = json.Unmarshal([]byte(resultMarkets), &markets)

	if len(markets) == 0 {
		return val, false
	}

	return markets[0], true
}

// RemoveMarket removes a market from the store
func (k Keeper) RemoveMarket(ctx sdk.Context, index string) {
	storage.CallSaiStorage("remove", storage.Request{
		Collection: 	"markets",
		SelectString:   bson.M{
			"internal_id": index,
		},
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	store.Delete(types.KeyPrefix(index))
}

// GetMarketBy returns all market by select criteria
func (k Keeper) GetMarketBy(ctx sdk.Context, criteria interface{}) (list []types.Market) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	//iterator := sdk.KVStorePrefixIterator(store, []byte{})
	//
	//defer iterator.Close()
	//
	//for ; iterator.Valid(); iterator.Next() {
	//	var val types.Market
	//	k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
	//	list = append(list, val)
	//}
	//
	//return

	resultMarkets := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"accounts",
		SelectString:   criteria,
	})

	_ = json.Unmarshal([]byte(resultMarkets), &markets)

	return markets
}
