package keeper

import (
	"encoding/json"
	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
	"go.mongodb.org/mongo-driver/bson"
)

var accounts types.AccountsType

// SetAccount set a specific account in the store from its index
func (k Keeper) SetAccount(ctx sdk.Context, account types.Account) {
	storage.CallSaiStorage("save", storage.Request{
		Collection: "account",
		Data:       account,
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	b := k.cdc.MustMarshalBinaryBare(&account)
	store.Set(types.KeyPrefix(account.GetInternalId()), b)
}

// GetAccount returns an account from its index
func (k Keeper) GetAccount(ctx sdk.Context, index string) (val types.Account, found bool) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	//
	//b := store.Get(types.KeyPrefix(index))
	//if b == nil {
	//	return val, false
	//}
	//
	//k.cdc.MustUnmarshalBinaryBare(b, &val)
	//return val, true

	resultAccounts := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"accounts",
		SelectString:   bson.M{
			"internal_id": index,
		},
	})
	_ = json.Unmarshal([]byte(resultAccounts), &accounts)

	if len(accounts) == 0 {
		return val, false
	}

	return accounts[0], true
}

// RemoveAccount removes an account from the store
func (k Keeper) RemoveAccount(ctx sdk.Context, index string) {
	storage.CallSaiStorage("remove", storage.Request{
		Collection: 	"accounts",
		SelectString:   bson.M{
			"internal_id": index,
		},
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	store.Delete(types.KeyPrefix(index))
}

// GetAccountBy returns all account by select criteria
func (k Keeper) GetAccountBy(ctx sdk.Context, criteria interface{}) (list []types.Account) {
	//store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	//iterator := sdk.KVStorePrefixIterator(store, []byte{})
	//
	//defer iterator.Close()
	//
	//for ; iterator.Valid(); iterator.Next() {
	//	var val types.Account
	//	k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
	//	list = append(list, val)
	//}
	//
	//return

	resultAccounts := storage.CallSaiStorage("get", storage.Request{
		Collection: 	"accounts",
		SelectString:   criteria,
	})

	_ = json.Unmarshal([]byte(resultAccounts), &accounts)

	return accounts
}
