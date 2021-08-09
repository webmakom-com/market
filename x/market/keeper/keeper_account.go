package keeper

import (
	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
)

// SetAccount set a specific account in the store from its index
func (k Keeper) SetAccount(ctx sdk.Context, account types.Account) {
	storage.CallSaiStorage("save", storage.Request{
		Collection: "account",
		Data:       account,
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	b := k.cdc.MustMarshalBinaryBare(&account)
	store.Set(types.KeyPrefix(account.GetId()), b)
}

// GetAccount returns an account from its index
func (k Keeper) GetAccount(ctx sdk.Context, index string) (val types.Account, found bool) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))

	b := store.Get(types.KeyPrefix(index))
	if b == nil {
		return val, false
	}

	k.cdc.MustUnmarshalBinaryBare(b, &val)
	return val, true
}

// RemoveAccount removes an account from the store
func (k Keeper) RemoveAccount(ctx sdk.Context, index string) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	store.Delete(types.KeyPrefix(index))
}

// GetAllAccount returns all account
func (k Keeper) GetAllAccount(ctx sdk.Context) (list []types.Account) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.AccountKey))
	iterator := sdk.KVStorePrefixIterator(store, []byte{})

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var val types.Account
		k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
		list = append(list, val)
	}

	return
}

// GetOrCreateAccount — returns an account (if account doesn't exist it will create an account and return it)
func (k Keeper) GetOrCreateAccount(ctx sdk.Context, index string) types.Account {
	account, ok := k.GetAccount(ctx, index)
	if !ok {
		account = core.NewAccount(index)
		k.SetAccount(ctx, account)
	}

	return account
}
