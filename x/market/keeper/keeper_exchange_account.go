package keeper

import (
	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
)

// SetExchangeAccount set a specific account in the store from its index
func (k Keeper) SetExchangeAccount(ctx sdk.Context, account types.ExchangeAccount) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.ExchangeAccountKey))
	b := k.cdc.MustMarshalBinaryBare(&account)
	store.Set(types.KeyPrefix(account.GetId()), b)
}

// GetExchangeAccount returns a account from its index
func (k Keeper) GetExchangeAccount(ctx sdk.Context, index string) (val types.ExchangeAccount, found bool) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.ExchangeAccountKey))

	b := store.Get(types.KeyPrefix(index))
	if b == nil {
		return val, false
	}

	k.cdc.MustUnmarshalBinaryBare(b, &val)
	return val, true
}

// RemoveExchangeAccount removes a account from the store
func (k Keeper) RemoveExchangeAccount(ctx sdk.Context, index string) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.ExchangeAccountKey))
	store.Delete(types.KeyPrefix(index))
}

// GetAllExchangeAccount returns all account
func (k Keeper) GetAllExchangeAccount(ctx sdk.Context) (list []types.ExchangeAccount) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.ExchangeAccountKey))
	iterator := sdk.KVStorePrefixIterator(store, []byte{})

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var val types.ExchangeAccount
		k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
		list = append(list, val)
	}

	return
}

// GetOrCreateExchangeAccount — returns an account (if account doesn't exist it will create an account and return it)
func (k Keeper) GetOrCreateExchangeAccount(ctx sdk.Context, index string) types.ExchangeAccount {
	account, ok := k.GetExchangeAccount(ctx, index)
	if !ok {
		account = core.NewExchangeAccount(index)
		k.SetExchangeAccount(ctx, account)
	}

	return account
}
