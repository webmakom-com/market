package keeper

import (
	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

// SetMarket set a specific market in the store from its index
func (k Keeper) SetMarket(ctx sdk.Context, market types.Market) {
	storage.CallSaiStorage("save", storage.Request{
		Collection: "market",
		Data:       market,
	})

	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	b := k.cdc.MustMarshalBinaryBare(&market)
	store.Set(types.KeyPrefix(market.GetPair()), b)
}

// GetMarket returns a market from its index
func (k Keeper) GetMarket(ctx sdk.Context, index string) (val types.Market, found bool) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))

	b := store.Get(types.KeyPrefix(index))
	if b == nil {
		return val, false
	}

	k.cdc.MustUnmarshalBinaryBare(b, &val)
	return val, true
}

// RemoveMarket removes a market from the store
func (k Keeper) RemoveMarket(ctx sdk.Context, index string) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	store.Delete(types.KeyPrefix(index))
}

// GetAllMarket returns all market
func (k Keeper) GetAllMarket(ctx sdk.Context) (list []types.Market) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), types.KeyPrefix(types.MarketKey))
	iterator := sdk.KVStorePrefixIterator(store, []byte{})

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var val types.Market
		k.cdc.MustUnmarshalBinaryBare(iterator.Value(), &val)
		list = append(list, val)
	}

	return
}
