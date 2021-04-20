package keeper

import (
	"github.com/onomyprotocol/market/x/market/types"
)

var _ types.QueryServer = Keeper{}
