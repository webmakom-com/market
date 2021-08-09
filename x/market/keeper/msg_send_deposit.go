package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
)

func (s msgServer) SendOpenAccount(ctx context.Context, msg *types.MsgSendOpenAccount) (*types.MsgSendOpenAccountResponse, error) {
	if err := validator.ValidateMsgSendOpenAccount(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	s.SetAccount(cctx, core.NewAccount(msg.GetSender()))

	return &types.MsgSendOpenAccountResponse{}, nil
}
