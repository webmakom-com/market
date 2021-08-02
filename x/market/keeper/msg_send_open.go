package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
)

func (s msgServer) SendOpen(ctx context.Context, msg *types.MsgSendOpen) (*types.MsgSendOpenResponse, error) {
	if err := validator.ValidateMsgSendOpen(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account := s.GetOrCreateExchangeAccount(cctx, msg.GetSender())

	if err := core.Open(&account, msg.GetAskCoinDenom(), msg.GetBidCoinDenom(), msg.GetOrderType(), msg.GetOrder()); err != nil {
		return nil, err
	}

	s.SetExchangeAccount(cctx, account)

	return &types.MsgSendOpenResponse{}, nil
}
