package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
)

func (s msgServer) SendClose(ctx context.Context, msg *types.MsgSendClose) (*types.MsgSendCloseResponse, error) {
	if err := validator.ValidateMsgSendClose(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account := s.GetOrCreateAccount(cctx, msg.GetSender())

	if err := core.Close(account.GetId(), msg.GetOrderId()); err != nil {
		return nil, err
	}

	s.SetAccount(cctx, account)

	return &types.MsgSendCloseResponse{}, nil
}
