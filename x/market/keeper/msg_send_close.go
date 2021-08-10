package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (s msgServer) SendClose(ctx context.Context, msg *types.MsgSendClose) (*types.MsgSendCloseResponse, error) {
	if err := validator.ValidateMsgSendClose(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account, ok := s.GetAccount(cctx, msg.GetSender())
	if !ok {
		return nil, status.Error(codes.Unauthenticated, "")
	}

	if err := core.Close(account.GetId(), msg.GetOrderId()); err != nil {
		return nil, err
	}

	s.SetAccount(cctx, account)

	return &types.MsgSendCloseResponse{}, nil
}
