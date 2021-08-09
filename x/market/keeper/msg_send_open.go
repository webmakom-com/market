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

func (s msgServer) SendOpen(ctx context.Context, msg *types.MsgSendOpen) (*types.MsgSendOpenResponse, error) {
	if err := validator.ValidateMsgSendOpen(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account := s.GetOrCreateAccount(cctx, msg.GetSender())
	if account.GetId() != msg.GetOrder().GetAccountId() {
		return nil, status.Error(codes.PermissionDenied, "")
	}

	if err := core.Open(msg.GetOrder()); err != nil {
		return nil, err
	}

	s.SetAccount(cctx, account)

	return &types.MsgSendOpenResponse{}, nil
}
