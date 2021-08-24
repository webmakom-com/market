package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/timestamppb"
)

func (s msgServer) SendOpen(ctx context.Context, msg *types.MsgSendOpen) (*types.MsgSendOpenResponse, error) {
	if err := validator.ValidateMsgSendOpen(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account, ok := s.GetAccount(cctx, msg.GetSender())
	if !ok {
		return nil, status.Error(codes.Unauthenticated, "")
	}

	order := msg.GetOrder()
	if account.GetInternalId() != order.GetAccountId() {
		return nil, status.Error(codes.PermissionDenied, "")
	}

	// TODO:
	if err := core.Open(msg.GetOrder()); err != nil {
		return nil, err
	}

	// TODO: exchange rate
	order.Status = types.OrderStatus_ORDER_TYPE_OPEN
	order.CrTime = timestamppb.Now().AsTime().Unix()

	s.SetOrder(cctx, *order)

	return &types.MsgSendOpenResponse{}, nil
}
