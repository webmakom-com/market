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

func (s msgServer) SendWithdraw(ctx context.Context, msg *types.MsgSendWithdraw) (*types.MsgSendWithdrawResponse, error) {
	if err := validator.ValidateMsgSendWithdraw(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account, ok := s.GetAccount(cctx, msg.GetSender())
	if !ok {
		return nil, status.Error(codes.Unauthenticated, "")
	}

	// TODO:
	if err := core.Withdraw(account.GetInternalId(), msg.GetCoin()); err != nil {
		return nil, err
	}

	s.SetAccount(cctx, account)

	return &types.MsgSendWithdrawResponse{}, nil
}
