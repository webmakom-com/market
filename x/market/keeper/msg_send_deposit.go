package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/core"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
)

func (s msgServer) SendDeposit(ctx context.Context, msg *types.MsgSendDeposit) (*types.MsgSendDepositResponse, error) {
	if err := validator.ValidateMsgSendDeposit(msg); err != nil {
		return nil, err
	}

	cctx := sdk.UnwrapSDKContext(ctx)

	account := s.GetOrCreateExchangeAccount(cctx, msg.GetSender())

	if err := core.Deposit(&account, msg.GetCoin()); err != nil {
		return nil, err
	}

	s.SetExchangeAccount(cctx, account)

	return &types.MsgSendDepositResponse{}, nil
}
