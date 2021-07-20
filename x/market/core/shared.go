package core

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

var (
	ErrBalanceNotFound        = errors.New("balance.not_found")
	ErrWithdrawNotEnoughFunds = errors.New("withdraw.not_enough_funds")

	ErrNotEnoughFunds       = errors.New("balance.not_enough_funds")
	ErrPositionNotFound     = errors.New("position.not_found")
	ErrOrderTypeUnspecified = errors.New("order_type.unspecified")
)

func NewExchangeAccount(sender string) types.ExchangeAccount {
	return types.ExchangeAccount{
		Id:       sender,
		Balances: make([]*types.Balance, 0),
	}
}

func getBalanceByCoin(balances []*types.Balance, coin *sdk.Coin) (*types.Balance, error) {
	for _, balance := range balances {
		if coin.GetDenom() == balance.GetCoin().GetDenom() {
			return balance, nil
		}
	}

	return nil, ErrBalanceNotFound
}

func getPositionByCoin(positions []*types.Position, coin *sdk.Coin) (*types.Position, error) {
	for _, position := range positions {
		if coin.GetDenom() == position.GetCoin().GetDenom() {
			return position, nil
		}
	}

	return nil, ErrPositionNotFound
}
