package core

import (
	"errors"

	"github.com/onomyprotocol/market/x/market/types"
)

var (
	ErrInvalidIndex           = errors.New("common.invalid_index")
	ErrNotEnoughFunds         = errors.New("balance.not_enough_funds")
	ErrBalanceNotFound        = errors.New("balance.not_found")
	ErrOrderTypeUnspecified   = errors.New("order_type.unspecified")
	ErrPositionNotFound       = errors.New("position.not_found")
	ErrWithdrawNotEnoughFunds = errors.New("withdraw.not_enough_funds")
)

func NewExchangeAccount(sender string) types.ExchangeAccount {
	return types.ExchangeAccount{
		Id:       sender,
		Balances: make([]*types.Balance, 0),
	}
}

func getBalanceByCoinDenom(balances []*types.Balance, coinDenom string) (*types.Balance, error) {
	for _, balance := range balances {
		if coinDenom == balance.GetCoin().GetDenom() {
			return balance, nil
		}
	}

	return nil, ErrBalanceNotFound
}

func getPositionByCoinDenom(positions []*types.Position, coinDenom string) (*types.Position, error) {
	for _, position := range positions {
		if coinDenom == position.GetCoin().GetDenom() {
			return position, nil
		}
	}

	return nil, ErrPositionNotFound
}
