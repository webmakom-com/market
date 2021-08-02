package core

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
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

func getBalanceByCoin(balances []*types.Balance, coin *sdk.Coin) (*types.Balance, error) {
	for _, balance := range balances {
		if coin.GetDenom() == balance.GetCoin().GetDenom() {
			return balance, nil
		}
	}

	return nil, ErrBalanceNotFound
}

func getBalanceByDenom(balances []*types.Balance, denom string) (*types.Balance, error) {
	for _, balance := range balances {
		if denom == balance.GetCoin().GetDenom() {
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

func getPositionByDenom(positions []*types.Position, denom string) (*types.Position, error) {
	for _, position := range positions {
		if denom == position.GetCoin().GetDenom() {
			return position, nil
		}
	}

	return nil, ErrPositionNotFound
}
