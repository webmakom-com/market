package core

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

var (
	ErrBalanceNotFound        = errors.New("balance.not_found")
	ErrWithdrawNotEnoughFunds = errors.New("withdraw.not_enough_funds")
)

func NewExchangeAccount(sender string) types.ExchangeAccount {
	return types.ExchangeAccount{
		Id:       sender,
		Balances: make([]*types.Balance, 0),
	}
}

// Deposit —
func Deposit(account *types.ExchangeAccount, coin *sdk.Coin) error {
	balance, err := getBalanceByCoin(account.GetBalances(), coin)
	if errors.Is(err, ErrBalanceNotFound) {
		account.Balances = append(account.GetBalances(), &types.Balance{
			Coin:      coin,
			Positions: make([]*types.Position, 0),
		})

		return nil
	}
	if err != nil {
		return err
	}

	balance.GetCoin().Amount = balance.GetCoin().Amount.Add(coin.Amount)

	return nil
}

// Withdraw —
func Withdraw(account *types.ExchangeAccount, coin *sdk.Coin) error {
	balance, err := getBalanceByCoin(account.GetBalances(), coin)
	if err != nil {
		return err
	}

	if coin.Amount.GT(balance.GetCoin().Amount) {
		return ErrWithdrawNotEnoughFunds
	}

	balance.GetCoin().Amount = balance.GetCoin().Amount.Sub(coin.Amount)

	return nil
}

func getBalanceByCoin(balances []*types.Balance, coin *sdk.Coin) (*types.Balance, error) {
	for _, balance := range balances {
		if coin.GetDenom() == balance.GetCoin().GetDenom() {
			return balance, nil
		}
	}

	return nil, ErrBalanceNotFound
}
