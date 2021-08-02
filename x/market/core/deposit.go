package core

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

// Deposit —
func Deposit(account *types.ExchangeAccount, coin *sdk.Coin) error {
	balance, err := getBalanceByCoinDenom(account.GetBalances(), coin.GetDenom())
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
