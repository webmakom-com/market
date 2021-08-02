package core

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

// Withdraw —
func Withdraw(account *types.ExchangeAccount, coin *sdk.Coin) error {
	balance, err := getBalanceByCoinDenom(account.GetBalances(), coin.GetDenom())
	if err != nil {
		return err
	}

	if coin.Amount.GT(balance.GetCoin().Amount) {
		return ErrWithdrawNotEnoughFunds
	}

	balance.GetCoin().Amount = balance.GetCoin().Amount.Sub(coin.Amount)

	return nil
}
