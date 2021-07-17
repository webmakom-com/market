package core

import (
	"errors"
	"log"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

// TestDeposit —
func TestDeposit(t *testing.T) {
	tables := []struct {
		account types.ExchangeAccount
		coin    sdk.Coin
		out     types.ExchangeAccount
	}{
		// Account don't have a balance with a specified coin
		{
			account: types.ExchangeAccount{
				Balances: make([]*types.Balance, 0),
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(1)),
			out: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(1),
						},
					},
				},
			},
		},
		// Account have a balance with a specified coin
		{
			account: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(1),
						},
					},
				},
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(1)),
			out: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(2),
						},
					},
				},
			},
		},
	}

	for i, table := range tables {
		if err := Deposit(&table.account, &table.coin); err != nil {
			log.Println(i)
			t.Fail()
		}

		if !table.account.GetBalances()[0].GetCoin().Amount.Equal(table.out.GetBalances()[0].GetCoin().Amount) {
			log.Println(i)
			t.Fail()
		}
	}
}

// TestWithdraw —
func TestWithdraw(t *testing.T) {
	tables := []struct {
		account types.ExchangeAccount
		coin    sdk.Coin
		out     types.ExchangeAccount
		err     error
	}{
		// Account don't have a balance with a specified coin
		{
			account: types.ExchangeAccount{
				Balances: make([]*types.Balance, 0),
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(1)),
			out:  types.ExchangeAccount{},
			err:  ErrBalanceNotFound,
		},
		// Account have a balance with a specified coin which amount is less than the coin amount
		{
			account: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(1),
						},
					},
				},
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(2)),
			out:  types.ExchangeAccount{},
			err:  ErrWithdrawNotEnoughFunds,
		},
		// Account have a balance with a specified coin which amount is equals to the coin amount
		{
			account: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(1),
						},
					},
				},
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(1)),
			out: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(0),
						},
					},
				},
			},
			err: nil,
		},
		// Account have a balance with a specified coin which amount is more than the coin amount
		{
			account: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(2),
						},
					},
				},
			},
			coin: sdk.NewCoin("onomomy/1", sdk.NewInt(1)),
			out: types.ExchangeAccount{
				Balances: []*types.Balance{
					{
						Coin: &sdk.Coin{
							Denom:  "onomomy/1",
							Amount: sdk.NewInt(1),
						},
					},
				},
			},
			err: nil,
		},
	}

	for i, table := range tables {
		if err := Withdraw(&table.account, &table.coin); err != nil {
			if !errors.Is(err, table.err) {
				log.Println(i)
				t.Fail()
			}

			continue
		}

		if !table.account.GetBalances()[0].GetCoin().Amount.Equal(table.out.GetBalances()[0].GetCoin().Amount) {
			log.Println(i)
			t.Fail()
		}
	}
}
