package core

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/gogo/protobuf/jsonpb"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

// Deposit —
func Deposit(accountId string, coin *sdk.Coin) error {
	// TODO: logic
	// Get order by order ID
	resp := storage.CallSaiStorage("get", storage.Request{
		Collection: "Accounts",
		SelectString: map[string]string{
			"Id": accountId,
		},
	})

	// TODO: parse resp

	var account types.Account
	if err := jsonpb.UnmarshalString(resp, &account); err != nil {
		return err
	}

	if account.Balance[coin.Denom] >= 0 {
		account.Balance[coin.Denom] += float64(coin.Amount.Int64())
	} else {
		account.Balance[coin.Denom] = float64(coin.Amount.Int64())
	}

	doc, err := new(jsonpb.Marshaler).MarshalToString(&account)
	if err != nil {
		return err
	}
	_ = doc

	// TODO: set request
	resp = storage.CallSaiStorage("update", storage.Request{
		Collection: "Orders",
		SelectString: map[string]string{
			"Id": accountId,
		},
		Data: account,
	})
	_ = resp

	return nil
}
