package core

import (
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

func NewAccount(sender string) types.Account {
	resp := storage.CallSaiStorage("save", storage.Request{
		Collection: "Accounts",
		Data: types.Account{
			Id:      sender,
			Balance: map[string]float64{},
		},
	})
	_ = resp

	return types.Account{
		Id:      sender,
		Balance: make(map[string]float64),
	}
}
