package core

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func NewAccount(sender string) types.Account {
	return types.Account{
		Id:      sender,
		Balance: make(map[string]float64),
	}
}
