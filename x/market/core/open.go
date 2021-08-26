package core

import (
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

// Open —
func Open(order *types.Order) error {
	// TODO: logic
	// TODO: set request
	resp := storage.CallSaiStorage("save", storage.Request{
		Collection: "Orders",
		Data:       order,
	})
	_ = resp

	return nil
}
