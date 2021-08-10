package core

import (
	"github.com/gogo/protobuf/jsonpb"
	"github.com/onomyprotocol/market/storage"
	"github.com/onomyprotocol/market/x/market/types"
)

// Close — TODO:
func Close(accountId, orderId string) (*types.Order, error) {
	// Get order by order ID
	// TODO: set request
	resp := storage.CallSaiStorage("get", storage.Request{})

	// TODO: parse resp

	var order types.Order
	if err := jsonpb.UnmarshalString(resp, &order); err != nil {
		return nil, err
	}

	order.Status = types.OrderStatus_ORDER_TYPE_CLOSE

	doc, err := new(jsonpb.Marshaler).MarshalToString(&order)
	if err != nil {
		return nil, err
	}
	_ = doc

	// TODO: set request
	resp = storage.CallSaiStorage("save", storage.Request{})
	_ = resp

	return &order, nil
}
