package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendClose(msg *types.MsgSendClose) error {
	if msg == nil {
		return ValidationErr
	}

	// validate "order_id"
	if len(msg.GetOrderId()) == 0 {
		return ValidationErr
	}

	return nil
}
