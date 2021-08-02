package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendClose(msg *types.MsgSendClose) error {
	if msg == nil {
		return ValidationErr
	}

	// validate "ask_coin"
	askCoin := msg.GetAskCoin()
	if askCoin == "" {
		return ValidationErr
	}

	// validate "bid_coin"
	bidCoin := msg.GetBidCoin()
	if bidCoin == "" {
		return ValidationErr
	}

	// validate "order_type"
	if msg.GetOrderType() == types.OrderType_ORDER_TYPE_UNSPECIFIED {
		return ValidationErr
	}

	// validate "index"
	if msg.GetIndex() < 0 {
		return ValidationErr
	}

	return nil
}
