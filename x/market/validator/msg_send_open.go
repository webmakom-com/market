package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendOpen(msg *types.MsgSendOpen) error {
	if msg == nil {
		return ValidationErr
	}

	// validate "ask_coin_denom"
	if len(msg.GetAskCoinDenom()) == 0 {
		return ValidationErr
	}

	// validate "bid_coin_denom"
	if len(msg.GetBidCoinDenom()) == 0 {
		return ValidationErr
	}

	// validate "order_type"
	if msg.GetOrderType() == types.OrderType_ORDER_TYPE_UNSPECIFIED {
		return ValidationErr
	}

	// validate "order"
	order := msg.GetOrder()
	if order == nil {
		return ValidationErr
	}

	// validate "order.amount"
	amount := order.GetAmount()
	if !amount.IsValid() || amount.IsZero() {
		return ValidationErr
	}

	// validate "order.exchange_rate"
	exchangeRate := order.GetExchangeRate().Dec
	if exchangeRate.IsNil() || exchangeRate.IsNegative() {
		return ValidationErr
	}

	return nil
}
