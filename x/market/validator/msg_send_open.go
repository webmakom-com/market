package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendOpen(msg *types.MsgSendOpen) error {
	if msg == nil {
		return ValidationErr
	}

	// validate "order"
	order := msg.GetOrder()
	if order == nil {
		return ValidationErr
	}

	// validate "order.account_id"
	if accountId := order.GetAccountId(); len(accountId) == 0 {
		return ValidationErr
	}

	// validate "order.bid_coin"
	if bidCoin := order.GetBidCoin(); len(bidCoin) == 0 {
		return ValidationErr
	}

	// validate "order.ask_coin"
	if askCoin := order.GetAskCoin(); len(askCoin) == 0 {
		return ValidationErr
	}

	// validate "order.amount"
	if amount := order.GetAmount(); !(amount > 0) {
		return ValidationErr
	}

	// validate "order.exchange_rate"
	if exchangeRate := order.GetExchangeRate(); !(exchangeRate > 0) {
		return ValidationErr
	}

	// validate "order.created" // TODO: improve validation
	if created := order.GetCreated(); created.IsZero() {
		return ValidationErr
	}

	return nil
}
