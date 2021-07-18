package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendWithdraw(msg *types.MsgSendWithdraw) error {
	if msg == nil {
		return ValidationErr
	}

	coin := msg.GetCoin()
	if coin == nil {
		return ValidationErr
	}
	if !coin.IsValid() || coin.IsZero() {
		return ValidationErr
	}

	return nil
}
