package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendDeposit(msg *types.MsgSendDeposit) error {
	if msg == nil {
		return ValidationErr
	}

	// validate "coin"
	coin := msg.GetCoin()
	if coin == nil {
		return ValidationErr
	}
	if !coin.IsValid() || coin.IsZero() {
		return ValidationErr
	}

	return nil
}
