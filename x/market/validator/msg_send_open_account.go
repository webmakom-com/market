package validator

import (
	"github.com/onomyprotocol/market/x/market/types"
)

func ValidateMsgSendOpenAccount(msg *types.MsgSendOpenAccount) error {
	if msg == nil {
		return ValidationErr
	}

	return nil
}
