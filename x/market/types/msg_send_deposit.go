package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgSendDeposit{}

func NewMsgSendDeposit(
	sender, port, channelId string,
	timeoutTimestamp uint64,
	coin *sdk.Coin,
) *MsgSendDeposit {
	return &MsgSendDeposit{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		Coin:             coin,
	}
}

func (m *MsgSendDeposit) Route() string {
	return RouterKey
}

func (m *MsgSendDeposit) Type() string {
	return "Open"
}

func (m *MsgSendDeposit) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(m.GetSender())
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (m *MsgSendDeposit) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(m)
	return sdk.MustSortJSON(bz)
}

func (m *MsgSendDeposit) ValidateBasic() error {
	if _, err := sdk.AccAddressFromBech32(m.GetSender()); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}
