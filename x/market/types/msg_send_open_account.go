package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgSendOpenAccount{}

func NewMsgSendOpenAccount(
	sender, port, channelId string,
	timeoutTimestamp uint64,
) *MsgSendOpenAccount {
	return &MsgSendOpenAccount{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
	}
}

func (m *MsgSendOpenAccount) Route() string {
	return RouterKey
}

func (m *MsgSendOpenAccount) Type() string {
	return "OpenAccount"
}

func (m *MsgSendOpenAccount) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(m.GetSender())
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (m *MsgSendOpenAccount) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(m)
	return sdk.MustSortJSON(bz)
}

func (m *MsgSendOpenAccount) ValidateBasic() error {
	if _, err := sdk.AccAddressFromBech32(m.GetSender()); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}
