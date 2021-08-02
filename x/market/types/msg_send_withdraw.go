package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgSendWithdraw{}

func NewMsgSendWithdraw(
	sender, port, channelId string,
	timeoutTimestamp uint64,
	coin *sdk.Coin,
) *MsgSendWithdraw {
	return &MsgSendWithdraw{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		Coin:             coin,
	}
}

func (m *MsgSendWithdraw) Route() string {
	return RouterKey
}

func (m *MsgSendWithdraw) Type() string {
	return "Open"
}

func (m *MsgSendWithdraw) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(m.GetSender())
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (m *MsgSendWithdraw) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(m)
	return sdk.MustSortJSON(bz)
}

func (m *MsgSendWithdraw) ValidateBasic() error {
	if _, err := sdk.AccAddressFromBech32(m.GetSender()); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}
