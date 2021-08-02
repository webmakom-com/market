package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgSendOpen{}

func NewMsgSendOpen(
	sender, port, channelId string,
	timeoutTimestamp uint64,
	askCoinDenom, bidCoinDenom string,
	orderType OrderType,
	order *Order,
) *MsgSendOpen {
	return &MsgSendOpen{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		AskCoinDenom:     askCoinDenom,
		BidCoinDenom:     bidCoinDenom,
		OrderType:        orderType,
		Order:            order,
	}
}

func (m *MsgSendOpen) Route() string {
	return RouterKey
}

func (m *MsgSendOpen) Type() string {
	return "Open"
}

func (m *MsgSendOpen) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(m.GetSender())
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (m *MsgSendOpen) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(m)
	return sdk.MustSortJSON(bz)
}

func (m *MsgSendOpen) ValidateBasic() error {
	if _, err := sdk.AccAddressFromBech32(m.GetSender()); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}
