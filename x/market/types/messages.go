package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgSendOpen{}

func NewMsgSendOpen(sender string, port string, channelId string, timeoutTimestamp uint64, askCoin string, bidCoin string, orderType OrderType, order *Order) *MsgSendOpen {
	return &MsgSendOpen{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		AskCoin:          askCoin,
		BidCoin:          bidCoin,
		OrderType:        orderType,
		Order:            order,
	}
}

func (msg *MsgSendOpen) Route() string {
	return RouterKey
}

func (msg *MsgSendOpen) Type() string {
	return "Open"
}

func (msg *MsgSendOpen) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (msg *MsgSendOpen) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(msg)
	return sdk.MustSortJSON(bz)
}

func (msg *MsgSendOpen) ValidateBasic() error {
	_, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}

var _ sdk.Msg = &MsgSendClose{}

func NewMsgSendClose(sender string, port string, channelId string, timeoutTimestamp uint64, askCoin string, bidCoin string, orderType OrderType, index int32) *MsgSendClose {
	return &MsgSendClose{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		AskCoin:          askCoin,
		BidCoin:          bidCoin,
		OrderType:        orderType,
		Index:            index,
	}
}

func (msg *MsgSendClose) Route() string {
	return RouterKey
}

func (msg *MsgSendClose) Type() string {
	return "Open"
}

func (msg *MsgSendClose) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (msg *MsgSendClose) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(msg)
	return sdk.MustSortJSON(bz)
}

func (msg *MsgSendClose) ValidateBasic() error {
	_, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}

var _ sdk.Msg = &MsgSendDeposit{}

func NewMsgSendDeposit(sender string, port string, channelId string, timeoutTimestamp uint64, coin *sdk.Coin) *MsgSendDeposit {
	return &MsgSendDeposit{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		Coin:             coin,
	}
}

func (msg *MsgSendDeposit) Route() string {
	return RouterKey
}

func (msg *MsgSendDeposit) Type() string {
	return "Open"
}

func (msg *MsgSendDeposit) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (msg *MsgSendDeposit) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(msg)
	return sdk.MustSortJSON(bz)
}

func (msg *MsgSendDeposit) ValidateBasic() error {
	_, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}

var _ sdk.Msg = &MsgSendWithdraw{}

func NewMsgSendWithdraw(sender string, port string, channelId string, timeoutTimestamp uint64, coin *sdk.Coin) *MsgSendWithdraw {
	return &MsgSendWithdraw{
		Sender:           sender,
		Port:             port,
		ChannelId:        channelId,
		TimeoutTimestamp: timeoutTimestamp,
		Coin:             coin,
	}
}

func (msg *MsgSendWithdraw) Route() string {
	return RouterKey
}

func (msg *MsgSendWithdraw) Type() string {
	return "Open"
}

func (msg *MsgSendWithdraw) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (msg *MsgSendWithdraw) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(msg)
	return sdk.MustSortJSON(bz)
}

func (msg *MsgSendWithdraw) ValidateBasic() error {
	_, err := sdk.AccAddressFromBech32(msg.Sender)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	return nil
}
