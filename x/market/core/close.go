package core

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

// Close —
func Close(
	account *types.ExchangeAccount,
	askCoinDenom, bidCoinDenom string,
	orderType types.OrderType,
	index int32,
) error {
	balance, err := getBalanceByCoinDenom(account.GetBalances(), bidCoinDenom)
	if err != nil {
		return err
	}

	pos, err := getPositionByCoinDenom(balance.GetPositions(), askCoinDenom)
	if err != nil {
		return err
	}

	var order *types.Order
	switch orderType {
	case types.OrderType_ORDER_TYPE_LIMIT:
		order, err = closeLimitOrder(pos, index)
		if err != nil {
			return err
		}
	case types.OrderType_ORDER_TYPE_STOP:
		order, err = closeStopOrder(pos, index)
		if err != nil {
			return err
		}
	case types.OrderType_ORDER_TYPE_UNSPECIFIED:
		return ErrOrderTypeUnspecified
	default:
		return ErrOrderTypeUnspecified
	}

	balance.GetCoin().Amount = balance.GetCoin().Amount.Add(sdk.NewIntFromBigInt(order.GetAmount().Amount.BigInt()))

	return nil
}

// closeLimitOrder —
func closeLimitOrder(position *types.Position, index int32) (*types.Order, error) {
	if index < 0 || index >= int32(len(position.LimitOrders)) {
		return nil, ErrInvalidIndex
	}

	order := position.LimitOrders[index]
	position.LimitOrders = append(position.LimitOrders[:index], position.LimitOrders[index+1:]...)

	return order, nil
}

// closeStopOrder —
func closeStopOrder(position *types.Position, index int32) (*types.Order, error) {
	if index < 0 || index >= int32(len(position.StopOrders)) {
		return nil, ErrInvalidIndex
	}

	order := position.StopOrders[index]
	position.StopOrders = append(position.StopOrders[:index], position.StopOrders[index+1:]...)

	return order, nil
}
