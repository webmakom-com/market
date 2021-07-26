package core

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/onomyprotocol/market/x/market/types"
)

func SubmitPosition(
	account *types.ExchangeAccount,
	askCoin, bidCoin *sdk.Coin,
	orderType types.OrderType,
	order *types.Order,
) error {
	balance, err := getBalanceByCoin(account.GetBalances(), bidCoin)
	if err != nil {
		return err
	}

	// We can't place order, because there are not enough funds in the account
	if balance.GetCoin().Amount.ToDec().Sub(order.GetAmount().Amount).LT(sdk.ZeroDec()) {
		return ErrNotEnoughFunds
	}

	pos, err := getPositionByCoin(balance.GetPositions(), askCoin)
	if err != nil {
		return err
	}

	switch orderType {
	case types.OrderType_ORDER_TYPE_LIMIT:
		submitLimitOrder(pos, order)
	case types.OrderType_ORDER_TYPE_STOP:
		submitStopOrder(pos, order)
	case types.OrderType_ORDER_TYPE_UNSPECIFIED:
		return ErrOrderTypeUnspecified
	default:
		return ErrOrderTypeUnspecified
	}

	balance.GetCoin().Amount = balance.GetCoin().Amount.Sub(sdk.NewIntFromBigInt(order.GetAmount().Amount.BigInt()))

	return nil
}

func submitLimitOrder(position *types.Position, order *types.Order) {
	limitOrders := position.GetLimitOrders()
	if len(limitOrders) == 0 {
		position.LimitOrders = []*types.Order{order}
	}

	for i, limitOrder := range limitOrders {
		if limitOrder.GetExchangeRate().Dec.GT(order.GetExchangeRate().Dec) {
			limitOrders = append(limitOrders[:i+1], limitOrders[i:]...)
			limitOrders[i] = order

			break
		}
	}
}

func submitStopOrder(position *types.Position, order *types.Order) {
	stopOrders := position.GetStopOrders()
	if len(stopOrders) == 0 {
		position.StopOrders = []*types.Order{order}
	}

	for i, stopOrder := range stopOrders {
		if stopOrder.GetExchangeRate().Dec.LT(order.GetExchangeRate().Dec) {
			stopOrders = append(stopOrders[:i+1], stopOrders[i:]...)
			stopOrders[i] = order

			break
		}
	}
}
