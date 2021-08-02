package rest

import (
	"net/http"
	"strconv"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/rest"
	"github.com/onomyprotocol/market/x/market/types"
)

type openRequest struct {
	BaseReq          rest.BaseReq `json:"base_req"`
	Sender           string       `json:"sender"`
	Port             string       `json:"port"`
	ChannelId        string       `json:"channel_id"`
	TimeoutTimestamp string       `json:"timeout_timestamp"`
	AskCoin          string       `json:"ask_coin"`
	BidCoin          string       `json:"bid_coin"`
	OrderType        string       `json:"order_type"`
	AccountId        string       `json:"account_id"`
	Amount           sdk.Coin     `json:"amount"`
	ExchangeRate     sdk.DecProto `json:"exchange_rate"`
}

func openHandler(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req openRequest
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			rest.WriteErrorResponse(w, http.StatusBadRequest, "failed to parse request")
			return
		}

		baseReq := req.BaseReq.Sanitize()
		if !baseReq.ValidateBasic(w) {
			return
		}

		_, err := sdk.AccAddressFromBech32(req.Sender)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedPort := req.Port

		parsedChannelId := req.ChannelId

		parsedTimeoutTimestamp, err := strconv.ParseUint(string(req.TimeoutTimestamp), 10, 64)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedAskCoin := req.AskCoin

		parsedBidCoin := req.BidCoin

		parsedOrderType, err := strconv.ParseInt(req.OrderType, 10, 32)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedAmount := sdk.NewDecCoinFromCoin(req.Amount)

		msg := types.NewMsgSendOpen(
			req.Sender,
			parsedPort,
			parsedChannelId,
			parsedTimeoutTimestamp,
			parsedAskCoin,
			parsedBidCoin,
			types.OrderType(parsedOrderType),
			&types.Order{
				AccountId:    req.AccountId,
				Amount:       &parsedAmount,
				ExchangeRate: &req.ExchangeRate,
			},
		)

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}

type closeRequest struct {
	BaseReq          rest.BaseReq `json:"base_req"`
	Sender           string       `json:"sender"`
	Port             string       `json:"port"`
	ChannelId        string       `json:"channel_id"`
	TimeoutTimestamp string       `json:"timeout_timestamp"`
	AskCoin          string       `json:"ask_coin"`
	BidCoin          string       `json:"bid_coin"`
	OrderType        string       `json:"order_type"`
	Index            string       `json:"index"`
}

func closeHandler(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req closeRequest
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			rest.WriteErrorResponse(w, http.StatusBadRequest, "failed to parse request")
			return
		}

		baseReq := req.BaseReq.Sanitize()
		if !baseReq.ValidateBasic(w) {
			return
		}

		_, err := sdk.AccAddressFromBech32(req.Sender)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedPort := req.Port

		parsedChannelId := req.ChannelId

		parsedTimeoutTimestamp, err := strconv.ParseUint(string(req.TimeoutTimestamp), 10, 64)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedAskCoin := req.AskCoin

		parsedBidCoin := req.BidCoin

		parsedOrderType, err := strconv.ParseInt(req.OrderType, 10, 32)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedIndex, err := strconv.ParseInt(req.Index, 10, 32)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		msg := types.NewMsgSendClose(
			req.Sender,
			parsedPort,
			parsedChannelId,
			parsedTimeoutTimestamp,
			parsedAskCoin,
			parsedBidCoin,
			types.OrderType(parsedOrderType),
			int32(parsedIndex),
		)

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}

type depositRequest struct {
	BaseReq          rest.BaseReq `json:"base_req"`
	Sender           string       `json:"sender"`
	Port             string       `json:"port"`
	ChannelId        string       `json:"channel_id"`
	TimeoutTimestamp string       `json:"timeout_timestamp"`
	Coin             sdk.Coin     `json:"coin"`
}

func depositHandler(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req depositRequest
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			rest.WriteErrorResponse(w, http.StatusBadRequest, "failed to parse request")
			return
		}

		baseReq := req.BaseReq.Sanitize()
		if !baseReq.ValidateBasic(w) {
			return
		}

		_, err := sdk.AccAddressFromBech32(req.Sender)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedPort := req.Port

		parsedChannelId := req.ChannelId

		parsedTimeoutTimestamp, err := strconv.ParseUint(string(req.TimeoutTimestamp), 10, 64)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		msg := types.NewMsgSendDeposit(
			req.Sender,
			parsedPort,
			parsedChannelId,
			parsedTimeoutTimestamp,
			&req.Coin,
		)

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}

type withdrawRequest struct {
	BaseReq          rest.BaseReq `json:"base_req"`
	Sender           string       `json:"sender"`
	Port             string       `json:"port"`
	ChannelId        string       `json:"channel_id"`
	TimeoutTimestamp string       `json:"timeout_timestamp"`
	Coin             sdk.Coin     `json:"coin"`
}

func withdrawHandler(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req withdrawRequest
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			rest.WriteErrorResponse(w, http.StatusBadRequest, "failed to parse request")
			return
		}

		baseReq := req.BaseReq.Sanitize()
		if !baseReq.ValidateBasic(w) {
			return
		}

		_, err := sdk.AccAddressFromBech32(req.Sender)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		parsedPort := req.Port

		parsedChannelId := req.ChannelId

		parsedTimeoutTimestamp, err := strconv.ParseUint(string(req.TimeoutTimestamp), 10, 64)
		if err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		msg := types.NewMsgSendWithdraw(
			req.Sender,
			parsedPort,
			parsedChannelId,
			parsedTimeoutTimestamp,
			&req.Coin,
		)

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}
