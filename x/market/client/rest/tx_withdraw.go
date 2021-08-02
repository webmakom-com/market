package rest

import (
	"net/http"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/rest"
	"github.com/onomyprotocol/market/x/market/types"
	"github.com/onomyprotocol/market/x/market/validator"
)

type withdrawRequest struct {
	BaseReq          rest.BaseReq `json:"base_req"`
	Sender           string       `json:"sender"`
	Port             string       `json:"port"`
	ChannelId        string       `json:"channel_id"`
	TimeoutTimestamp uint64       `json:"timeout_timestamp"`
	Coin             *sdk.Coin    `json:"coin"`
}

func withdrawHandler(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req withdrawRequest
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			rest.WriteErrorResponse(w, http.StatusBadRequest, "failed to parse request")
			return
		}

		if baseReq := req.BaseReq.Sanitize(); !baseReq.ValidateBasic(w) {
			return
		}

		if _, err := sdk.AccAddressFromBech32(req.Sender); err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		msg := types.NewMsgSendWithdraw(
			req.Sender,
			req.Port,
			req.ChannelId,
			req.TimeoutTimestamp,
			req.Coin,
		)
		if err := validator.ValidateMsgSendWithdraw(msg); err != nil {
			rest.WriteErrorResponse(w, http.StatusBadRequest, err.Error())
			return
		}

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}
