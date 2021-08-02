package rest

import (
	"github.com/gorilla/mux"

	"github.com/cosmos/cosmos-sdk/client"
	// this line is used by starport scaffolding # 1
)

const (
	MethodGet  = "GET"
	MethodPost = "POST"
)

// RegisterRoutes registers market-related REST handlers to a router
func RegisterRoutes(clientCtx client.Context, r *mux.Router) {
	// this line is used by starport scaffolding # 2
	registerTxHandlers(clientCtx, r)
}

func registerQueryRoutes(clientCtx client.Context, r *mux.Router) {
	// this line is used by starport scaffolding # 3
}

func registerTxHandlers(clientCtx client.Context, r *mux.Router) {
	// this line is used by starport scaffolding # 4
	r.HandleFunc("/market/deposit", depositHandler(clientCtx)).Methods(MethodPost)
	r.HandleFunc("/market/withdraw", withdrawHandler(clientCtx)).Methods(MethodPost)
	r.HandleFunc("/market/open", openHandler(clientCtx)).Methods(MethodPost)
	r.HandleFunc("/market/close", closeHandler(clientCtx)).Methods(MethodPost)
}
