GRAVITY_ASSETS="/root/assets"
BUCKET_MASTER="/root/market/master"

GRAVITY_HOME_FLAG="--home /root/testchain/gravity"
GRAVITY_GENESIS_FILE="/root/testchain/gravity/config"
GRAVITY_CONFIG_FILE="/root/testchain/gravity/config/config.toml"
BUCKET_MASTER_GENESIS_FILE="/root/mainNode/master/genesis.json"
BUCKET_MASTER_SEED_FILE="/root/mainNode/master/seed"
MAIN_NODE="/root/mainNode"

GIT_HUB_BRANCH=$1

echo "Get pull updates"
git clone -b $GIT_HUB_BRANCH https://github.com/sunnyk56/market.git $MAIN_NODE

echo "updating EthGenesis.json in the root assets directory"
rm -rf $GRAVITY_ASSETS
mkdir $GRAVITY_ASSETS
cp $BUCKET_MASTER/assets/. $GRAVITY_ASSETS

echo "Copying genesis file"
rm $GRAVITY_GENESIS_FILE/genesis.json
touch $GRAVITY_GENESIS_FILE/genesis.json
cp $BUCKET_MASTER_GENESIS_FILE $GRAVITY_GENESIS_FILE/genesis.json
peerseed=$(cat $BUCKET_MASTER_SEED_FILE)

sed -i 's#persistent_peers = ""#persistent_peers = "'$peerseed'"#g' $GRAVITY_CONFIG_FILE

rm -r $MAIN_NODE

# echo "Run the gravity start scripts"
# gravity $GRAVITY_HOME_FLAG start --pruning=nothing &>/dev/null

# Resets the blockchain database, removes address book files and start the node
gravity $GRAVITY_HOME_FLAG unsafe-reset-all
gravity $GRAVITY_HOME_FLAG --address tcp://0.0.0.0:26655 --rpc.laddr tcp://0.0.0.0:26657 --grpc.address 0.0.0.0:9090 --log_level error --p2p.laddr tcp://0.0.0.0:26656 --rpc.pprof_laddr 0.0.0.0:6060 start
# sh /root/scripts/cosmos-run.sh