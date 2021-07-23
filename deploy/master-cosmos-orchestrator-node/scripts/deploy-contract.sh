#!/bin/bash
set -eu

echo "running ethereum node"

# Initial dir
CURRENT_WORKING_DIR="/root"
# Name of the network to bootstrap
CHAINID="testchain"
# Name of the gravity artifact
GRAVITY=gravity
# The name of the gravity node
GRAVITY_NODE_NAME="gravity"
# The address to run gravity node
# GRAVITY_HOST="143.244.147.226"
GIT_HUB_USER=$1
GIT_HUB_PASS=$2
GIT_HUB_EMAIL=$3
GIT_HUB_BRANCH=$4
GRAVITY_HOST=$5
ETH_HOST=$6
# Home folder for gravity config
GRAVITY_HOME="$CURRENT_WORKING_DIR/$CHAINID/$GRAVITY_NODE_NAME"
# Home flag for home folder
GRAVITY_HOME_FLAG="--home $GRAVITY_HOME"
# Prefix of cosmos addresses
GRAVITY_ADDRESS_PREFIX=cosmos
# Gravity chain demons
STAKE_DENOM="stake"

#ETH_MINER_PRIVATE_KEY="0xb1bab011e03a9862664706fc3bbaa1b16651528e5f0e7fbfcbfdd8be302a13e7"
#ETH_MINER_PUBLIC_KEY="0xBf660843528035a5A4921534E156a27e64B231fE"
ETH_MINER_PRIVATE_KEY="0xb1bab011e03a9862664706fc3bbaa1b16651528e5f0e7fbfcbfdd8be302a13e7"
ETH_MINER_PUBLIC_KEY="0xBf660843528035a5A4921534E156a27e64B231fE"
# The host of ethereum node
# ETH_HOST="143.244.147.226"



echo "copy the all test mode contract"
cp -r /go/src/github.com/onomyprotocol/gravity-bridge/. /gravity

echo "Applying contracts"
GRAVITY_DIR=/go/src/github.com/onomyprotocol/gravity-bridge/
cd $GRAVITY_DIR/solidity
# echo "running contract-deployer.ts: GRAVITY_HOST: $GRAVITY_HOST ETH_HOST: $ETH_HOST  6 : '$6'"
echo ts-node \
    contract-deployer.ts \
    --cosmos-node="http://$GRAVITY_HOST:26657" \
    --eth-node="http://$ETH_HOST:8545" \
    --eth-privkey="$ETH_MINER_PRIVATE_KEY" \
    --contract=artifacts/contracts/Gravity.sol/Gravity.json \
    --test-mode=true

npx ts-node \
    contract-deployer.ts \
    --cosmos-node="http://$GRAVITY_HOST:26657" \
    --eth-node="http://$ETH_HOST:8545" \
    --eth-privkey="$ETH_MINER_PRIVATE_KEY" \
    --contract=artifacts/contracts/Gravity.sol/Gravity.json \
    --test-mode=true >> /root/contracts
#    --test-mode=false | grep "Gravity deployed at Address" | grep -Eow '0x[0-9a-fA-F]{40}' >> /root/eth_contract_address

echo "extract gravity contract address"
grep "Gravity deployed at Address" /root/contracts | grep -Eow '0x[0-9a-fA-F]{40}' >> /root/eth_contract_address
CONTRACT_ADDRESS=$(cat /root/eth_contract_address)
echo "Contract address: $CONTRACT_ADDRESS"

###----------------------------- commit save Contract address-----
cd /root/onomy/
#sh deploy/master-cosmos-orchestrator-node/scripts/store-ethereum-contract-info.sh $GIT_HUB_USER $GIT_HUB_PASS $GIT_HUB_EMAIL $GIT_HUB_BRANCH
# # return back to home
# cd $CURRENT_WORKING_DIR
# echo "going to store contract address on github"
# sh deploy/master-cosmos-orchestrator-node/scripts/store-ethereum-contract-info.sh $GIT_HUB_USER $GIT_HUB_PASS $GIT_HUB_EMAIL $GIT_HUB_BRANCH
# #sleep 10
GRAVITY_CHAIN_DATA="/root/eth_contract_address"
GRAVITY_CHAIN_CONTRACT="/root/contracts"
BUCKET_MASTER_CHAIN_DATA="/root/onomy/master/eth_contract_address"
BUCKET_MASTER_CHAIN_CONTRACT="/root/onomy/master/contracts"

echo "Get pull updates"
git pull origin $GIT_HUB_BRANCH

echo "add master contract information file"
rm -rf $BUCKET_MASTER_CHAIN_DATA
rm -rf $BUCKET_MASTER_CHAIN_CONTRACT
touch $BUCKET_MASTER_CHAIN_DATA
touch $BUCKET_MASTER_CHAIN_CONTRACT
echo "Copying contract file"
cp $GRAVITY_CHAIN_DATA $BUCKET_MASTER_CHAIN_DATA
cp $GRAVITY_CHAIN_CONTRACT $BUCKET_MASTER_CHAIN_CONTRACT
echo "git add command"
git add master
echo "git add git config command"
git config --global user.email $GIT_HUB_EMAIL
git config --global user.name $GIT_HUB_USER
# //TODO this repo name should be pass as parameter
git remote set-url origin https://$GIT_HUB_USER:$GIT_HUB_PASS@github.com/sunnyk56/market.git

echo "git commit command"
git commit -m "add smart contract address in master directory file"

echo "git fetch command"
git fetch
echo "git push command"
git push origin $GIT_HUB_BRANCH
