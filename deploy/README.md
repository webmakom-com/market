# Gravity Bridge Binary
 Here the idea is instead of making binary again and again, we can create a docker image,  ```gravity-bridge-binary.yml``` will create a docker image ```leeway321/gravity-bridge-binary:0.0.1``` that will contain all the binaries, and whenever we need to launch either cosmos gravity node, ethereum node, or orchestrator node we can use this docker image.
# Master Cosmos Orchestrator Node
This holds the code to start a master validator node. For further information read this [file](https://github.com/sunnyk56/onomy/tree/ONET-49/deploy/master-cosmos-orchestrator-node#readme)

# Peer Cosmos Orchestrator Node
This holds the code to start a peer validator node that starts a gravity validator container and orchestrator container.

---
# Network-setup
- ```network-setup.yml``` this git action starts a test network in which there are two validators, two orchestrators, and one ethereum node.
- In this network the one validators and orchestrator containers set is running in one machine and another one in other machine.
- Ethereum node container is running independently.
- Steps which are taken into consideration to start the test net : 
### Start the validators
- Build and push image for the ```master-cosmos-validator-node``` and ```peer-cosmos-validator-node``` to the dockerhub.
- Now use these images to start ```master-validator-node``` and ```peer-validator-node``` in two different containers in two different machines.
- First, the validators are started individually and independently in which master cosmos node which will store genesis file, keys and all gravity data, and ```ETH_MINER_PUBLIC_KEY``` and ```eth_key``` in ```ETHGenesis.json``` file in a master directory on GitHub.
- peer cosmos node which will store ```gentx``` file, ```val_key``` in peerInfo directory and add ```eth_key``` in ```ETHGenesis.json``` file in a peerInfo directory on GitHub.
- then run the ```update-master-node.sh``` script which will be updating the genesis file and Ethgenesis.json file using peer info and finally update the genesis file on GitHub in the master directory and start the node.
- then run the ```update-peer-node.sh``` script which will be updating the genesis file and Ethgenesis.json using the master directory and start the node
- once these are started start the Ethereum node.

### Start Ethereum node
- Build and push image for ```cosmos-ethereum-node```.
- Start the ethereum container now.
- it needs ```ETHGenesis.json``` in the master directory having all ethkeys of validator added and ```ETH_MINER_PUBLIC_KEY```

### Deploy Contract
- Now you have to provide ```GRAVITY_HOST``` and ```ETH_HOST```.
- once the contract is deployed you will get ```CONTRACT_ADDRESS``` this will be automatically saved in GitHub master/eth_contract_address

### Start Orchestrators
- Now build and push image for ```cosmos-orchestartor-node```.
- start the orchestrator container for the respective validator now.
- You have to provide a validator mnemonic to start the orchestrator.
- It will use the ```eth_contract_address``` which you have saved in the last step as ```gravity-contract-address```.

