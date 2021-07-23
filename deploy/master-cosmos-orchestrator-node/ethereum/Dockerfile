FROM leeway321/gravity-bridge-binary:0.0.1 as builder

EXPOSE 8545 30303
ARG PUBLIC_IP=${PUBLIC_IP}
ARG GIT_HUB_USER=${GIT_HUB_USER}
ARG GIT_HUB_PASS=${GIT_HUB_PASS}
ARG GIT_HUB_EMAIL=${GIT_HUB_EMAIL}
ARG GIT_HUB_BRANCH=${GIT_HUB_BRANCH}
ARG GIT_HUB_REPO=${GIT_HUB_REPO}

# purpose of clone the repo is to get updated Ethgenesis.json file
# //TODO this clone may be change in future
RUN git clone -b $GIT_HUB_BRANCH $GIT_HUB_REPO
RUN cp -r /root/market/deploy/master-cosmos-orchestrator-node/scripts scripts
RUN cp -r /root/market/master/assets assets
#RUN cp -r /root/market/master/testchain testchain


RUN chmod -R +x /root/scripts
RUN chmod -R +x /root/assets
#RUN chmod -R +x /root/testchain

CMD ["sh", "scripts/ethereum-run.sh"]