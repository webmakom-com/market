FROM ubuntu:18.04

WORKDIR /srv

COPY ./ /srv/
RUN apt-get update && apt-get install -y locales curl && locale-gen ${OS_LOCALE}
RUN dpkg-reconfigure locales && apt-get install -y sudo gnupg \
 && apt-get install -y --reinstall ca-certificates \
 && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 9DA31620334BD75D9DCB49F368818C72E52529D4 \
 && echo "deb [ arch=amd64 ] https://repo.mongodb.org/apt/ubuntu bionic/mongodb-org/4.0 multiverse" | sudo tee /etc/apt/sources.list.d/mongodb-org-4.0.list \
 && apt-get update && apt-get install -y mongodb-org \
 && apt-get purge -y --auto-remove gnupg \
 && rm -rf /var/lib/apt/lists/*

VOLUME ["/data/db"]

#CMD ["mongod", "/etc/mongodb.conf"]

#CMD ./installmongo.sh
#CMD ["service mongod start"]
CMD ./sai_storage

EXPOSE 27017
EXPOSE 8818
