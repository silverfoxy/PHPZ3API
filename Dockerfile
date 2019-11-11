FROM ubuntu:latest

ARG DEBIAN_FRONTEND=noninteractive

RUN apt update
RUN apt install curl unzip git software-properties-common -y
RUN add-apt-repository ppa:ondrej/php
RUN apt update
RUN apt install php7.4 php7.4-mbstring php7.4-ffi -y
RUN curl -L -O https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip
RUN unzip z3-4.8.6-x64-ubuntu-16.04.zip
#WORKDIR z3-4.8.6-x64-ubuntu-16.04

