

# syntax=docker/dockerfile:1

FROM coqorg/coq:8.18.0
RUN sudo apt update
RUN sudo apt upgrade --yes
RUN sudo apt install python3-seaborn --yes
COPY . .
#USER root
#RUN chown coq:coq /_build
#USER coq
