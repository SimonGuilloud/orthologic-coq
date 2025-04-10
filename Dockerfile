

# syntax=docker/dockerfile:1

FROM coqorg/coq:8.18.0
COPY . .
#USER root
#RUN chown coq:coq /_build
#USER coq
