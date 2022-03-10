# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.224.2/containers/debian/.devcontainer/base.Dockerfile

# [Choice] Debian version (use bullseye on local arm64/Apple Silicon): bullseye, buster
ARG VARIANT="buster"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

# ** [Optional] Uncomment this section to install additional packages. **
ARG OPAM_VERSION="2.1.2"
ARG OPAM_ARCH="x86_64"
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends build-essential wget openjdk-11-jre-headless libgmp-dev \
    && wget -O /usr/local/bin/opam https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/opam-${OPAM_VERSION}-${OPAM_ARCH}-linux \
    && chmod +x /usr/local/bin/opam


USER vscode

ARG COQ_VERSION="8.15.0"
RUN opam init -y -a --disable-sandboxing \
    && eval $(opam env --switch=default) \
    && opam pin -y add coq ${COQ_VERSION}