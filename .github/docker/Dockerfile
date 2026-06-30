FROM alpine:3.24

ARG TARGETPLATFORM

RUN apk add --no-cache \
        autoconf \
        automake \
        bash \
        bc \
        bison \
        build-base \
        coreutils \
        curl \
        dejagnu \
        diffutils \
        expect \
        file \
        findutils \
        flex \
        gawk \
        git \
        libstdc++-dev \
        libtool \
        linux-headers \
        m4 \
        musl-dev \
        patch \
        perl \
        pkgconf \
        python3 \
        rsync \
        tar \
        tcl \
        texinfo \
        xz \
        zlib-dev \
        zlib-static \
        zstd-dev \
        zstd-static \
    && if [ "$(uname -m)" != "aarch64" ]; then apk add --no-cache qemu-aarch64; fi
