#!/usr/bin/env bash

set -euo pipefail

: "${MSYSROOT:?MSYSROOT is required}"

exec qemu-aarch64 -L "${MSYSROOT}" "$@"
