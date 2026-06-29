#!/usr/bin/env bash

set -euo pipefail

MODE="${1:?build mode is required}"
MODE_ENV_VARS=()
BUILD_JOBS="${BUILD_JOBS:-$(nproc --all)}"

require_env() {
    local name

    for name in "$@"; do
        if [[ -z "${!name:-}" ]]; then
            echo "${name} is required" >&2
            exit 1
        fi
    done
}

case "${MODE}" in
    headers)
        if (($# != 4)); then
            echo "Usage: $0 headers <linux|musl> <repository> <commit-id>" >&2
            exit 1
        fi
        case "$2" in
            linux | musl)
                ;;
            *)
                echo "Unsupported header source: $2" >&2
                exit 1
                ;;
        esac
        if [[ -z "$3" ]]; then
            echo "Header repository is required" >&2
            exit 1
        fi
        if [[ ! "$4" =~ ^[0-9a-f]{40}$ ]]; then
            echo "Invalid header commit id: $4" >&2
            exit 1
        fi
        ;;
    gmp-build | gmp-check)
        MODE_ENV_VARS=(GMP_REPOSITORY GMP_COMMIT_ID)
        ;;
    isl-build | isl-check)
        MODE_ENV_VARS=(ISL_REPOSITORY ISL_COMMIT_ID)
        ;;
    mpfr-build | mpfr-check)
        MODE_ENV_VARS=(MPFR_REPOSITORY MPFR_COMMIT_ID)
        ;;
    mpc-build | mpc-check)
        MODE_ENV_VARS=(MPC_REPOSITORY MPC_COMMIT_ID)
        ;;
    toolchain-build | toolchain-verify)
        ;;
    *)
        echo "Unsupported build mode: ${MODE}" >&2
        exit 1
        ;;
esac

if [[ "${MODE}" != "headers" ]] && (($# != 1)); then
    echo "Usage: $0 ${MODE}" >&2
    exit 1
fi
if [[ ! "${BUILD_JOBS}" =~ ^[1-9][0-9]*$ ]]; then
    echo "BUILD_JOBS must be a positive integer: ${BUILD_JOBS}" >&2
    exit 1
fi

require_env \
    BUILD_CONTAINER_NAME \
    GITHUB_WORKSPACE \
    SOURCE_DIR \
    OUTPUT_DIR \
    BUILD_DIR \
    LOG_DIR \
    MPREFIX \
    MSYSROOT \
    "${MODE_ENV_VARS[@]}"

mkdir -p "${LOG_DIR}"

if ! docker container inspect "${BUILD_CONTAINER_NAME}" >/dev/null 2>&1; then
    echo "Build container is not running: ${BUILD_CONTAINER_NAME}" >&2
    exit 1
fi

DOCKER_ARGS=(
    exec
    --env "BUILD_JOBS=${BUILD_JOBS}"
    --env "HOST_UID=$(id -u)"
    --env "HOST_GID=$(id -g)"
    --env "GITHUB_WORKSPACE=${GITHUB_WORKSPACE}"
    --env "SOURCE_DIR=${SOURCE_DIR}"
    --env "OUTPUT_DIR=${OUTPUT_DIR}"
    --env "BUILD_DIR=${BUILD_DIR}"
    --env "LOG_DIR=${LOG_DIR}"
    --env "MPREFIX=${MPREFIX}"
    --env "MSYSROOT=${MSYSROOT}"
    --env "ALPINE_ARM64_IMAGE=${ALPINE_ARM64_IMAGE:-}"
)
for name in "${MODE_ENV_VARS[@]}"; do
    DOCKER_ARGS+=(--env "${name}=${!name}")
done

set +e
docker "${DOCKER_ARGS[@]}" \
    "${BUILD_CONTAINER_NAME}" \
    bash .github/scripts/build-in-alpine.sh "$@" \
    2>&1 | tee "${LOG_DIR}/alpine-${MODE}.log"
status=${PIPESTATUS[0]}
set -e

if ((status != 0)); then
    failure_log="${LOG_DIR}/alpine-${MODE}-failure.log"
    tail -n 80 "${LOG_DIR}/alpine-${MODE}.log" > "${failure_log}"
    annotation=$(
        grep -E \
            '(^|: )(fatal error:|error:|internal compiler error:)|Killed|collect2: error:|make(\[[0-9]+\])?: \*\*\*' \
            "${LOG_DIR}/alpine-${MODE}.log" |
            tail -n 20 ||
            true
    )
    if [[ -z "${annotation}" ]]; then
        annotation=$(tail -n 20 "${failure_log}")
    fi
    annotation="${annotation//'%'/'%25'}"
    annotation="${annotation//$'\r'/'%0D'}"
    annotation="${annotation//$'\n'/'%0A'}"
    echo "::error title=Alpine ${MODE} failed::${annotation}"
    exit "${status}"
fi
