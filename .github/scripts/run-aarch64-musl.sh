#!/usr/bin/env bash

set -euo pipefail

: "${MSYSROOT:?MSYSROOT is required}"

TARGET="aarch64-linux-musl"
target_root="$(dirname "${MSYSROOT}")"
toolchain_root="$(dirname "${target_root}")"
target_ld_paths=()

if [[ ! -f "${MSYSROOT}/lib/ld-musl-aarch64.so.1" ]]; then
    echo "Missing musl dynamic loader: ${MSYSROOT}/lib/ld-musl-aarch64.so.1" >&2
    echo "MSYSROOT must point to the ${TARGET} sysroot" >&2
    exit 1
fi

append_target_ld_path() {
    local path="$1"
    local existing_path

    if [[ ! -d "${path}" ]]; then
        return
    fi
    for existing_path in "${target_ld_paths[@]}"; do
        if [[ "${existing_path}" == "${path}" ]]; then
            return
        fi
    done
    target_ld_paths+=("${path}")
}

is_target_ld_path() {
    local path="$1"

    case "${path}" in
        "." | ./* | ../*)
            return 0
            ;;
        *"/${TARGET}/"* | "${target_root}"/* | "${MSYSROOT}"/*)
            return 0
            ;;
    esac

    if [[ -n "${GITHUB_WORKSPACE:-}" ]]; then
        case "${path}" in
            "${GITHUB_WORKSPACE}"/*)
                return 0
                ;;
        esac
    fi

    return 1
}

if [[ -n "${LD_LIBRARY_PATH:-}" ]]; then
    IFS=':' read -r -a existing_ld_paths <<< "${LD_LIBRARY_PATH}"
    for path in "${existing_ld_paths[@]}"; do
        if [[ -z "${path}" ]]; then
            continue
        fi
        if is_target_ld_path "${path}"; then
            append_target_ld_path "${path}"
            continue
        fi
        echo "Ignoring host LD_LIBRARY_PATH entry for ${TARGET}: ${path}" >&2
    done
fi

append_target_ld_path "${target_root}/lib"
append_target_ld_path "${target_root}/lib64"
if [[ -d "${toolchain_root}/lib/gcc/${TARGET}" ]]; then
    shopt -s nullglob
    for path in "${toolchain_root}/lib/gcc/${TARGET}"/*; do
        append_target_ld_path "${path}"
    done
    shopt -u nullglob
fi
append_target_ld_path "${MSYSROOT}/lib"
append_target_ld_path "${MSYSROOT}/usr/lib"
append_target_ld_path "${MSYSROOT}/usr/local/lib"

target_ld_path="$(
    IFS=':'
    printf '%s' "${target_ld_paths[*]}"
)"

if [[ "$(uname -m)" == "aarch64" ]]; then
    export LD_LIBRARY_PATH="${target_ld_path}"
    exec "$@"
fi

exec env -u LD_LIBRARY_PATH \
    qemu-aarch64 \
        -L "${MSYSROOT}" \
        -E "LD_LIBRARY_PATH=${target_ld_path}" \
        "$@"
