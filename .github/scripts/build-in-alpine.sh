#!/usr/bin/env bash

set -euo pipefail

MODE="${1:?build mode is required}"
TARGET="aarch64-linux-musl"
HOST="x86_64-alpine-linux-musl"
JOBS="${BUILD_JOBS:-$(getconf _NPROCESSORS_ONLN)}"
HOST_CFLAGS="-g0 -O2"
HOST_CXXFLAGS="-g0 -O2"
HOST_LDFLAGS="-static"
TARGET_CFLAGS="-g0 -O2"
TARGET_CXXFLAGS="${TARGET_CFLAGS}"
TARGET_LDFLAGS="-Wl,-O2,--hash-style=both"

: "${GITHUB_WORKSPACE:?GITHUB_WORKSPACE is required}"
: "${SOURCE_DIR:?SOURCE_DIR is required}"
: "${OUTPUT_DIR:?OUTPUT_DIR is required}"
: "${BUILD_DIR:?BUILD_DIR is required}"
: "${LOG_DIR:?LOG_DIR is required}"
: "${MPREFIX:?MPREFIX is required}"
: "${MSYSROOT:?MSYSROOT is required}"
: "${HOST_UID:?HOST_UID is required}"
: "${HOST_GID:?HOST_GID is required}"

require_env() {
    local name

    for name in "$@"; do
        if [[ -z "${!name:-}" ]]; then
            echo "${name} is required" >&2
            exit 1
        fi
    done
}

fix_ownership() {
    local path

    for path in "${SOURCE_DIR}" "${OUTPUT_DIR}" "${BUILD_DIR}" "${LOG_DIR}"; do
        if [[ -e "${path}" ]]; then
            chown -R "${HOST_UID}:${HOST_GID}" "${path}" || true
        fi
    done
}

trap fix_ownership EXIT

mkdir -p "${SOURCE_DIR}" "${OUTPUT_DIR}" "${BUILD_DIR}" "${LOG_DIR}"

export CFLAGS="${HOST_CFLAGS}"
export CXXFLAGS="${HOST_CXXFLAGS}"
export LDFLAGS="${HOST_LDFLAGS}"
export CFLAGS_FOR_TARGET="${TARGET_CFLAGS}"
export CXXFLAGS_FOR_TARGET="${TARGET_CXXFLAGS}"
export LDFLAGS_FOR_TARGET="${TARGET_LDFLAGS}"

run_make_check() {
    local log_file="$1"
    local status

    shift
    set +e
    make -k check -j"${JOBS}" "$@" 2>&1 | tee "${LOG_DIR}/${log_file}"
    status=${PIPESTATUS[0]}
    set -e
    return "${status}"
}

clone_source() {
    local repository="$1"
    local commit_id="$2"
    local destination="$3"
    local actual_commit_id

    if [[ ! "${commit_id}" =~ ^[0-9a-f]{40}$ ]]; then
        echo "Invalid commit id for ${repository}: ${commit_id}" >&2
        exit 1
    fi

    rm -rf "${destination}"
    git clone --no-tags --depth=1 "${repository}" "${destination}"
    actual_commit_id=$(git -C "${destination}" rev-parse HEAD)
    if [[ "${actual_commit_id}" == "${commit_id}" ]]; then
        return
    fi

    git -C "${destination}" fetch --no-tags --depth=1 origin "${commit_id}"
    git -C "${destination}" checkout --detach FETCH_HEAD
    actual_commit_id=$(git -C "${destination}" rev-parse HEAD)
    if [[ "${actual_commit_id}" != "${commit_id}" ]]; then
        echo "Expected ${commit_id}, cloned ${actual_commit_id} from ${repository}" >&2
        exit 1
    fi
}

require_installed_headers() {
    local include_dir="$1"
    local header

    shift
    for header in "$@"; do
        if [[ ! -f "${include_dir}/${header}" ]]; then
            echo "Missing installed header: ${include_dir}/${header}" >&2
            exit 1
        fi
    done
}

install_missing_include_files() {
    local source_dir="$1"
    local include_dir="$2"
    local source_file
    local relative_path

    while IFS= read -r -d '' source_file; do
        relative_path="${source_file#"${source_dir}"/}"
        if [[ -f "${include_dir}/${relative_path}" ]]; then
            continue
        fi
        install -Dm644 "${source_file}" "${include_dir}/${relative_path}"
        echo "Installed missing public include file: ${relative_path}"
    done < <(find "${source_dir}" -type f -print0)

    while IFS= read -r -d '' source_file; do
        relative_path="${source_file#"${source_dir}"/}"
        if [[ ! -f "${include_dir}/${relative_path}" ]]; then
            echo "Missing public include file after installation: ${relative_path}" >&2
            exit 1
        fi
    done < <(find "${source_dir}" -type f -print0)
}

verify_prefixed_include_closure() {
    local include_dir="$1"
    local prefix="$2"
    local dependency

    while IFS= read -r dependency; do
        if [[ ! -f "${include_dir}/${prefix}/${dependency}" ]]; then
            echo "Missing ${prefix} include dependency: ${dependency}" >&2
            exit 1
        fi
    done < <(
        grep -RhoE \
            "#[[:space:]]*include[[:space:]]*<${prefix}/[^>]+>" \
            "${include_dir}/${prefix}" |
            sed -E "s|.*<${prefix}/([^>]+)>.*|\\1|" |
            sort -u ||
            true
    )
}

verify_header_compilation() {
    local compiler="$1"
    local language="$2"
    local source="$3"

    shift 3
    printf '%s\n' "${source}" |
        "${compiler}" -x "${language}" -fsyntax-only "$@" -
}

build_headers() {
    local source="$1"
    local repository="$2"
    local commit_id="$3"

    exec > >(tee "${LOG_DIR}/${source}-headers.log") 2>&1
    mkdir -p "${MSYSROOT}/usr/include"
    case "${source}" in
        linux | musl)
            ;;
        *)
            echo "Unsupported header source: ${source}" >&2
            exit 1
            ;;
    esac
    if [[ ! "${commit_id}" =~ ^[0-9a-f]{40}$ ]]; then
        echo "Invalid ${source} commit id: ${commit_id}" >&2
        exit 1
    fi

    clone_source "${repository}" "${commit_id}" "${SOURCE_DIR}/${source}"

    if [[ "${source}" == "linux" ]]; then
        make -C "${SOURCE_DIR}/linux" ARCH=arm64 mrproper -j"${JOBS}"
        make -C "${SOURCE_DIR}/linux" \
            O="${OUTPUT_DIR}/linux" \
            ARCH=arm64 \
            INSTALL_HDR_PATH="${MSYSROOT}/usr" \
            headers_install \
            -j"${JOBS}"
    else
        make -C "${SOURCE_DIR}/musl" \
            ARCH=aarch64 \
            prefix=/usr \
            DESTDIR="${MSYSROOT}" \
            install-headers \
            -j"${JOBS}"
    fi
}

build_gmp() {
    exec > >(tee "${LOG_DIR}/gmp.log") 2>&1

    rm -rf "${SOURCE_DIR:?}/gmp" "${BUILD_DIR:?}/build-gmp"
    mkdir -p "${BUILD_DIR}/build-gmp" "${OUTPUT_DIR}/gmp"
    clone_source "${GMP_REPOSITORY}" "${GMP_COMMIT_ID}" "${SOURCE_DIR}/gmp"
    echo "GMP $(git -C "${SOURCE_DIR}/gmp" rev-parse HEAD)"
    (
        cd "${SOURCE_DIR}/gmp"
        ./.bootstrap
    )

    cd "${BUILD_DIR}/build-gmp"
    "${SOURCE_DIR}/gmp/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --prefix="${OUTPUT_DIR}/gmp" \
        --enable-maintainer-mode \
        --enable-cxx \
        --disable-shared \
        --enable-static
    make all -j"${JOBS}"
    make install -j"${JOBS}"
    require_installed_headers "${OUTPUT_DIR}/gmp/include" gmp.h gmpxx.h
    verify_header_compilation \
        g++ \
        c++ \
        $'#include <gmp.h>\n#include <gmpxx.h>\nint main() { mpz_class value; return 0; }' \
        -I"${OUTPUT_DIR}/gmp/include"
}

check_gmp() {
    exec > >(tee "${LOG_DIR}/gmp-check-driver.log") 2>&1
    cd "${BUILD_DIR}/build-gmp"
    run_make_check gmp-check.log
}

build_isl() {
    exec > >(tee "${LOG_DIR}/isl.log") 2>&1

    rm -rf "${SOURCE_DIR:?}/isl" "${BUILD_DIR:?}/build-isl"
    mkdir -p "${BUILD_DIR}/build-isl" "${OUTPUT_DIR}/isl"
    clone_source "${ISL_REPOSITORY}" "${ISL_COMMIT_ID}" "${SOURCE_DIR}/isl"
    echo "ISL $(git -C "${SOURCE_DIR}/isl" rev-parse HEAD)"
    (
        cd "${SOURCE_DIR}/isl"
        ./autogen.sh
    )

    cd "${BUILD_DIR}/build-isl"
    PYTHON=: \
    "${SOURCE_DIR}/isl/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --prefix="${OUTPUT_DIR}/isl" \
        --with-gmp=system \
        --with-gmp-prefix="${OUTPUT_DIR}/gmp" \
        --with-gcc-arch=no \
        --disable-shared \
        --enable-static
    make all -j"${JOBS}"
    make install -j"${JOBS}"
    install_missing_include_files \
        "${SOURCE_DIR}/isl/include/isl" \
        "${OUTPUT_DIR}/isl/include/isl"
    verify_prefixed_include_closure "${OUTPUT_DIR}/isl/include" isl
    verify_header_compilation \
        gcc \
        c \
        $'#include <isl/id_set.h>\n#include <isl/map_to_basic_set.h>\nint main(void) { return 0; }' \
        -I"${OUTPUT_DIR}/isl/include" \
        -I"${OUTPUT_DIR}/gmp/include"
}

check_isl() {
    exec > >(tee "${LOG_DIR}/isl-check-driver.log") 2>&1
    cd "${BUILD_DIR}/build-isl"
    run_make_check isl-check.log
}

build_mpfr() {
    exec > >(tee "${LOG_DIR}/mpfr.log") 2>&1

    rm -rf "${SOURCE_DIR:?}/mpfr" "${BUILD_DIR:?}/build-mpfr"
    mkdir -p "${BUILD_DIR}/build-mpfr" "${OUTPUT_DIR}/mpfr"
    clone_source "${MPFR_REPOSITORY}" "${MPFR_COMMIT_ID}" "${SOURCE_DIR}/mpfr"
    echo "MPFR $(git -C "${SOURCE_DIR}/mpfr" rev-parse HEAD)"
    (
        cd "${SOURCE_DIR}/mpfr"
        ./autogen.sh
    )

    cd "${BUILD_DIR}/build-mpfr"
    "${SOURCE_DIR}/mpfr/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --prefix="${OUTPUT_DIR}/mpfr" \
        --with-gmp="${OUTPUT_DIR}/gmp" \
        --disable-shared \
        --enable-static
    make all -j"${JOBS}"
    make install -j"${JOBS}"
    require_installed_headers "${OUTPUT_DIR}/mpfr/include" mpfr.h mpf2mpfr.h
    verify_header_compilation \
        gcc \
        c \
        $'#include <mpfr.h>\n#include <mpf2mpfr.h>\nint main(void) { return 0; }' \
        -I"${OUTPUT_DIR}/mpfr/include" \
        -I"${OUTPUT_DIR}/gmp/include"
}

check_mpfr() {
    exec > >(tee "${LOG_DIR}/mpfr-check-driver.log") 2>&1
    cd "${BUILD_DIR}/build-mpfr"
    run_make_check mpfr-check.log
}

build_mpc() {
    exec > >(tee "${LOG_DIR}/mpc.log") 2>&1

    rm -rf "${SOURCE_DIR:?}/mpc" "${BUILD_DIR:?}/build-mpc"
    mkdir -p "${BUILD_DIR}/build-mpc" "${OUTPUT_DIR}/mpc"
    clone_source "${MPC_REPOSITORY}" "${MPC_COMMIT_ID}" "${SOURCE_DIR}/mpc"
    echo "MPC $(git -C "${SOURCE_DIR}/mpc" rev-parse HEAD)"
    (
        cd "${SOURCE_DIR}/mpc"
        autoreconf -i
    )

    cd "${BUILD_DIR}/build-mpc"
    "${SOURCE_DIR}/mpc/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --prefix="${OUTPUT_DIR}/mpc" \
        --with-gmp="${OUTPUT_DIR}/gmp" \
        --with-mpfr="${OUTPUT_DIR}/mpfr" \
        --disable-shared \
        --enable-static
    make all -j"${JOBS}"
    make install -j"${JOBS}"
    require_installed_headers "${OUTPUT_DIR}/mpc/include" mpc.h
    verify_header_compilation \
        gcc \
        c \
        $'#include <mpc.h>\nint main(void) { return 0; }' \
        -I"${OUTPUT_DIR}/mpc/include" \
        -I"${OUTPUT_DIR}/mpfr/include" \
        -I"${OUTPUT_DIR}/gmp/include"
}

check_mpc() {
    exec > >(tee "${LOG_DIR}/mpc-check-driver.log") 2>&1
    cd "${BUILD_DIR}/build-mpc"
    run_make_check \
        mpc-check.log \
        CPPFLAGS="-I${BUILD_DIR}/build-mpc/src -I${OUTPUT_DIR}/mpfr/include -I${OUTPUT_DIR}/gmp/include"
}

clone_toolchain_sources() {
    rm -rf \
        "${SOURCE_DIR:?}/binutils" \
        "${SOURCE_DIR:?}/gcc" \
        "${SOURCE_DIR:?}/musl"
    git clone --branch master --depth=1 \
        https://sourceware.org/git/binutils-gdb.git \
        "${SOURCE_DIR}/binutils"
    git clone --branch master --depth=1 \
        https://gcc.gnu.org/git/gcc.git \
        "${SOURCE_DIR}/gcc"
    git clone --branch master --depth=1 \
        https://git.musl-libc.org/git/musl \
        "${SOURCE_DIR}/musl"

    {
        echo "binutils $(git -C "${SOURCE_DIR}/binutils" rev-parse HEAD)"
        echo "gcc      $(git -C "${SOURCE_DIR}/gcc" rev-parse HEAD)"
        echo "musl     $(git -C "${SOURCE_DIR}/musl" rev-parse HEAD)"
        echo "host     $(gcc -dumpmachine)"
        echo "libc     $(ldd --version 2>&1 | head -1)"
    } | tee "${LOG_DIR}/source-revisions.log"
}

configure_binutils() {
    exec > >(tee "${LOG_DIR}/binutils-configure.log") 2>&1
    cd "${BUILD_DIR}/build-binutils"
    "${SOURCE_DIR}/binutils/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --target="${TARGET}" \
        --prefix="${MPREFIX}" \
        --with-sysroot="${MSYSROOT}" \
        --disable-multilib \
        --disable-nls \
        --disable-plugins \
        --disable-shared \
        --enable-static \
        --disable-werror \
        --with-gmp="${OUTPUT_DIR}/gmp" \
        --with-mpc="${OUTPUT_DIR}/mpc" \
        --with-mpfr="${OUTPUT_DIR}/mpfr" \
        --with-isl="${OUTPUT_DIR}/isl"
}

build_binutils() {
    exec > >(tee "${LOG_DIR}/binutils-build.log") 2>&1
    cd "${BUILD_DIR}/build-binutils"
    make \
        AM_LDFLAGS=-all-static \
        all-binutils \
        all-gas \
        all-ld \
        -j"${JOBS}"
    make \
        AM_LDFLAGS=-all-static \
        install-strip-binutils \
        install-strip-gas \
        install-strip-ld \
        -j"${JOBS}"
}

configure_gcc() {
    exec > >(tee "${LOG_DIR}/gcc-configure.log") 2>&1
    cd "${BUILD_DIR}/build-gcc"
    "${SOURCE_DIR}/gcc/configure" \
        --build="${HOST}" \
        --host="${HOST}" \
        --target="${TARGET}" \
        --prefix="${MPREFIX}" \
        --with-sysroot="${MSYSROOT}" \
        --enable-languages=c,c++ \
        --disable-multilib \
        --disable-bootstrap \
        --disable-libsanitizer \
        --disable-lto \
        --disable-plugin \
        --disable-nls \
        --disable-werror \
        --enable-initfini-array \
        --with-arch=armv8-a \
        --with-abi=lp64 \
        --enable-fix-cortex-a53-835769 \
        --enable-fix-cortex-a53-843419 \
        --with-static-standard-libraries \
        --with-stage1-ldflags="${HOST_LDFLAGS} -static-libstdc++ -static-libgcc" \
        --with-gmp="${OUTPUT_DIR}/gmp" \
        --with-mpc="${OUTPUT_DIR}/mpc" \
        --with-mpfr="${OUTPUT_DIR}/mpfr" \
        --with-isl="${OUTPUT_DIR}/isl"
}

build_gcc_compiler() {
    exec > >(tee "${LOG_DIR}/gcc-compiler.log") 2>&1
    cd "${BUILD_DIR}/build-gcc"
    make all-gcc -j"${JOBS}"
    make install-strip-gcc -j"${JOBS}"
    ln -sf "${TARGET}-gcc" "${MPREFIX}/bin/${TARGET}-cc"
}

build_static_libgcc() {
    exec > >(tee "${LOG_DIR}/gcc-libgcc-static.log") 2>&1
    cd "${BUILD_DIR}/build-gcc"
    make enable_shared=no all-target-libgcc -j"${JOBS}"
    make install-strip-target-libgcc -j"${JOBS}"
}

build_musl() {
    local libgcc_dir

    exec > >(tee "${LOG_DIR}/musl-build.log") 2>&1
    libgcc_dir="$(find "${MPREFIX}/lib/gcc/${TARGET}" -maxdepth 1 -type d -name '[0-9]*' -print -quit)"
    if [[ -z "${libgcc_dir}" ]]; then
        echo "Unable to locate the target libgcc directory" >&2
        exit 1
    fi

    cd "${BUILD_DIR}/build-musl"
    CFLAGS="${TARGET_CFLAGS}" \
        CXXFLAGS="${TARGET_CXXFLAGS}" \
        LDFLAGS="${TARGET_LDFLAGS}" \
        ARCH=aarch64 \
        CC="${TARGET}-gcc" \
        CROSS_COMPILE="${TARGET}-" \
        LIBCC="${libgcc_dir}/libgcc.a" \
        "${SOURCE_DIR}/musl/configure" \
            --host="${TARGET}" \
            --prefix=/usr
    make AR="${TARGET}-ar" RANLIB="${TARGET}-ranlib" -j"${JOBS}"
    make \
        AR="${TARGET}-ar" \
        RANLIB="${TARGET}-ranlib" \
        DESTDIR="${MSYSROOT}" \
        install \
        -j"${JOBS}"
    rm -f "${MSYSROOT}/lib/ld-musl-aarch64.so.1"
    cp -a "${MSYSROOT}/usr/lib/libc.so" "${MSYSROOT}/lib/ld-musl-aarch64.so.1"
}

build_target_libraries() {
    exec > >(tee "${LOG_DIR}/gcc-target-libraries.log") 2>&1
    cd "${BUILD_DIR}/build-gcc"
    make -C "${TARGET}/libgcc" distclean -j"${JOBS}"
    make enable_shared=yes all-target -j"${JOBS}"
    make install-strip-target -j"${JOBS}"
}

patch_gcc_for_static_default() {
    local gcc_cc="${SOURCE_DIR}/gcc/gcc/gcc.cc"

    if [[ ! -f "${gcc_cc}" ]]; then
        echo "ERROR: gcc.cc not found at ${gcc_cc}" >&2
        exit 1
    fi

    # Add "-static" to GCC's DRIVER_SELF_SPECS so the driver defaults
    # to static linking.  User-supplied -shared / -Bdynamic override it
    # because GCC processes options left-to-right and self-specs are
    # processed before user arguments.
    # Step 1: Add trailing comma to the last entry in the array.
    # Find the line before "};" inside driver_self_specs and append ",".
    gawk '
        /static.*driver_self_specs\[/ { in_specs = 1 }
        in_specs && /^};/ {
            in_specs = 0
            need_comma = 1
        }
        {
            if (need_comma && last !~ /,$/) {
                sub(/"$/, "\",", last)
            }
            if (NR > 1) print last
            last = $0
            need_comma = 0
        }
        END { print }
    ' "${gcc_cc}" > "${gcc_cc}.tmp" && mv "${gcc_cc}.tmp" "${gcc_cc}"

    # Step 2: Insert "-static" before the closing brace.
    gawk '
        /static.*driver_self_specs\[/ { in_specs = 1 }
        in_specs && /^};/ {
            print "  \"-static\","
            in_specs = 0
            patched = 1
        }
        { print }
        END { if (!patched) exit 1 }
    ' "${gcc_cc}" > "${gcc_cc}.tmp" && mv "${gcc_cc}.tmp" "${gcc_cc}"

    # Show the patched array for debugging (from definition to first };\n).
    echo "--- driver_self_specs after patch ---"
    gawk '
        /static.*driver_self_specs\[/ { show = 1 }
        show { print }
        show && /^};/ { exit }
    ' "${gcc_cc}"
    echo "--- end ---"

    # Verify "-static" exists and is within the array (line number between
    # the array definition and the next top-level definition).
    local static_line array_start
    static_line="$(grep -n '"-static"' "${gcc_cc}" | head -1 | cut -d: -f1)"
    array_start="$(grep -n 'static.*driver_self_specs\[' "${gcc_cc}" | head -1 | cut -d: -f1)"
    if [[ -z "${static_line}" ]] || [[ -z "${array_start}" ]] || (( static_line <= array_start )); then
        echo "ERROR: Failed to patch gcc.cc — -static not found after array definition" >&2
        exit 1
    fi
    echo "Patched gcc.cc: added -static to DRIVER_SELF_SPECS (line ${static_line})"
}

verify_static_host() {
    local count=0
    local executable

    exec > >(tee "${LOG_DIR}/verify-static-musl-host.log") 2>&1
    while IFS= read -r -d '' executable; do
        if ! file "${executable}" | grep -Eq 'ELF 64-bit.*x86-64'; then
            continue
        fi

        count=$((count + 1))
        echo "Checking ${executable#"${MPREFIX}"/}"
        file "${executable}"
        if ! file "${executable}" | grep -Eq 'statically linked|static-pie linked'; then
            echo "Host executable is not statically linked: ${executable}" >&2
            exit 1
        fi
        if readelf -lW "${executable}" | grep -q 'INTERP'; then
            echo "Host executable has a program interpreter: ${executable}" >&2
            exit 1
        fi
        if readelf -dW "${executable}" 2>/dev/null | grep -q 'NEEDED'; then
            echo "Host executable has a dynamic dependency: ${executable}" >&2
            exit 1
        fi
        if readelf --version-info "${executable}" 2>/dev/null | grep -q 'GLIBC_'; then
            echo "Host executable contains a GLIBC symbol version: ${executable}" >&2
            exit 1
        fi
    done < <(
        find -L "${MPREFIX}/bin" "${MPREFIX}/libexec" \
            -type f \
            -perm /111 \
            -print0
    )

    if ((count == 0)); then
        echo "No x86_64 host executables were checked" >&2
        exit 1
    fi
    echo "Verified ${count} static x86_64-musl host executables"
}

verify_relocatable_toolchain() {
    local relocated_dir="${GITHUB_WORKSPACE}/relocated-toolchain"
    local smoke_dir="${GITHUB_WORKSPACE}/smoke-test"
    local cc
    local cxx
    local expected_sysroot
    local actual_sysroot

    exec > >(tee "${LOG_DIR}/verify-relocatable-toolchain.log") 2>&1
    rm -rf "${relocated_dir}" "${smoke_dir}"
    mv "${MPREFIX}" "${relocated_dir}"
    mkdir -p "${smoke_dir}"

    cc="${relocated_dir}/bin/${TARGET}-gcc"
    cxx="${relocated_dir}/bin/${TARGET}-g++"
    expected_sysroot="$(realpath "${relocated_dir}/${TARGET}/sysroot")"
    actual_sysroot="$(realpath "$("${cc}" -print-sysroot)")"
    if [[ "${actual_sysroot}" != "${expected_sysroot}" ]]; then
        echo "Unexpected sysroot: ${actual_sysroot}" >&2
        echo "Expected sysroot: ${expected_sysroot}" >&2
        exit 1
    fi

    printf '#include <stdio.h>\nint main(void) { puts("ok"); return 0; }\n' \
        > "${smoke_dir}/hello.c"
    printf '#include <iostream>\nint main() { std::cout << "ok"; }\n' \
        > "${smoke_dir}/hello.cpp"
    printf '#include <omp.h>\nint main(void) { return omp_get_max_threads() < 1; }\n' \
        > "${smoke_dir}/openmp.c"
    printf 'int main(void) { volatile __int128 a = ((__int128) 1 << 100) + 7; volatile __int128 b = 11; return a / b == 0; }\n' \
        > "${smoke_dir}/libgcc.c"

    # Dynamically linked: verify binary format, dynamic linker, and execution
    "${cc}" -Bdynamic "${smoke_dir}/hello.c" -o "${smoke_dir}/hello-c-dyn"
    "${cxx}" -Bdynamic "${smoke_dir}/hello.cpp" -o "${smoke_dir}/hello-cpp-dyn"
    "${cc}" -Bdynamic -fopenmp "${smoke_dir}/openmp.c" -o "${smoke_dir}/hello-openmp-dyn"
    "${cc}" -Bdynamic "${smoke_dir}/libgcc.c" -o "${smoke_dir}/hello-libgcc-dyn"

    file "${smoke_dir}/hello-c-dyn" | grep -q 'ARM aarch64'
    file "${smoke_dir}/hello-cpp-dyn" | grep -q 'ARM aarch64'
    file "${smoke_dir}/hello-openmp-dyn" | grep -q 'ARM aarch64'
    file "${smoke_dir}/hello-libgcc-dyn" | grep -q 'ARM aarch64'
    readelf -lW "${smoke_dir}/hello-c-dyn" | grep -q 'INTERP'
    readelf -lW "${smoke_dir}/hello-cpp-dyn" | grep -q 'INTERP'
    readelf -lW "${smoke_dir}/hello-openmp-dyn" | grep -q 'INTERP'
    readelf -lW "${smoke_dir}/hello-libgcc-dyn" | grep -q 'INTERP'

    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-c-dyn" |
        grep '^ok$'
    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-cpp-dyn" |
        grep '^ok$'
    MSYSROOT="${expected_sysroot}" \
        OMP_NUM_THREADS=2 \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-openmp-dyn"
    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-libgcc-dyn"

    # Statically linked (default via DRIVER_SELF_SPECS): verify binary format and execution
    "${cc}" "${smoke_dir}/hello.c" -o "${smoke_dir}/hello-c"
    "${cxx}" "${smoke_dir}/hello.cpp" -o "${smoke_dir}/hello-cpp"
    "${cc}" -fopenmp "${smoke_dir}/openmp.c" -o "${smoke_dir}/hello-openmp"
    "${cc}" "${smoke_dir}/libgcc.c" -o "${smoke_dir}/hello-libgcc"

    file "${smoke_dir}/hello-c" | grep -q 'statically linked'
    file "${smoke_dir}/hello-cpp" | grep -q 'statically linked'
    file "${smoke_dir}/hello-openmp" | grep -q 'statically linked'
    file "${smoke_dir}/hello-libgcc" | grep -q 'statically linked'
    ! readelf -lW "${smoke_dir}/hello-c" | grep -q 'INTERP'
    ! readelf -lW "${smoke_dir}/hello-cpp" | grep -q 'INTERP'
    ! readelf -lW "${smoke_dir}/hello-openmp" | grep -q 'INTERP'
    ! readelf -lW "${smoke_dir}/hello-libgcc" | grep -q 'INTERP'

    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-c" |
        grep '^ok$'
    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-cpp" |
        grep '^ok$'
    MSYSROOT="${expected_sysroot}" \
        OMP_NUM_THREADS=2 \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-openmp"
    MSYSROOT="${expected_sysroot}" \
        "${GITHUB_WORKSPACE}/.github/scripts/run-aarch64-musl.sh" \
        "${smoke_dir}/hello-libgcc"

    mv "${relocated_dir}" "${MPREFIX}"
}

prepare_toolchain_path() {
    export PATH="${MPREFIX}/bin:${PATH}"
}

build_toolchain() {
    local headers_backup="${BUILD_DIR}/cached-target-headers"

    rm -rf "${headers_backup}"
    if [[ -d "${MSYSROOT}/usr/include" ]]; then
        mkdir -p "${headers_backup}"
        cp -a "${MSYSROOT}/usr/include" "${headers_backup}/include"
    fi

    rm -rf \
        "${BUILD_DIR:?}/build-binutils" \
        "${BUILD_DIR:?}/build-gcc" \
        "${BUILD_DIR:?}/build-musl" \
        "${MPREFIX:?}"
    mkdir -p \
        "${BUILD_DIR}/build-binutils" \
        "${BUILD_DIR}/build-gcc" \
        "${BUILD_DIR}/build-musl" \
        "${MPREFIX}" \
        "${MSYSROOT}/usr/include"
    if [[ -d "${headers_backup}/include" ]]; then
        cp -a "${headers_backup}/include/." "${MSYSROOT}/usr/include/"
    fi
    prepare_toolchain_path

    clone_toolchain_sources
    patch_gcc_for_static_default
    configure_binutils
    build_binutils
    configure_gcc
    build_gcc_compiler
    build_static_libgcc
    build_musl
    build_target_libraries
}

verify_toolchain() {
    prepare_toolchain_path
    verify_static_host
    verify_relocatable_toolchain
}

case "${MODE}" in
    headers)
        build_headers \
            "${2:?header source is required}" \
            "${3:?header repository is required}" \
            "${4:?header commit id is required}"
        ;;
    gmp-build)
        require_env GMP_REPOSITORY GMP_COMMIT_ID
        build_gmp
        ;;
    gmp-check)
        check_gmp
        ;;
    isl-build)
        require_env ISL_REPOSITORY ISL_COMMIT_ID
        build_isl
        ;;
    isl-check)
        check_isl
        ;;
    mpfr-build)
        require_env MPFR_REPOSITORY MPFR_COMMIT_ID
        build_mpfr
        ;;
    mpfr-check)
        check_mpfr
        ;;
    mpc-build)
        require_env MPC_REPOSITORY MPC_COMMIT_ID
        build_mpc
        ;;
    mpc-check)
        check_mpc
        ;;
    toolchain-build)
        build_toolchain
        ;;
    toolchain-verify)
        verify_toolchain
        ;;
    *)
        echo "Unsupported build mode: ${MODE}" >&2
        exit 1
        ;;
esac
