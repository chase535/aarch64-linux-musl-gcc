# aarch64-linux-musl-gcc

适用于 **x86_64 Linux** 平台的 GCC 交叉编译器，用于交叉编译 **aarch64** 平台程序，目标端使用 musl libc 代替 glibc。

工具链自身使用 x86_64-musl 静态链接，不依赖宿主系统的 glibc。由于纯静态 musl 程序不支持运行时加载动态插件，构建时关闭了 GCC LTO 和 linker plugin；普通 C/C++、OpenMP、目标端共享库与静态库均保留。

开启 GitHub Actions 后，**协调世界时每周一 1 点左右**自动 clone 最新的 binutils、GCC、musl 源码，并下载最新 Release 版 GMP、MPFR、MPC、ISL 源码，在 Alpine x86_64-musl 环境中构建并推送。

构建步骤位于 `build.yml` 和 `.github/scripts`。本地使用时可以直接 clone 本仓库，也可以按 workflow 中的步骤自行构建。

## 静态链接

交叉编译器默认生成**静态链接**的 ELF 文件（通过 GCC specs 文件注入 `-static`）。

### 为什么默认静态链接

大多数 aarch64 Linux 发行版（如 Ubuntu、Debian）使用 glibc，而本工具链编译出的动态链接程序依赖 musl 的动态链接器 `/lib/ld-musl-aarch64.so.1`。这意味着：

- 在 glibc 系统上无法直接运行动态链接的产物，必须额外安装 musl 库
- 静态链接的产物不依赖任何动态链接器，可以**在任意 aarch64 Linux 系统上直接运行**

因此默认静态链接以保证编译产物的最大兼容性。

### 如需动态链接

使用以下任一方式覆盖默认的静态链接：

```bash
# 方式一：忽略自定义 specs，使用 GCC 默认行为（动态链接）
aarch64-linux-musl-gcc -specs=/dev/null hello.c -o hello

# 方式二：显式切换为动态链接
aarch64-linux-musl-gcc -Wl,-Bdynamic hello.c -o hello
```

普通的 `-Wl` 参数（如 `-Wl,-O2`、`-Wl,--hash-style=both`）不会覆盖默认的 `-static`，只有 `-Wl,-Bdynamic` 或 `-specs=/dev/null` 等显式切换动静态的参数才会生效。

动态链接的产物**只能在以下环境中运行**：

- **Alpine Linux（aarch64）**：系统自带 musl，直接可用
- **其他发行版**：需手动安装 musl 并创建动态链接器：

  ```bash
  # Ubuntu / Debian
  apt install musl
  ln -sf /usr/lib/aarch64-linux-musl/libc.so /lib/ld-musl-aarch64.so.1
  ```

## LTO（Link-Time Optimization）

本工具链**不支持** `-flto` 参数。由于工具链自身为纯静态 musl 链接，GCC 的 LTO linker plugin 需要动态加载（`dlopen`），与静态链接不兼容，因此构建时已通过 `--disable-lto` 关闭。使用 `-flto` 编译会报错。
