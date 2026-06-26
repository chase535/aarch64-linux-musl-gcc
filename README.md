# aarch64-linux-musl-gcc

适用于 **x86_64 Linux** 平台的 GCC 交叉编译器，用于交叉编译 **aarch64** 平台程序，目标端使用 musl libc 代替 glibc。

工具链自身使用 x86_64-musl 静态链接，不依赖宿主系统的 glibc。由于纯静态 musl 程序不支持运行时加载动态插件，构建时关闭了 GCC LTO 和 linker plugin；普通 C/C++、OpenMP、目标端共享库与静态库均保留。

开启 GitHub Actions 后，**协调世界时每周一 1 点左右**自动 clone 最新的 binutils、GCC、musl 源码，并下载最新 Release 版 GMP、MPFR、MPC、ISL 源码，在 Alpine x86_64-musl 环境中构建并推送。

构建步骤位于 `build.yml` 和 `.github/scripts`。本地使用时可以直接 clone 本仓库，也可以按 workflow 中的步骤自行构建。

## 静态链接

交叉编译器默认生成**静态链接**的 ELF 文件（通过 GCC specs 文件注入 `-static`）。编译产物可以直接在目标 aarch64 Linux 系统上运行，无需 musl 动态链接器。

如需动态链接，使用以下任一方式覆盖：

```bash
# 方式一：忽略自定义 specs
aarch64-linux-musl-gcc -specs=/dev/null hello.c -o hello

# 方式二：显式切换为动态链接
aarch64-linux-musl-gcc -Wl,-Bdynamic hello.c -o hello
```

普通的 `-Wl` 参数（如 `-Wl,-O2`、`-Wl,--hash-style=both`）不会覆盖默认的 `-static`，只有 `-Wl,-Bdynamic` 或 `-specs=/dev/null` 等显式切换动静态的参数才会生效。
