# aarch64-linux-musl-gcc

适用于 **x86_64 Linux** 平台的 GCC 交叉编译器，用于交叉编译 **aarch64** 平台程序，目标端使用 musl libc 代替 glibc。

工具链自身使用 x86_64-musl 静态链接，不依赖宿主系统的 glibc。目标端默认生成静态链接程序，同时保留 musl、libstdc++、libgcc_s、libgomp 等动态运行库，因此也可以显式构建动态可执行文件或共享库。由于纯静态 musl 程序不支持运行时加载动态插件，构建时关闭了 GCC LTO 和 linker plugin；普通 C/C++、OpenMP、静态库与动态库可用。

开启 GitHub Actions 后，**协调世界时每周一 1 点左右**自动 clone 最新的 binutils、GCC、musl 源码，并下载最新 Release 版 GMP、MPFR、MPC、ISL 源码，在 Alpine x86_64-musl 环境中构建并推送。

构建步骤位于 `build.yml` 和 `.github/scripts`。本地使用时可以直接 clone 本仓库，也可以按 workflow 中的步骤自行构建。

## 静态链接

交叉编译器默认生成**静态链接**的 aarch64 ELF 文件。`gcc`、`g++`、`cc`、`c++` 不使用 wrapper；默认静态链接通过 GCC installed specs 实现。

### 为什么默认静态链接

大多数 aarch64 Linux 发行版（如 Ubuntu、Debian）使用 glibc。动态链接的 musl 程序需要目标系统提供 musl 动态链接器和匹配的运行库；这会让产物难以在普通 aarch64 Linux 系统上直接运行。

默认静态链接的产物不依赖任何目标端动态链接器，可以**在普通 aarch64 Linux 系统上直接运行**。CI 会在 arm64 Ubuntu 容器中验证 C、C++、OpenMP 和 libgcc 相关静态产物。

因此工具链默认静态链接以保证编译产物的最大兼容性。

### 动态链接参数

需要动态可执行文件时，显式传递 `-specs=dynamic.specs`：

```bash
aarch64-linux-musl-gcc hello.c -o hello
aarch64-linux-musl-g++ hello.cpp -o hello-cpp
aarch64-linux-musl-gcc -specs=dynamic.specs hello.c -o hello-dyn
aarch64-linux-musl-g++ -specs=dynamic.specs hello.cpp -o hello-cpp-dyn
```

默认产物应显示为静态链接，并且没有 `INTERP` 段：

```bash
file hello
readelf -lW hello | grep INTERP
```

动态产物会依赖 musl 动态链接器和对应运行库：

```bash
file hello-dyn
readelf -lW hello-dyn | grep INTERP
readelf -dW hello-dyn | grep NEEDED
```

构建共享库时，使用 GCC 原生 `-shared` 路径：

```bash
aarch64-linux-musl-gcc -shared -fPIC foo.c -o libfoo.so
```

`-Wl,-Bdynamic` 是底层 linker 状态切换，不是推荐的 GCC driver 级 opt-out；需要动态可执行文件时优先使用 `-specs=dynamic.specs`。如果绕过 `gcc`/`g++` driver 直接调用 `aarch64-linux-musl-ld`，则不会读取 GCC installed specs。

### 在没有 musl runtime 的系统上运行动态产物

很多 Linux 发行版默认使用 glibc，并不会预装 musl 动态链接器和 musl 版 C++/OpenMP 运行时。动态 musl ELF 的解释器路径通常是：

```text
/lib/ld-musl-aarch64.so.1
```

如果目标系统的包管理器提供 musl 包，安装后通常只能补齐 musl 动态链接器和 libc，足够运行仅依赖 musl libc 的 C 动态程序。Ubuntu/Debian 可使用：

```bash
apt-get update
apt-get install -y musl
```

C++ 或 OpenMP 动态程序还会依赖 musl 版 GCC 运行库，例如：

```text
libstdc++.so.6
libgcc_s.so.1
libgomp.so.1
```

系统包管理器中的 `libstdc++`、`libgcc_s`、`libgomp` 如果是 glibc 版运行库，就不能满足 musl 动态程序的依赖；文件名相似不代表 ABI 兼容。

如果必须在没有完整 musl runtime 的系统上运行动态链接的 C++/OpenMP musl 程序，需要随程序发布本工具链构建出的 musl 版运行库，或安装一套兼容的 musl GCC runtime。发布包中这些运行库相对工具链根目录的位置是固定的：

```text
aarch64-linux-musl/sysroot/lib/ld-musl-aarch64.so.1
aarch64-linux-musl/sysroot/usr/lib/libc.so
aarch64-linux-musl/lib64/libstdc++.so.6
aarch64-linux-musl/lib64/libgcc_s.so.1
aarch64-linux-musl/lib64/libgomp.so.1
```

如果程序还使用了 `libatomic` 等其他 GCC runtime，请以 `readelf -dW app | grep NEEDED` 的输出为准，从 `aarch64-linux-musl/lib64/` 中一并复制对应的 musl 版 `.so`。

常见做法是把除动态链接器外的运行库放在程序旁边并设置 rpath：

```bash
aarch64-linux-musl-g++ \
  -specs=dynamic.specs \
  -fopenmp \
  -Wl,-rpath,'$ORIGIN/lib' \
  main.cpp -o app
```

示例发布目录：

```text
app
lib/libc.so
lib/libstdc++.so.6
lib/libgcc_s.so.1
lib/libgomp.so.1
```

注意，rpath 只影响普通共享库搜索，不影响 ELF 的动态链接器路径。动态 musl ELF 的解释器仍是 `/lib/ld-musl-aarch64.so.1`，因此目标系统需要在这个绝对路径提供 musl loader。可选做法包括安装系统提供的 musl 包、把发布包中的 `aarch64-linux-musl/sysroot/lib/ld-musl-aarch64.so.1` 安装到目标系统 `/lib/`，或通过 wrapper 显式调用随程序发布的 loader 并指定 library path。

因此，若目标是“复制到没有 musl runtime 的系统后直接执行”，推荐继续使用默认静态链接。动态链接更适合目标环境已经安装了兼容的 musl runtime，或应用自己携带 runtime 的场景。

### 宿主 glibc 版本限制

本项目构建出的交叉编译器本体使用 x86_64-musl 静态链接，因此在 x86_64 Linux 宿主机上运行时不依赖宿主 glibc 版本。

如果改为在 glibc 环境中动态构建交叉编译器本体，构建机的 glibc 版本会成为运行下限。例如在 glibc 2.39 系统上动态构建出的 `aarch64-linux-musl-gcc`、`cc1`、`ld` 等程序，可能无法在 glibc 低于 2.39 的系统上运行。

## LTO（Link-Time Optimization）

本工具链**不支持** `-flto` 参数。由于工具链自身为纯静态 musl 链接，GCC 的 LTO linker plugin 需要动态加载（`dlopen`），与静态链接不兼容，因此构建时已通过 `--disable-lto` 关闭。使用 `-flto` 编译会报错。
