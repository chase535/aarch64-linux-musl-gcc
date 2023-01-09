# aarch64-linux-gnu-with-musl

### aarch64-linux-gnu与musl的结合，更方便的跨平台静态编译aarch64平台的C语言程序

每天自动拉取最新Binutils、GCC、musl源码进行CI构建

使用时务必确保aarch64-linux-gnu与musl这两个文件夹位于同一目录下

在编译时将C编译器改为“项目目录/musl/bin/musl-gcc”即可

亦可单独使用其中的aarch64-linux-gnu来作为普通的GCC编译器

为了保证musl编译出来的程序能够在未安装musl的aarch64设备上运行，默认静态链接musl库

如需动态链接，请自行fork一份后修改build.yml中第130行，将“--disable-shared”改为“--enable-shared”

CI构建的步骤很详细，如需在本机构建安装，设置好变量，按顺序执行build.yml中的每一步即可
