# aarch64-linux-musl-gcc

**由于近期gcc14的改动暂未支持musl，所以暂时clone gcc的releases/gcc-13分支，待gcc14支持musl后恢复clone master分支**

适用于**x64**平台的gcc交叉编译器，使用musl libc代替glibc，用于交叉编译**aarch64**平台的程序

开启GitHub Actions，**协调世界时每周周一的1点（UTC+0100）左右**自动拉取最新的binutils、gcc、musl源码及最新的Release版GMP、MPFR、MPC、ISL源码进行CI构建并推送

构建步骤在build.yml中写的很详细，如果想要本地使用，可以直接clone本仓库，亦可执行build.yml中的步骤自行部署
