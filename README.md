# aarch64-linux-musl-gcc

适用于**x64**平台的gcc交叉编译器，使用musl libc代替glibc，用于交叉编译**aarch64**平台的程序

开启GitHub Actions，每天**北京时间0时左右**自动拉取最新binutils、gcc源码进行CI构建并推送

构建步骤在build.yml中写的很详细，如果想要本地使用，可以直接clone本仓库，亦可执行build.yml中的步骤自行部署
