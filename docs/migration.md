# 环境迁移

先核对操作系统、CPU 架构和准确版本。优先复制项目源码及 lean-toolchain、Lake 配置、lake-manifest.json、_CoqProject 和 Makefile，再重建环境。

## Rocq / opam

在源机器的目标 switch 导出：

```sh
opam switch export --full --freeze calculus-rocq.export
opam repository list
```

另记系统依赖、仓库和本地 pin 源码。目标 Ubuntu 已安装 opam 并配置仓库后：

```sh
opam switch create calculus-copy --empty
eval "$(opam env --switch=calculus-copy --set-switch)"
opam switch import calculus-rocq.export
```

导出文件不是离线二进制包，import 通常仍需下载和编译。不要直接搬一个 .opam switch 并假定其绝对路径能自动更新。

## Lean 同平台离线工具链

复制完整、同系统同 CPU 的工具链目录，保留权限和符号链接。假设解压到 ~/tools/lean-4.31.0，且已安装 elan：

```sh
"$HOME/tools/lean-4.31.0/bin/lean" --version
elan toolchain link local-4.31.0 "$HOME/tools/lean-4.31.0"
cd /mnt/d/calculus-work/CalculusBasics
elan override set local-4.31.0
elan run local-4.31.0 lean --version
elan run local-4.31.0 lake build
```

用 elan override unset 撤销目录覆盖。Linux 二进制不能当作 Windows 程序。mathlib 离线构建还需对应依赖源码和缓存；复制完整项目的 .lake 后检查绝对链接和构建。

## 整个 WSL 迁移

在源 Windows PowerShell 保存工作并关闭程序后：

```powershell
wsl --list --verbose
wsl --terminate Ubuntu
wsl --export Ubuntu D:\transfer\ubuntu-calculus.tar
```

发行版名和已创建的输出目录按实际替换。目标同架构 Windows 已安装 WSL，归档已复制后：

```powershell
wsl --import CalculusUbuntu D:\WSL\CalculusUbuntu D:\transfer\ubuntu-calculus.tar --version 2
wsl -d CalculusUbuntu -u student
```

student 替换成原发行版的普通用户名。归档含私人文件与凭据，不能公开上传；/mnt/d 上的 Windows 文件需要另行复制。Windows VS Code、WSL 扩展需在新机器安装，证明器扩展需在对应 WSL 中核验。

参考：[WSL 命令](https://learn.microsoft.com/en-us/windows/wsl/basic-commands)、[elan 工具链](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/)、[opam switch](https://opam.ocaml.org/doc/man/opam-switch.html)。
