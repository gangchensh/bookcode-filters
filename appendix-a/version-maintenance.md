# 多版本环境：切换、升级、空间统计与卸载

附录 A.12 集中介绍这些操作，逐条命令见 [a12.txt](commands/a12.txt)。先区分三种工作：切换已有软件、把项目源码迁移到新版本、删除不再使用的环境。它们不能用同一个“升级”命令代替。

## 先查看，再操作

从本公开代码根目录运行：

```bash
bash appendix-a/scripts/version-space.sh lean
```

脚本只读统计每个 Lean 工具链、已登记的 opam switch、共享缓存和指定项目的 `.lake`，不会安装、升级、清理或卸载。可把 `lean` 换成另一个 Lean 项目的完整路径。自定义 `ELAN_HOME`、`OPAMROOT` 会被尊重。局部 switch 的前缀通过 opam 查询，而非假定都在 `~/.opam`。

`.lake` 总量已经包含其中 build/packages 的分项；opam 根目录也包含全局 switch。不要将总量与分项重复相加。符号链接和共享文件会使简单求和偏离实际占用。遍历磁盘较慢时应等待完成；目录不存在的提示不等于安装损坏。

## 切换和升级

- Lean：正常 elan 代理根据当前项目 `lean-toolchain` 选择版本；临时选择可用 `elan run VERSION ...`。版本不一致先核对入口，不随意修改项目要求。
- Lean 真正升级：保留旧源码，在试验分支或独立副本中选择相容的 Lean/mathlib/其他依赖组合；更新依赖清单、取得相容缓存，再构建全部目标及独立练习文件。旧 `.olean` 不能直接转换为新版本文件。Git 分支不会自动隔离 `.lake`。
- Rocq：每个目标版本保留独立 switch。先导出旧环境的软件记录及固定包清单，再准备新 switch 与相容库；对独立源码副本重新生成 Makefile、clean 和构建。新旧 `.vo` 或插件不能混用。
- 安装或构建失败时，从首个真实错误修复模块路径、库接口或证明脚本；安装新证明器不保证源码自动通过。终端通过后仍要重开编辑器并核验语言服务器路径。

## 旧版本与缓存

先核对所有项目版本文件、目录 override、环境变量和编辑器固定路径。默认版本以外的环境仍可能被旧项目使用。elan 的 gc 根据已知项目给出候选，不能代替完整项目清点。

确认不再需要后，Lean 用 `elan toolchain uninstall` 指定准确工具链名；Rocq 用 `opam switch remove` 指定准确 switch 名。应先选中要保留的环境，再卸载旧环境，并保留交互确认。不要用递归删除整个 `.elan`、`.opam` 或项目目录来代替包管理器。

`opam clean --download-cache --logs --dry-run` 只预览指定缓存与日志的清理；随后是否实际清理由用户决定。缓存清理不等于卸载，删缓存也会降低离线重建能力。教材项目的 `make cleanLean` 只处理教材包的构建结果，保留依赖缓存。`cache get` 和 `unpack!` 不是空间清理命令。

WSL 删除文件后，Linux 内的可用空间与 Windows 上 ext4.vhdx 的实际大小可能不同。虚拟磁盘压缩属于单独的系统维护工作，不应删除 ext4.vhdx。

升级时需保留新旧环境，并预留新依赖、构建及解压空间。用当前相近版本的实际占用作预算参考，而非把版本号或单个安装包大小当作总量。

官方资料：[elan 管理](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/)、[opam switch](https://opam.ocaml.org/doc/man/opam-switch.html)、[opam clean](https://opam.ocaml.org/doc/man/opam-clean.html)、[WSL 磁盘空间](https://learn.microsoft.com/en-us/windows/wsl/disk-space)。
