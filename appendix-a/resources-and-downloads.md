# 安装资源、下载量与磁盘占用

以下是本书规划建议。安装所需的硬盘空间依据需求而定，实际占用随版本、库和缓存变化。

| 范围 | 主机内存建议 | CPU建议 | 安装前空闲磁盘 |
| --- | --- | --- | --- |
| 基础安装、短例子 | 至少8GB | 现代64位、2核以上 | 至少20GB |
| 本章完整环境 | 16GB，WSL可用约8GB | 4核以上 | 50–80GB |
| 中等项目、多版本 | 32GB | 8核左右 | 100GB以上 |
| 大项目、库源码重建 | 32–64GB起步 | 8–16核以上 | 200GB以上 |

完整环境包括 Ubuntu、编辑器、Lean/mathlib、Rocq/Coquelicot及语言服务器；选装库和多套环境还需余量。为每个 Lean 工具链预留3–5GB、每个 mathlib 项目5–20GB、每个 Rocq/OCaml环境及选定库5–10GB，另计系统和10–20GB临时空间。库与环境合计先按10–30GB预算，不包括整个操作系统。

编写时一个 Linux Lean4.31.0 工具链实测约2.8GiB；其他数值是规划范围。内存峰值、是否下载缓存和并行任务决定实际需求，通常不需要独立GPU。

从代码根目录在 Ubuntu 执行只读检查：

```bash
bash appendix-a/scripts/check-resources.sh
```

只读脚本直接显示磁盘、内存、处理器和用户工具目录的占用信息，并注明不存在的目录。`du` 统计磁盘占用：`$HOME/.elan` 是当前用户的 Lean 工具链等文件，`$HOME/.opam` 是 opam 管理的 OCaml/Rocq 环境，当前项目的 `.lake` 是依赖与构建文件。请在 Lean 项目根目录检查 `.lake`。

`free -h` 在 WSL 2 中显示分配给 Linux 环境的内存范围及使用情况，通常小于 Windows 主机的物理内存；`available` 是估计还能供程序使用的内存。Windows 的剩余磁盘空间应另在资源管理器中检查，WSL 显示的虚拟盘容量不代表物理盘剩余空间。

WSL 总额度和单个任务的额度是两层设置，见 [WSL 资源配置与任务隔离](wsl-resources.md)（正文 A.5）。

## 各类下载命令的预算

以下为随版本变化的规划范围，不是每个版本的实测大小。按一套环境计算，互为替代的路线不相加。

| 操作 | 首次下载量预算 | 安装后占用预算 |
| --- | --- | --- |
| WSL、Ubuntu、基础 apt 工具 | 1–3GB | 5–10GB |
| apt update | 索引数十至数百MB | 索引、缓存占用另计 |
| VS Code与扩展 | 0.2–1GB | 1–2GB |
| elan及一个Lean版本 | 安装器数至数十MB，工具链0.5–1.5GB | 工具链3–5GB |
| math项目源码、依赖与缓存 | 合计2–8GB | 一个项目5–20GB |
| opam、OCaml、Rocq、Coquelicot、语言服务器 | 合计0.5–3GB | 一个switch约5–10GB |
| MathComp、Flocq等选装库 | 按版本、依赖另计 | 按新增安装、构建内容另计 |
| git clone示例与附件 | 小例子较小，带历史的库可达数百MB或更多 | 源码、历史和构建另计 |
| Kimi Code／Codex（选装） | 脚本很小，客户端数十至数百MB量级 | 两个客户端先留1GB余量 |

主要路线首次总下载先按约5–15GB安排，完成后系统、编辑器、证明器与库合计约20–50GB，再留下载、解压和编译余量，所以建议开始前有50–80GB可用空间。多版本、多个独立项目和更多选装库会继续增加。

curl下载脚本只取得脚本文本，执行脚本才可能取得程序。math项目创建可能已经触发缓存下载，随后cache get复用同一份内容，不应重复相加。build会增加构建产物，但这些不都是下载数据。opam源码包通常比包含编译工具和结果的switch小得多。

用apt确认提示、下载进度及du记录实际量。没有锁定版本与安装集合，不能提供精确总字节数。完整解释见附录A末尾工具链对照一节。

参考：[VS Code要求](https://code.visualstudio.com/docs/supporting/requirements)、[Rocq Platform](https://github.com/rocq-prover/platform/blob/main/doc/README_Linux.md)、[WSL配置](https://learn.microsoft.com/en-us/windows/wsl/wsl-config)。
