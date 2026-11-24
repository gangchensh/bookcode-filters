# 环境搭建完整在线指南

本目录保留原详细指南的A.1—A.19编号，**不对应新教材简明附录的小节号**。当前《形式化微积分的滤子基础》纸面附录采用简明流程；可复制命令见 [简明附录命令](textbook-quickstart.txt)。在线指南保留更详细的安装、迁移和故障处理，以下原编号供查阅。


完整附件结构见 [目录导览](../docs/repository-layout.md)，两种证明器的多文件操作见 [编辑器依赖](editor-dependencies.md)。

首次体验请先阅读 [快速上手](quick-start.md)：Windows 图形安装、在线证明器与 AI 辅助安装。

A.8 安装 Lean 并完成单文件练习；A.9 准备 Rocq 与可选 Coquelicot；A.10 任选一种 Rocq 编辑器并核验单文件；A.11 集中讲用户模块相互导入、构建与编辑器操作。日常命令见 A.8 和 A.11；何时省去 elan run 前缀见 [Lake 两种写法](lake-command-forms.md)。版本选择见 A.12，三种处理方法见 [版本处理步骤](lean-version-actions.md)，故障分类见 A.16。排错命令只在对应现象出现时使用。

完整网页地址见 [网址文本清单](web-resources.txt)，编号与附录末尾参考目录一致。

Lean 例子见 [Smoke.lean](../lean/AppendixA/Smoke.lean)；复制、InfoView 截图和 Lake 启动问题见 [Lean 图文说明](lean-infoview.md)。

目录约定与正文一致：练习目录默认是 `/mnt/d/calculus-work`，附件目录名为 `code`，与 `CalculusBasics`、`CalculusLean`、`RocqBasics` 并列；主目录方案自行替换练习目录。`lean/AppendixA/Smoke.lean` 是正文 A.8 的完整独立例子；附件根目录下的 `lean/examples/Smoke.lean` 导入本附件的基础库，两者用途不同。全书 lean/ 项目固定 Lean 4.35.0 与 mathlib v4.35.0，公共理论、各章和附录共用配置；附录中读者从零建立的 CalculusBasics 仍以4.31.0示范，按各自项目的 `lean-toolchain` 选择。

配置文件来源、作用范围和 _CoqProject 格式见 [项目配置速查](project-configuration.md)；多文件项目与调试见 [编辑器依赖说明](editor-dependencies.md)。

工具链术语见 [Rocq 与 Lean 对照](toolchain-comparison.md)，导入报错见 [Mathlib 排查](mathlib-import-troubleshooting.md)。

安装前请读 [资源与下载预算](resources-and-downloads.md)，查看 [资源检查命令](commands/resources.txt) 与 [WSL 资源限制](wsl-resources.md)；AI工具见 [Kimi Code 与 Codex](ai-agents.md)，Rocq库环境见 [opam 与 Coquelicot](rocq-environments.md)。多版本空间统计、项目升级与卸载见 [版本维护](version-maintenance.md)，只读脚本为 `scripts/version-space.sh`。

在 VS Code 中打开 commands 下的文本文件，复制所需行到教材指定的终端或文件。文件使用 UTF-8、LF 换行，命令中的减号是 ASCII `-`。优先从文本复制，避免 PDF 字体映射或自动换行改变字符。

这些文件包含 Bash、PowerShell、配置片段、证明源码及标为“输出示例”的核对内容，不可整份执行；输出不输入终端。请结合教材确认输入位置、当前目录和版本，替换占位符，出错即停止。机器配置和软件可能变化，遇到问题请把系统信息、命令和完整报错交给大模型协助排查；不要提交凭据。

## 可执行脚本

从练习目录运行 `bash code/appendix-a/scripts/clone-mil.sh`（假定附件与练习项目并列），会在练习目录克隆镜像仓库；目标 mathematics_in_lean 目录不能已存在且非空。此脚本会访问网络，不会安装或更改系统软件。

从 CalculusLean 项目根目录复制一次 `../code/appendix-a/scripts/check-lean.sh` 到当前目录后，日常运行 `bash check-lean.sh` 检查 MathlibSmoke.lean，或用 `bash check-lean.sh --build` 构建配置目标；也可直接使用 Lake。首次库载入、下载或构建可能较久，暂时没有输出不等于失败；等待时间与按需导入例子见 [Lean 图文说明](lean-infoview.md)。脚本读取当前项目的版本，不主动升级依赖。

## 按小节查找

- [A.1 快速上手](commands/a01.txt)：1 个代码框
- [A.2 证明器、编辑器与数学库的基本概念](commands/a02.txt)：0 个代码框
- [A.3 安装 WSL 与 Ubuntu](commands/a03.txt)：4 个代码框
- [A.4 目录对应关系与工作位置的选择](commands/a04.txt)：6 个代码框
- [A.5 Ubuntu 命令入门](commands/a05.txt)：14 个代码框
- [A.6 安装 VS Code、扩展与 WSL 连接](commands/a06.txt)：4 个代码框
- [A.7 Git：给学习笔记保存可比较的版本](commands/a07.txt)：6 个代码框
- [A.8 安装 Lean 4 并建立项目](commands/a08.txt)：28 个代码框
- [A.9 安装 Rocq、标准库与 Coquelicot](commands/a09.txt)：9 个代码框
- [A.10 Rocq 编辑器与第一个完整证明](commands/a10.txt)：11 个代码框
- [A.11 项目配置与 Make：从单文件到多文件](commands/a11.txt)：29 个代码框
- [A.12 Lean 与 Rocq 的版本切换](commands/a12.txt)：21 个代码框
- [A.13 推荐的 Bash 交互配置](commands/a13.txt)：6 个代码框
- [A.14 常用数学库怎样安装与核验](commands/a14.txt)：1 个代码框
- [A.15 把已有开发环境迁移到另一台机器](commands/a15.txt)：5 个代码框
- [A.16 日常使用、版本记录与问题定位](commands/a16.txt)：14 个代码框
- [A.17 安装与使用 AI 智能体：Kimi Code 与 Codex](commands/a17.txt)：4 个代码框
- [A.18 安装与使用的快速路线](commands/a18.txt)：1 个代码框
- [A.19 Rocq 与 Lean 工具链的对照](commands/a19.txt)：1 个代码框
