# 快速上手：下载安装证明器

## Windows 上的交互式图形用户界面安装

RocqIDE 是 Rocq 的专用交互界面，支持编辑、查看目标和单步执行。Windows 的 Rocq Platform 二进制安装包把证明器、RocqIDE、标准库及配套组件一起提供，按图形向导安装即可开始使用。

从 [官方安装页](https://rocq-prover.org/install) 进入 [Platform 发布页](https://github.com/rocq-prover/platform/releases)，下载适合机器架构的安装包，选择目录并按向导完成。打开 RocqIDE 后，可用 `rocq/AppendixA/FirstProof.v` 核验；新建例子文件不是安装要求。

Example 声明命题，Proof 开始证明，reflexivity 用自反性完成计算后的等式，Qed 关闭证明。详细练习见 [RocqIDE 与单步操作](rocqide-and-stepping.md)。

Lean 的便捷桌面路线是 VS Code 与官方 Lean 4 扩展，没有直接对应上述专用 IDE 安装包的官方整套下载方式。Rocq 和 Lean 都能通过 VS Code 实现编辑与执行一体化；具体安装见 [快速入门](../docs/quickstart.md) 和附录分节命令。VsRocq 要求独立安装相配的语言服务器，见 [服务器配置](vsrocq-server.md)。

## 在线环境

- [Lean Web](https://live.lean-lang.org/)：可输入 `lean/AppendixA/FirstProof.lean`。
- [jsCoq](https://coq.vercel.app/)：打开 scratchpad，输入 Rocq/Coq 示例，用 Alt+Down 前进。该入口仍以 Coq 命名，版本和库不保证与 Rocq 9 相同。

在线环境适合短例子，版本与库由服务决定，请把代码另存到本地。

## AI 辅助安装

向能操作本机的智能体说明系统和教材要求的版本，请它检查已有环境、安装相配组件，报告安装位置与核验结果。聊天式大模型可以解释操作步骤。

初学者仍建议亲手完成一次安装，学习理解 AI 的操作。中大规模项目需要命令行、工具链、依赖管理、Git 和构建工具。

遇到问题时请向大模型提供系统信息、实际命令、版本与完整报错，不要提供凭据。
