# VsRocq 要求安装语言服务器时

本说明对应 A.10.1 的 VsRocq 路线；先完成 A.9 的 Rocq 环境准备，并按 A.10 开头建立 RocqBasics。选择 RocqIDE 时可直接读 A.10.3，不必安装本服务器。多文件项目的构建与路径说明集中在 A.11。

语言服务器是在后台读取代码、调用证明器并返回错误位置、补全和证明目标的程序；VS Code 扩展负责显示与交互。它运行在本机或所连接的 WSL 内，不是网站服务。服务器能启动不等于依赖库已经编译。扩展和服务器是两个组件。服务器包 vsrocq-language-server 提供本地程序 vsrocqtop，不是云服务器；安装好后通常由扩展启动。

1. 确认运行位置：Windows VS Code 连接 WSL 时，在 Ubuntu 安装 Linux 服务器，并把扩展安装在该 WSL。Windows 原生窗口使用 Windows 程序。
2. 查看扩展版本和报错所要求的服务器版本。两者应相配，证明器版本不必与它们相同。
3. 激活装有 Rocq 的 opam switch，先检查已有安装：

```bash
opam switch show
rocq -v
opam list --installed vsrocq-language-server
command -v vsrocqtop
```

若 command -v 没输出，可能未安装或选错 switch。没有 opam 时先按附录安装 Rocq 环境。Platform 可能已提供服务器。

4. 在同一个 switch 安装对应版本。下面是扩展2.5.0、Rocq9.2.0的配对示例，不是所有环境的通用版本：

```bash
opam switch list
eval "$(opam env --switch=calculus-rocq-9.2 --set-switch)"
rocq -v
opam update
opam install rocq-core=9.2.0 vsrocq-language-server.2.5.0 --dry-run
opam install rocq-core=9.2.0 vsrocq-language-server.2.5.0
opam list --installed vsrocq-language-server
command -v vsrocqtop
```

switch 名须按实际替换；先确认已有 Rocq 为9.2.0，dry-run 的求解方案没有意外改变证明器，再执行安装。缺系统依赖时按 opam 的提示处理；求解失败时检查约束，不随意降级。

5. 若自动发现失败或选错环境，在 VS Code 设置搜索 vsrocq.path，填写 command -v 输出的完整路径，目标是 vsrocqtop，不是 rocq、rocqide 或 coqtop。WSL 设置用 Linux 路径。示例配置见仓库 config/vscode-settings.example.json，替换用户和 switch 占位符。
6. 执行 Developer: Reload Window，打开 .v 文件，确认语言模式 Rocq，用 Rocq: Step Forward 执行代码附件中的 rocq/AppendixA/AndDemo.v（或复制到练习目录的 AndDemo.v），Display Proof View 查看目标。
7. 若失败，执行 Rocq: Troubleshooting: Show Log Output，或查看 Rocq Language Server 输出；核对扩展、服务器、证明器版本以及路径，向大模型提供完整错误。

Windows 原生用户先查找 Platform 提供的 vsrocqtop.exe，再核对版本并填入 Windows 路径；不要照搬 Ubuntu 的 opam 命令。Windows 的安装目录不能自动变成 WSL 的 opam switch。

参考：[VsRocq FAQ](https://github.com/rocq-prover/vsrocq/blob/main/docs/FAQ.md)。

路径示例中的 student 或 REPLACE_USER 是假设用户名。实际主目录用 `echo "$HOME"` 查询，服务器以 `command -v vsrocqtop` 的完整输出为准。JSON 设置不是 shell 脚本，不直接把绝对路径替换成字面量 `$HOME` 或 `~`；`${env:HOME}` 也只在支持变量替换的设置字段中有效。本书采用实际绝对路径。

多文件例子的终端构建与两个界面的单步操作见 [编辑器依赖说明](editor-dependencies.md)。

不设置 settings.json 也能正常使用的原因：扩展可以从启动环境的 PATH 自动查找服务器，Lean 也会使用项目的工具链选择。工作正常无需额外配置；只有找不到、选错环境或需编辑行为定制时才设置。查询相应值可用 opam switch show、opam var prefix、command -v vsrocqtop，直接复制最后一条完整输出。
