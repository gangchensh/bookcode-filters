# 常见问题

## 终端每次执行命令都有提示声

在 VS Code 按 Ctrl+Shift+P，运行 Preferences: Open User Settings (JSON)，将 `config/vscode-terminal-silent.example.json` 的三个设置合并进现有 JSON 对象。不要覆盖已有设置，注意逗号。它们将命令成功、命令失败和终端铃声的 sound 设为 off。也可在 Ctrl+, 设置页搜索这些完整设置名，将 Sound 选为 off。若声音仍存在，检查 WSL Remote 设置或 Workspace 设置是否覆盖用户设置。

这些声音属于辅助功能信号，关闭声音不需要禁用整个终端 shell integration。参考 [VS Code 辅助功能](https://code.visualstudio.com/docs/configure/accessibility/accessibility)。

## clone: Too many arguments

复制排版命令可能带入多余空格、换行、文字或非 ASCII 连字符。在 Ubuntu 的练习目录执行附件脚本，假定 code 与练习项目并列；当前目录不能有同名非空目标目录：

```sh
bash code/appendix-a/scripts/clone-mil.sh
```

脚本使用 ASCII 减号和带引号的网址。语法修复后，镜像可用性与网络错误需要另行判断。

## Windows Lean 下载 4.31 失败

项目要求的版本与已装版本必须一致。下载 windows.tar.zst 表示扩展使用 Windows 工具链；WSL 中的 Lean 不会自动替代它。CRYPT_E_REVOCATION_OFFLINE 表示 Windows TLS 后端无法查询证书吊销状态，错误发生在下载阶段。

本附件推荐 Windows VS Code 连接 WSL：命令面板执行 WSL: Reopen Folder in WSL，确认左下角发行版，安装 Lean 扩展到该 WSL，然后在 Ubuntu 项目终端检查：

```sh
cat lean-toolchain
command -v lean
elan toolchain list
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lean --version
elan run "$project_toolchain" lake build
```

已有完整准确版本可按 migration.md 登记本地工具链。坚持 Windows 原生路线则检查系统时间、代理及证书服务连通性，安装准确的 Windows 版本。不要关闭 TLS 校验或修改项目版本来掩盖网络错误。

## VS Code Git 只有 message 和 Publish Branch

仓库干净时没有待提交文件是正常情况。修改文件并保存，再看 Changes。Publish Branch 是发布没有上游的分支，不是本地提交必需步骤。用 git status --short 和 git rev-parse --show-toplevel 检查目录与仓库。提交输入框不代表存在未提交修改。

## 复制粘贴

Linux VS Code 编辑区通常 Ctrl+C / Ctrl+V；集成终端默认 Ctrl+Shift+C / Ctrl+Shift+V。Windows VS Code 即使终端运行 Ubuntu，也通常使用 Windows 界面的快捷键。终端无选区时 Ctrl+C 通常中断程序。可通过编辑菜单和 Keyboard Shortcuts 核对自定义设置。

参考：[终端快捷键](https://code.visualstudio.com/docs/terminal/basics)、[Git 界面](https://code.visualstudio.com/docs/sourcecontrol/overview)。
