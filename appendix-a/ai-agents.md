# AI智能体：Kimi Code与Codex

可选安装示例，按2026-10-13官方文档核对。推荐在证明器所在的WSL Ubuntu或原生Ubuntu运行CLI，Windows安装的客户端不会自动成为Linux命令。以下命令在Ubuntu执行，不在聊天输入框执行。

## Kimi Code CLI

当前官方新版使用独立CLI；不要混用旧Python kimi-cli的安装步骤。

```bash
mkdir -p "$HOME/.cache/calculus-install"
cd "$HOME/.cache/calculus-install"
curl -fL https://code.kimi.com/kimi-code/install.sh -o install-kimi.sh
less install-kimi.sh
bash install-kimi.sh
```

less按q返回。安装器可能下载发布文件并准备路径；查看输出，按提示重开终端。无需为独立安装器先安装Node.js。检查和启动：

```bash
command -v kimi
kimi --version
kimi --help
cd /mnt/d/calculus-work/CalculusBasics
kimi
```

项目路径自行替换。首次在Kimi交互输入框执行 `/login`，按官方账户授权或API模式配置；`/help`查看操作，`/exit`退出。账户、费用和可用地区以服务说明为准，个人登录码及密钥不能公开。

参考：[官方项目](https://github.com/MoonshotAI/kimi-code)、[入门](https://github.com/MoonshotAI/kimi-code/blob/main/docs/en/guides/getting-started.md)。

## Codex CLI

当前独立安装器无需先安装npm：

```bash
mkdir -p "$HOME/.cache/calculus-install"
cd "$HOME/.cache/calculus-install"
curl -fL https://chatgpt.com/codex/install.sh -o install-codex.sh
less install-codex.sh
sh install-codex.sh
```

查看脚本，按当前安装器输出处理路径，重开终端后检查：

```bash
command -v codex
codex --version
codex --help
cd /mnt/d/calculus-work/CalculusBasics
codex
```

本人按界面进行账户授权。WSL浏览器回调失败时，可按官方支持情况在Ubuntu shell运行 `codex login --device-auth`，由本人在浏览器完成设备码登录。`codex login status`查询状态，`codex resume`恢复会话；在交互输入框输入 `/`查看命令列表，`/status`查看状态，`/quit`或`/exit`退出。

参考：[OpenAI官方CLI文档](https://learn.chatgpt.com/docs/codex/cli)、[WSL](https://learn.chatgpt.com/docs/windows/wsl)、[认证](https://learn.chatgpt.com/docs/auth)。

## 练习

先给出只读任务：检查工具版本、路径和项目目录，不安装、不修改。理解结果后要求修复一个问题，并保留已有版本。修改证明后要求实际运行Lean/Rocq，检查没有sorry/Admitted，而不是只相信自然语言结论。

CLI安装不等于安装全部数学工具，不等于下载本地大模型。安装及登录需网络和可用服务账户；读者应按自己的账户完成安装核验与登录。凭据、个人主目录和会话记录不上传公开仓库。
