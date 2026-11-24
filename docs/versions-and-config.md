# 版本和配置

多版本空间统计、项目升级与旧环境卸载见 [版本维护](../appendix-a/version-maintenance.md)；命令集中在附录 [A.12](../appendix-a/commands/a12.txt)。

## Lean

- `lean/lean-toolchain` 记录精确版本，不跟随 `stable` 自动改变。
- `lean/lakefile.toml` 声明包名、库和构建目标。
- `lean/lake-manifest.json` 是 Lake 生成的依赖清单，应随源代码保存。
- `.lake/` 是生成目录，不上传。
- 查看 `elan show`、`elan toolchain list` 和 `lean --version`；`elan default` 改默认值，`elan override set` 只覆盖某个目录，`elan run VERSION lean --version` 临时使用指定工具链。

切换项目可能自动切换版本。升级工具链和 mathlib 应在实验分支完成，重新检查所有代码；不要只修改一个版本字符串。

## 终端与 VS Code 版本不一致

例如，项目要求Lean4.35.0，终端显式elan run也使用4.35.0，但VS Code日志出现 `.../toolchains/stable/bin/lake setup-file ...`。直接查看该目录的Lean，实际为4.31.0。如果`.elan/bin/lean`与`lake`被直接链接到该固定工具链，就会绕过正常代理。

- `stable`是发布通道，不是固定版本；本地目录名不能证明实际程序版本。
- `lean-toolchain`声明项目版本；lakefile和manifest另行声明、固定mathlib等依赖。
- 正常elan代理按上下文选择工具链。最近目录的配置优先于更远父目录，同目录override可以覆盖文件；无项目选择时才使用默认值。显式elan run选择一次调用的版本。
- 项目文件无法强迫直接启动的某个绝对路径程序改变版本。alias、PATH、环境变量和手工链接都可能改变实际路线。
- 集成终端与扩展是不同进程。终端中的source、export和elan run不永久修改已运行的扩展环境。

在项目根目录检查：

```bash
pwd
cat lean-toolchain
type -a lean lake elan
lean --version
lake --version
elan show
elan override list
printenv ELAN_TOOLCHAIN
ls -l "$HOME/.elan/bin/lean" "$HOME/.elan/bin/lake"
readlink -f "$HOME/.elan/bin/lean"
readlink -f "$HOME/.elan/bin/lake"
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lean --version
elan run "$project_toolchain" lake --version
```

`printenv`无输出通常表示未设置；符号链接本身不是错误，要看它最终指向正常代理还是固定版本的真实程序。比较直接调用与显式elan run的结果。新终端要重新赋值project_toolchain，工具链和库仍保存在磁盘上。

在VS Code直接打开CalculusLean根目录，WSL用户确认WSL: Ubuntu。检查InfoView失败命令和“输出”面板中Lean相关通道，对日志显示的绝对路径检查程序版本。`Built`行是构建成功日志，不是失败原因；setup-file用于准备编辑器检查环境。

长期方案是恢复正常elan代理与PATH，修改前记录并备份配置，考虑其他项目；不要覆盖stable目录。局部方案可合并 [工具链路径示例](../config/vscode-lean-toolchain.example.json) 到**这个项目**的`.vscode/settings.json`，替换真实用户名及与lean-toolchain匹配的已安装版本。

`lean4.envPathExtensions`增加Lean扩展及其子进程的PATH，不安装工具链，不改变项目声明，也不设置终端全局PATH。只有打开对应项目、在正确的WSL环境中应用它才有意义。该绝对路径不适合作为公共默认配置。版本升级后要同步检查，正常代理恢复后可以移除局部覆盖。

修改后Developer: Reload Window，重新查看实际启动路径。正确版本的cache get正在运行时等待它结束，不重复启动；随后在同一版本下build和单独检查MathlibSmoke.lean，最后Restart File。不要立即升级mathlib或删除整个.lake。

参考：[elan工具链规则](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/)、[Lean扩展配置](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/package.json)。

## CRLF 导致非法工具链名

如果cat看似正常，elan却报invalid toolchain name，error开头显示错位。Linux通常用LF，Windows常用CRLF；命令替换去掉末尾LF但留下CR，变量中隐藏的回车也会影响报错排版。双引号不删除CR。

只读检查：

```bash
cat -A lean-toolchain
raw_toolchain=$(cat lean-toolchain)
printf '%q\n' "$raw_toolchain"
od -An -tx1 lean-toolchain
```

cat -A显示的^M是CR，行末$是显示标记；od中的0d 0a为CRLF，0a为LF。

统一赋值：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lean --version
elan run "$project_toolchain" lake --version
```

tr -d删除CR和LF，不修改原文件。仅适用于应含单项标识的lean-toolchain；不能修复错误拼写、多行内容、BOM或空格。VS Code状态栏选择LF并保存为UTF-8无BOM；修改后重新赋值变量。切换项目也重新赋值。

换行修复不等于升级版本。不同项目可以固定不同版本。只把lean-toolchain从4.34.1改为4.35.0，不会自动升级仍固定4.34.1的mathlib和编译文件。运行原项目要核对原来相容组合；真正升级应先保存工作，在独立分支或副本中核对Lean、mathlib及其他依赖、更新清单、取得相容缓存或重建、检查所有目标和独立文件，并核对编辑器固定路径。

## Rocq

- `rocq/_CoqProject` 记录逻辑目录和源文件；本项目使用传统名称以兼容编辑器。
- `RocqMakefile` 由 `rocq makefile` 生成，不手工编辑，不上传。
- 使用 `opam switch list`、`opam list --installed` 和 `rocq -v` 核对环境。
- `eval "$(opam env --switch=SWITCH_NAME --set-switch)"` 为当前 shell 选择 switch；需要时重开编辑器并修改语言服务器路径。
- `.vscode/settings.json` 包含本机路径，默认不上传；使用示例文件生成自己的设置。
- Rocq 9.2 仍支持 coqrc 启动脚本，包括 `$HOME/.coqrc` 与版本专用名称，并优先检查配置目录；`-q` 禁用自动启动脚本，`-init-file` 明确指定文件。可选 `config/coqrc.example` 只设显示宽度。本项目不要求隐式导入；把导入写在源文件里。

## Bash

`config/bashrc.example` 是建议追加的交互配置片段，不自动替换用户配置。先备份 `.bashrc`，把片段复制到 `~/.bashrc.d/calculus.sh`，再在 `.bashrc` 末尾加入受存在性检查的 `source`。`bash -n` 检查语法；`PS1` 决定提示符；`CALCULUS_WORK` 和 `CALCULUS_CODE` 指向自行选定的目录。`rocqenv SWITCH_NAME` 显式选择 switch，不在每次开终端时安装或升级软件。
