# Lean 版本不一致：三种处理办法

对应正文 A.12，日常简写条件见 [Lake 命令写法](lake-command-forms.md)。这里“根目录”指当前 Lean 项目根目录，不限于 CalculusLean。

先区分项目要求与实际工具。优先让工具适应已有项目；主动改变项目要求是升级，不是让版本数字看起来相同。lakefile 中项目自身的 version（如0.1.0）也不是 Lean 版本。

- 方法一保留项目，通过 elan run 临时调用项目工具链。只对本次命令选版，不修复直接 lake 的入口。
- 方法二保留项目，在当前终端安装并选择所需工具。示例只影响当前终端和随后启动的程序；切换项目后重新选择，不把固定版本的真实 bin 写进 .bashrc。查询真实路径时，ELAN_TOOLCHAIN 临时指定 elan which 的查询版本，dirname 取目录，PATH 令其优先，unset 清除残留覆盖，hash -r 清除 Bash 路径缓存。alias 等问题仍可能覆盖选择，需另查。
- 方法三确需升级时，在试验分支或独立副本中一起更新 Lean、mathlib 及其他依赖，更新清单、取得相容缓存并重新检查全部交付代码。示例升级到4.35.0；已经采用该组合的项目不用重复，4.31.0基础项目也不要求升级。

下面依次收录正文的操作框。不要整份执行；先选方法，再核对每框的目录和前提。方法三运行前保存并提交工作，git status --short 无输出才继续；已有修改先处理。升级失败保留分支，切回原分支后重新核验相应编译结果。不要直接修改旧清单的版本文字，也不要通过删除所有缓存代替升级。

## 方法一：临时选择工具链

当前 Lean 项目根目录；保留项目文件与终端原有版本选择。

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run --install "$project_toolchain" lean --version
elan run "$project_toolchain" lake --version
elan run "$project_toolchain" lake build
```

## 方法一：检查独立练习

CalculusLean 根目录；已按本项目的 lean-toolchain 赋值。

```bash
elan run "$project_toolchain" lake env lean MathlibSmoke.lean
```

## 方法二：在当前终端选用工具

当前 Lean 项目根目录；只调整当前终端及随后启动的程序。

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan toolchain install "$project_toolchain"
lake_path=$(ELAN_TOOLCHAIN="$project_toolchain" elan which lake)
export PATH="$(dirname "$lake_path"):$PATH"
unset ELAN_TOOLCHAIN
hash -r
lean --version
lake --version
```

## 方法三：建立升级分支并取得配套版本要求

待升级的 Git 项目根目录；已保存并提交工作，目标分支名尚未使用。

```bash
git status --short
git switch -c upgrade-lean-4.35
curl -fL https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/lean-toolchain -o lean-toolchain
```

## 方法三：编辑已有依赖条目

升级分支中的 lakefile.toml；替换已有的 mathlib 依赖条目。

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"
```

## 方法三：更新工具链与依赖清单

升级分支的项目根目录；依赖声明已修改并保存。

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan toolchain install "$project_toolchain"
elan run "$project_toolchain" lake update
```

## 方法三：按需补齐缓存

升级分支的 mathlib 项目根目录；仅在需要补齐新版本缓存时运行。

```bash
elan run "$project_toolchain" lake exe cache get
```

## 方法三：构建与检查

升级试验项目根目录；缓存准备已结束，不并行更新与构建。

```bash
elan run "$project_toolchain" lake build
elan run "$project_toolchain" lake env lean MathlibSmoke.lean
```

其他直接依赖也须核对；使用 lakefile.lean 时修改对应 require 声明。lake update 可能自动获取缓存，已经完成时跳过 cache get。更新与构建串行执行，独立练习文件名按实际替换。升级通过后提交 lean-toolchain、lakefile、lake-manifest.json 和必要的源码改动。VS Code 还要核对所打开项目及固定服务器路径并重载窗口；终端变更不会自动切换现有服务器。
