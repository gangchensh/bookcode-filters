# 快速使用

Windows 用户先安装 VS Code 和 WSL 扩展，Ubuntu 中准备 Git、Make、elan 与所选 Rocq switch。确认编辑器连接 WSL: Ubuntu。安装详见 [附录 A](../appendix-a/README.md)。

## 全书 Lean 项目

全书代码已配置 Lean 4.35.0、mathlib v4.35.0，保留仓库附带的 lean-toolchain、lakefile.toml、lake-manifest.json，不运行 lake new 覆盖它们。从仓库根目录进入 lean/：

```bash
cd lean
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run --install "$project_toolchain" lake exe cache get
elan run "$project_toolchain" lake build
code .
```

首次获取依赖和缓存可能较久。缓存已齐全时跳过 get；日常只保存、构建和检查。在仓库根目录直接 make lean，会构建全部入口并检查 examples 中的使用文件。工具链选择正常时，lean/ 中可简写为 lake build；适用条件见 [两种写法](../appendix-a/lake-command-forms.md)。

## Rocq 项目

先选择安装了 Rocq 9.2.0 的现有 opam switch，运行 rocq -v 核验；switch 名字不等于版本。从仓库根目录执行：

```bash
make rocq
```

默认包含 Theories、各章、附录标准库例子和 examples。已在同一 switch 安装 Coquelicot 后，另执行：

```bash
make rocq-coquelicot
```

VS Code 与 RocqIDE 从 rocq/ 启动，并使用 _CoqProject；依赖的 .vo 先由终端构建，再单步运行使用文件。详见 [编辑器依赖](../appendix-a/editor-dependencies.md)。

## 安装练习和模板

正文从零创建的 CalculusBasics、CalculusLean、RocqBasics 是独立练习目录；不要与仓库 lean/、rocq/ 混用配置。证明源码从各语言 AppendixA 复制，特殊配置从 templates 复制到新的练习目录。templates 不参与主构建。

make cleanLean、make cleanRocq 和 make clean 清理生成结果，保留源码、配置和已安装工具。日常不必先清理；这是源码重构后的使用路线，不是缓存故障恢复命令。

清理范围：make cleanLean 执行 lake clean filterCalculus，只删除教材包的生成结果，保留 Mathlib 等依赖的构建缓存；不要把不带包名的 lake clean 当作等价替换。
