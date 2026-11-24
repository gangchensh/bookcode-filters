# Rocq 与 Lean 工具链

正文 A.2 提前介绍检查、模块编译与构建，A.11 用具体项目说明目标和范围。检查核对定义与证明；模块编译生成可导入的二进制目标文件（库文件）；构建按依赖组织这些工作。Lean 同样使用编译和构建术语，Lake 是构建工具。

模块是可被其他文件导入的代码单位，本书通常以一个源文件对应一个模块。模块名称与定义所在的 namespace 作用不同：import／Require 表示模块依赖，namespace 管理定义名称。

构建目标是交给工具的一项结果或操作；证明目标是当前待证命题。库目标处理模块及其依赖，clean 是清理目标。构建成功仍须核查 sorry、Admitted 和依赖假设，不能据此断言所有文件或证明均已完整。

| 工作 | Rocq | Lean |
| --- | --- | --- |
| 版本、包 | opam switch 与软件包、Platform | elan 工具链、Lake 项目依赖 |
| 单文件 | `rocq compile File.v`（9.2.0） | `lake env lean File.lean` |
| 可导入的库文件扩展名 | 通常 `.vo` | 通常 `.olean`；构建还可产生 `.ilean` 交互信息文件 |
| 项目 | `rocq makefile` 与 Make | `lake build` |
| 编辑器 | RocqIDE 或 VsRocq 逐步处理脚本 | Lean 语言服务器增量处理、InfoView 查看状态 |

单独 `lake env lean File.lean` 默认不写同名 `.olean`。需要保存时使用 `lake env lean -o File.olean File.lean`，或构建项目已声明的库目标。lake env 提供项目依赖环境；指定文件检查仍会载入依赖模块，但不代替库目标构建。两者都要保存文件并按项目要求构建，检查未完成证明。

## `elan run` 与安装

`--install` 有两个 ASCII 减号，明确表达需要时安装工具链的意图。省略它不能作为禁止下载或离线开关：本书核对的 elan 4.2.3 即使省略，也会安装缺少的发行工具链。无法安装、网络失败或版本不存在时会报错退出，不会自动改用别的版本。

参考：[Lake 官方文档](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)、[elan 工具链实现](https://github.com/leanprover/elan/blob/master/src/elan/toolchain.rs)。
