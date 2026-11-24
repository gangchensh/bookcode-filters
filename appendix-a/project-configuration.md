# 项目配置与构建（附录 A.11）

ProjectBase 定义 above 和 above_self，examples/ProjectUse 导入它。使用文件在另一目录，需要先构建依赖，再由配置确定导入路径。编辑器与终端打开同一个项目根目录。

## Lean：一个项目管理全书模块

项目根目录 lean/ 固定 Lean 4.35.0 和 mathlib v4.35.0；Theories、Textbook、AppendixA 和 examples 不分别初始化。完整 [lakefile.toml](../lean/lakefile.toml) 为：

```toml
name = "filterCalculus"
version = "0.1.0"
defaultTargets = ["FilterCalculus"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"

[[lean_lib]]
name = "FilterCalculus"
roots = ["FilterCalculus", "Theories", "AppendixA", "Textbook"]
```

当前教材的统一检查入口是 `make check`，它显式构建 `Textbook`；`make chapter CHAPTER=08`使用当前章号的入口。

name 是包名；version 是项目发布版本；require 声明数学库版本；defaultTargets 指定默认目标；roots 登记同一库可构建的四个模块根。每个根对应一个入口文件，不要求存在 FilterCalculus 文件夹。

[FilterCalculus.lean](../lean/FilterCalculus.lean) 为：

```lean
import Theories
import AppendixA
import Textbook
```

Theories.lean汇集公共练习模块，AppendixA.lean导入安装练习源码，Textbook.lean汇集按第1—13章组织的教材模块。Lake 由 roots 和 import 找到源码并按依赖顺序构建，输出在 .lake/build/lib/lean/，例如 Theories/ProjectBase.olean。命名空间管理定义名称，不替代模块路径。

lake-manifest.json 固定实际依赖提交；它由 Lake 更新，不能用手写空 packages 代替。保留仓库清单，首次按需获取缓存，日常不反复 update。只修改工具链字符串不能升级整套数学库。

examples 未被入口导入，因此 make lean 在库构建后单独检查这两个使用文件。编辑器打开 lean/，终端执行相同项目的构建；版本或依赖准备完成后再重新加载文件。详细命令见 [编辑器依赖](editor-dependencies.md)。

## Rocq：路径映射与文件清单

[完整 _CoqProject](../rocq/_CoqProject) 为：

```text
-Q Textbook Textbook
-Q Theories Theories
-Q AppendixA AppendixA
-Q examples Examples
-docroot FilterCalculus
Theories/Eventually.v
Textbook/Ch01/Language.v
Theories/ProjectBase.v
Textbook/Ch02/Eventually.v
Textbook/Ch02/Reciprocal.v
Textbook/Ch02/Sets.v
Textbook/Ch02/Neighborhoods.v
Textbook/Ch03/LocalEstimates.v
Textbook/Ch03/Maps.v
Textbook/Ch02/Filters.v
Textbook/Ch02/Logic.v
Textbook/Ch03/StandardFilters.v
Textbook/Ch03/Approach.v
Textbook/Ch03/LimitRules.v
Textbook/Ch05/Sequences.v
Textbook/Ch04/LocalLimits.v
AppendixA/AndDemo.v
AppendixA/FirstProof.v
examples/ProjectUse.v
examples/Smoke.v
Textbook/Ch04/OneSidedInfinity.v
Textbook/Ch04/LimitRules.v
Textbook/Ch06/Derivatives.v

Textbook/Ch07/Differentiation.v

Textbook/Ch08/Taylor.v
Textbook/Ch03/DefinitionExamples.v
Textbook/Ch03/CoquelicotBridge.v
Textbook/IntroductionExamples.v
```

前四行分别把物理目录映射到逻辑前缀；-docroot 只设置文档安装根名；其后各 .v 文件是生成构建规则时纳入的目标，实际 Require 决定依赖次序。Theories/ProjectBase.v 对应 Theories.ProjectBase，使用文件写 From Theories Require Import ProjectBase.。

在 rocq/ 运行 rocq makefile -f _CoqProject -o RocqMakefile，再运行 make -f RocqMakefile；库与调用文件的 .vo 默认生成在源码旁边。新增文件或改映射后重新生成规则，单改证明时重复 make 即可。RocqMakefile.conf 是生成器记录本次项目参数的辅助配置，不手工编辑。

CoquelicotSmoke.v 和 Textbook/Ch02/CoquelicotBridge.v 需要选装库，由根 Makefile 的 make rocq-coquelicot 单独检查；不纳入默认标准库构建。模板在 rocq/templates，不能用模板覆盖主 _CoqProject。

RocqIDE 从 rocq/ 启动并打开源码，在 Project 偏好启用最近的 _CoqProject；VsRocq 也打开该项目根目录。先构建依赖 .vo，再逐步运行 examples/ProjectUse.v。Require 成功后才检查 exact 的证明项是否匹配目标；导入失败先查路径和产物。

### 可选的 VS Code 设置

.vscode/settings.json 可以不存在。自动找到正确服务器并正常交互时无需新建。确需指定服务器时，选对 switch 后运行 `opam switch show`、`opam var prefix`、`command -v vsrocqtop`；最后一条的完整输出替换 [设置示例](../config/vscode-settings.example.json) 中整段路径，已有 JSON 只合并字段，不猜用户名。不要假定这个扩展设置支持 shell 的 $HOME 展开。

从 rocq 根目录 `code .` 才使用这里的工作区设置；只打开 examples 不应假定父目录工作区设置生效。vsrocq.path 选择服务器，proof.mode 0 选择手动模式；两者不改变终端 switch，也不安装库。extensions.json 只推荐扩展。服务器变更后重载窗口并检查日志；PATH 可能仍来自旧启动环境。

### 扩展选项：目录名与逻辑前缀可以不同

[CoqProject.minimal](../rocq/templates/CoqProject.minimal) 使用 Theories → BookLibrary，仅作格式练习，不覆盖主工程。

| 条目 | 含义 |
| --- | --- |
| -Q <目录> <逻辑前缀> | core → BookTheory 后，core/Basics.v 对应 BookTheory.Basics |
| -R <目录> <逻辑前缀> | compat → Compat，还允许 Require Import Small 这样的部分限定名 |
| 一个 .v 文件名 | 纳入生成构建规则的目标范围 |
| 一个目录名 | 纳入目录及子目录下受支持的源码；新增后重新生成规则 |
| -I plugins | OCaml 插件搜索路径，不替代数学模块的 -Q |
| -arg "-w all" | 把包含空格的警告选项作为整体传递 |
| -docroot PathDemo | 文档安装根名，不改变 Require |

[完整独立示范](../rocq/templates/rocq-paths/_CoqProject) 使用上述条目，core/Basics.v 定义 sample，compat/Small.v 定义 marker，examples/Use.v 导入它们。plugins 为空，只演示路径。在开源代码根目录、已有 Rocq 9.2.0 环境执行：

```bash
cd rocq/templates/rocq-paths
rocq makefile -f _CoqProject -o RocqMakefile
make -f RocqMakefile
```

产生三个模块的 .vo，并显示 marker 的类型 True。`From BookTheory Require Import Basics.` 等价于 `Require Import BookTheory.Basics.`；也可先 Require 再 Import。逻辑前缀本身不必是可单独导入的模块。选用无空格路径，不把全部可选条目拼进主项目。

用户 .bashrc、coqrc 是可选个人设置。例如 [coqrc.example](../config/coqrc.example) 的 Set Printing Width 80. 设置后续 Print 输出的排版宽度，不改变定理或编辑器窗口；临时设40再 Print Nat.add. 可比较换行，下一次读取原配置恢复80。已有配置先备份并合并，不覆盖；源码显式导入数学库，不依赖隐藏导入。

## Make：两条流程的共同入口

开源代码的 [完整 Makefile](../Makefile) 是维护者手写的，现成项目直接使用。它与从 _CoqProject 生成的 RocqMakefile 不同。在代码根目录 `make lean` 构建 Lean 库并检查两个例子，`make rocq` 核对 Rocq 9.2、生成规则并构建；`make` 执行两者。它不安装软件、不选择 opam switch，环境先准备好。

参考：[Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)、[Rocq 工程工具](https://rocq-prover.org/doc/V9.2.0/refman/practical-tools/utilities.html)、[RocqIDE](https://rocq-prover.org/doc/V9.2.0/refman/practical-tools/coqide.html)。

Makefile 另有 cleanLean、cleanRocq、clean 三个可选清理目标，分别清理本附件的 Lean、Rocq 基础产物或两者。保留源码、项目配置和工具链；日常不必执行，清理后需重建，不用它替代 Mathlib 缓存排错。
