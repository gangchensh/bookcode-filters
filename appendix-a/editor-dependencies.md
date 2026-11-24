# 多文件构建与编辑器库依赖（附录 A.11）

阅读顺序与正文相同：先用 ProjectBase → ProjectUse 完成 Lean 的配置、构建和编辑器检查，再完成 Rocq 流程，最后可用代码根目录的 make lean / make rocq 简化操作。配置与编译缺一不可。

目录结构见 [开源代码目录导览](../docs/repository-layout.md)，配置格式见 [项目配置速查](project-configuration.md)。以下从各自 lean/ 或 rocq/ 项目根目录操作。工具安装完成后再执行，不重复创建项目。A.8 的 CalculusBasics/Smoke.lean、CalculusLean/MathlibSmoke.lean 与 A.10 的 RocqBasics 都是另建的单文件练习；这里改用附件现成的 lean/、rocq/，不要在其中再次执行 lake new 或 mkdir RocqBasics。

## Lean：基础模块与独立例子

Theories/ProjectBase.lean 定义 above 并证明 above_self；examples/ProjectUse.lean 导入它。FilterCalculus.lean 通过 Theories、Chapters、AppendixA 汇集公共模块、章节和附录，默认库构建不自动检查 examples；顶层 make lean 已组合构建和两个例子的检查。

### 首次准备

这里的 lean 根目录例如 /mnt/d/calculus-work/code/lean（主目录方案为 $HOME/calculus-work/code/lean），其中有 lean-toolchain、lakefile.toml、FilterCalculus.lean、Theories/、Textbook/、AppendixA/、examples/；不是系统的 / 或工具链安装目录。先 pwd、ls -a 核对，再执行：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run --install "$project_toolchain" lake exe cache get
elan run "$project_toolchain" lake build
elan run "$project_toolchain" lake env lean examples/ProjectUse.lean
code .
```

在 VS Code 打开 examples/ProjectUse.lean，查看 InfoView；by 后目标为 above 3 3，exact 后目标关闭。独立单文件检查不自动写出 ProjectUse.olean。基础模块产物在 lean 根目录的 .lake/build/lib/lean/Theories/ProjectBase.olean，同处还有相应 .ilean；不是 .build。日常也可在 code 根目录直接 make lean，版本正确且经 elan 代理时可在 lean 根目录直接 lake build，再检查指定例子。

### 日常修改

保存源码后，可以在同一终端重复两条 elan run；新开终端或换项目时，先重新读取当前 lean-toolchain。更简洁的入口在 code 根目录：

```bash
make lean
```

它读取项目工具链、构建库并检查两个例子。若直接使用 lake 命令，须先确认由 elan 代理选对版本。构建后再查看编辑器反馈，不重新初始化或下载缓存。

### 出错以后

import 报错先查项目目录、模块名和依赖结果；在终端上编译成功、但编辑器检查失败，查编辑器的项目与版本，再重新启动文件。不要直接修改 lean-toolchain。导入通过后再查看证明目标并检查策略；这个目标与 Make、Lake 的构建目标含义不同。

## Rocq：先构建用户库

ProjectBase.v → ProjectUse.v，Eventually.v → Smoke.v。基础文件都在 Theories，使用文件都在 examples。第一条 Require 依赖已编译的 .vo；另一标签页执行到 Qed 不会自动更新磁盘上的库。

### 首次准备

在 Ubuntu 中选择已有的 Rocq 9.2.0 switch 并构建；示例目录和 switch 名按实际替换：

```bash
cd /mnt/d/calculus-work/code/rocq
eval "$(opam env --switch=calculus-rocq-9.2 --set-switch)"
rocq -v
rocq makefile -f _CoqProject -o RocqMakefile
make -f RocqMakefile
```

这不重新安装证明器。_CoqProject 的前四行是路径映射，其后的文件条目是构建范围，工具按 Require 安排顺序；公共模块、章节与附录标准库文件都由该清单管理；只改内容时保存后再 make，新增文件或改路径、工具版本后重新生成规则。No common logical root 是文档安装根名警告，不等于证明编译失败。

以下手工编译是可选练习，不必在 Make 成功后重复执行；在同一 rocq 根目录使用：

```bash
rocq compile -Q Theories Theories Theories/ProjectBase.v
rocq compile -Q Theories Theories examples/ProjectUse.v
```

直接 rocq compile 不自动读取旁边的 _CoqProject，所以仍须 -Q。成功后有 Theories/ProjectBase.vo 和 examples/ProjectUse.vo，均在对应源码旁，后者可以导入前者。RocqMakefile.conf 保存生成时的项目和工具环境参数，由 RocqMakefile 读取，两者不手改。

### VS Code／VsRocq 单步操作

在 rocq 根目录 code . 打开项目，Windows 用户确认 WSL: Ubuntu，服务器来自相同 switch。RocqBasics 的工作区设置不会自动应用到这里；若自动发现正确并能手动步进，不需要新增设置；否则在当前工作区指定实际 vsrocq.path 和 proof.mode 0。路径以 command -v vsrocqtop 的完整输出为准，JSON 不直接展开 shell 的 $HOME。

打开 examples/ProjectUse.v，点击源码区，执行 Display Proof View，再用 Step Forward（通常 Alt+Down）：

| 检查点 | 结果 |
| --- | --- |
| From Theories Require Import ProjectBase. | 成功导入库，此时没有目标是正常的 |
| Example / Proof | 出现 above 3 3 |
| exact (above_self 3) | 完成目标 |
| Qed | 登记证明 |

用 Step Backward 回退。examples/Smoke.v 同样先导入 Eventually，Check 显示有限合取定理类型；随后 exists 100 选见证、intros n Hn 引入变量和假设、exact Hn 完成目标，最后 Qed。导入失败时先修复环境、逻辑路径和依赖构建，不跳过它继续后面的策略。

### RocqIDE 单步操作

使用构建时同一个 switch，在含 _CoqProject 的 rocq 根目录直接运行 `rocqide`，再用 File / Open 打开 examples/ProjectUse.v。编辑器按该文件关联最近的 _CoqProject；Edit / Preferences / Project 应启用项目选项，examples 不另放冲突配置。空白窗口需打开或保存目标文件才能关联项目。也可 `rocqide examples/ProjectUse.v`。

只有需要显式核验路径时，再用下面的备用命令；不是每次都要运行：

```bash
rocqide -Q Theories Theories -Q examples Examples examples/ProjectUse.v
```

Navigation / Forward（通常 Alt+Down）与 Backward（Alt+Up）逐句操作，目标变化与上表相同。在同一界面打开 examples/Smoke.v 可运行另一组例子。正常读取项目选项时也可用 rocqide examples/ProjectUse.v。

每个缓冲区默认关联源文件所在目录或最近父目录的 _CoqProject；Project 偏好控制读取选项。本例只保留 rocq 根目录一份，子目录另放同名配置可能遮蔽外层配置。不要在 examples 内照抄 -Q Theories Theories，因为相对目录已经改变。

### 日常修改

保存源码，在 rocq 根目录执行：

```bash
make -f RocqMakefile
```

新终端先选择原 switch。新增文件、改映射或版本后重新生成规则；只改证明时复用现有规则。code 根目录的 make rocq 也可用，但它每次核对版本并生成规则。

若修改了基础模块，构建后重新载入 ProjectUse.v。RocqIDE 中这个文件的页签有自己的交互会话，重启解释器就是清空已执行状态，从 Require 开始重新检查，以读取新库；初学者可关闭并重新打开该文件。VsRocq 重新打开文件或重载窗口；修改 _CoqProject 后也应重新打开相关文件。可以保留备份，但编辑器与构建必须指向同一份项目，不把不同目录或版本的 .vo 混用。

### 出错以后

Require 失败先检查逻辑路径及 ProjectBase.vo；终端成功而编辑器失败时比较环境、版本和配置。导入通过而 exact 的证明项不匹配目标时，才检查引理和参数。

外部 Coquelicot 先安装在对应 switch 中，再从代码根目录检查 rocq/AppendixA/CoquelicotSmoke.v；Windows 原生 RocqIDE 不能直接载入 Ubuntu 构建的库，反向也不应直接复用；文件即使可见，也应在目标环境重建。Lean 的mathlib 已由全书 lean/ 项目声明；独立的 CalculusBasics 则不因此自动获得数学库，见 [Mathlib 排查](mathlib-import-troubleshooting.md)。

参考：[RocqIDE 9.2](https://rocq-prover.org/doc/V9.2.0/refman/practical-tools/coqide.html)、[VsRocq](https://github.com/rocq-prover/vsrocq)。

本节的多文件构建与编辑器操作集中对应附录 A.11；A.8–A.10 是安装与单文件核验路线。

## 可选清理

在 code 根目录用 make cleanLean 清理 Lean 基础项目构建结果，make cleanRocq 清理 Rocq 基础项目产物，make clean 同时执行。保留源码、配置和工具链，不卸载数学库，也不是 Mathlib 缓存修复操作。日常不必先清理；清理后需重新构建依赖，再在界面检查。

清理范围：make cleanLean 执行 lake clean filterCalculus，只删除教材包的生成结果，保留 Mathlib 等依赖的构建缓存；不要把不带包名的 lake clean 当作等价替换。
