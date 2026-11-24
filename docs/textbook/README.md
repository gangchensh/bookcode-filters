# 《形式化微积分的滤子基础》代码导航

路径相对于下载的代码仓库顶层。本书只使用一个Lean项目根目录 `lean/` 和一个Rocq项目根目录 `rocq/`；数学源码和命名空间前缀按教材章号组织，可直接按下表定位。

| 教材章节 | 主要Lean文件 | 主要Rocq文件 |
| --- | --- | --- |
| 第1章 | `Textbook/Ch01/Language.lean` | `Textbook/Ch01/Language.v` |
| 第2章 最终成立、邻域、滤子 | `Textbook/Ch02/Eventually.lean`、`Tail.lean`；`Textbook/Ch02/Neighborhoods.lean`；`Textbook/Ch02/Filters.lean`、`Logic.lean` | 同名 `.v` 模块；倒数估计另见 `Textbook/Ch02/Reciprocal.v` |
| 第3章 趋近与各类极限 | `Textbook/Ch03/StandardFilters.lean`、`Approach.lean`；`Textbook/Ch03/LimitRules.lean`；`Textbook/Ch03/DefinitionExamples.lean` | 相应 `.v`；跨库关系见 `Textbook/Ch03/CoquelicotBridge.v` |
| 第4章 极限运算与连续性 | `Textbook/Ch04/LimitRules.lean`；`Textbook/Ch04/Continuity.lean`；`Textbook/Ch04/LocalLimits.lean` | `Textbook/Ch04/LimitRules.v`及局部极限模块 |
| 第5章 完备性 | `Textbook/Ch05/Sequences.lean`；`Textbook/Ch05/SqrtBounds.lean`；`Textbook/Ch05/Recursion.lean`；`ClosedIntervals.lean` | `Textbook/Ch05/Sequences.v` |
| 第6章 导数 | `Textbook/Ch06/Derivatives.lean` | `Textbook/Ch06/Derivatives.v` |
| 第7章 微分法则与优化 | `Textbook/Ch07/Differentiation.lean` | `Textbook/Ch07/Differentiation.v` |
| 第8章 泰勒近似 | `Textbook/Ch08/Taylor.lean` | `Textbook/Ch08/Taylor.v` |
| 第9章 积分 | `Textbook/Ch09/Integration.lean` | `Textbook/Ch09/Integration.v`（需要Coquelicot） |
| 第10章 积分方法与反常积分 | `Textbook/Ch10/Methods.lean` | `Textbook/Ch10/Methods.v`（需要Coquelicot） |
| 第11章 级数与函数近似 | `Textbook/Ch11/Series.lean` | `Textbook/Ch11/Series.v`（需要Coquelicot） |
| 第12章 多元极限与全微分 | `Textbook/Ch12/Audit.lean`、`Textbook/Ch12/Multivariable.lean`、`Textbook/Ch12/Applications.lean` | `Textbook/Ch12/Multivariable.v`（需要Coquelicot） |
| 第13章 多重与工程积分 | `Textbook/Ch13/All.lean`（[模块说明](../../lean/Textbook/Ch13/README.md)） | `Textbook/Ch13/MultipleIntegrals.v`（需要Coquelicot） |

上表省略了每种语言的根目录前缀。书稿和教材PDF不放在本代码仓库内。

## 当前章号入口

两种语言都提供 `Textbook/Ch01/All` 至 `Textbook/Ch13/All`。从仓库根目录执行 `make chapter CHAPTER=03` 检查一章，`make check` 检查全部。实现模块保留下表路径，不复制第二套定义。

## 检查

在已按 `appendix-a/` 安装Lean 4.35.0、对应Mathlib和Rocq 9.2的环境中，从仓库顶层执行：

```bash
make check-lean
# 已安装相容的Coquelicot后检查完整Rocq章节
make check-rocq
# 仅检查第13章
make chapter CHAPTER=13
```

完整检查按依赖顺序构建；Rocq基础模块重新编译后，需要连同依赖它们的模块一起重建，避免旧 `.vo` 文件的依赖指纹不一致。日常编辑可单独检查文件，但应先完成项目准备和依赖构建。Lean `lake env lean` 成功时可能没有输出；Lake构建会显示进度和成功消息。首次载入较大数学库可能需要数分钟，导入风格警告与证明错误应区分。

在Lean根目录检查第6章的示例：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake env lean Textbook/Ch06/Derivatives.lean
```

确认当前终端的Lean和Lake均由Elan选择项目版本后，可简写为 `lake env lean Textbook/Ch06/Derivatives.lean`。VS Code也应打开项目根目录并使用该项目的工具链。

## 正文摘录与选读

`snippets/`及`rules/`从完整源文件提取供教材排版使用。摘录不一定含全部导入及上下文；运行优先打开原始 `.lean` 或 `.v` 文件。

完整集合记号例子在 `Textbook/Ch02/Sets`；滤子基与积构造在 `Textbook/Ch03/Maps`。这些材料可以回查，不作为本书进入导数之前必须逐一录入的练习。

摘录用于正文阅读，实际编译请使用完整源码。

新增案例中，第4章的有理函数极限位于`Continuity.lean`；第5章`Recursion.lean`验证平方根迭代的一步恒等式与单调估计；第6章文件包含仿射、倒数、余项界及Rocq标准导数桥接。代码未覆盖的数学推导仍须按正文审读，不能以其他定理检查成功代替其核验。

第7—9章分别提供乘积/复合求导、中值定理与优化证书、渐近关系与显式余项、积分及基本定理示例。Rocq完整教材构建需要Coquelicot，使用 `make check-rocq` 或默认构建前应按依赖文件准备环境。一般Taylor定理等完整纸面证明并未全部另写Rocq版本，书中注明了实际形式化范围。

其他已验证示例：第7章包含平方复合、扰动代价和容器优化证书；第8章包含Lagrange余项到共同上界、三次余项缩放，以及Rocq的小o教学定义；第9章包含通用网格滤子/非平凡性与一次函数积分证书。通用网格滤子尚未编码所有具体分割合法性条件，不能把它等同于完整Riemann积分理论的形式化。

第11章特别区分默认HasSum的无条件求和与显式conditional求和滤子，提供自然顺序桥接；Coquelicot的sum_n含最后一项，具体换算见Series.v。Fourier一般理论未全部在本仓库另行形式化。

第12章用二元实向量给出原生全微分、线性映射、二元模型和链式法则；Rocq包含教学余项及Coquelicot原生线性/乘积例子。先核对输入输出类型、默认范数及定义域，再比较矩阵系数。完整形式化范围见各语言Textbook/Ch12/README.md。

第7章增加直接使用共同源极限规则的product_rule_direct，与库乘积求导对照。第13章区分整体积分、迭代积分与参数积分，提供原生Fubini、极坐标区域换元、Gauss积分及代表性工程计算；具体覆盖见Textbook/Ch13/README.md。


## 全书覆盖与查阅

第1—13章的26个逐章入口均已提供。具体实现、尚未双语形式化的范围见[代码覆盖表](../textbook-coverage.md)，可搜索名称见[声明清单](../textbook-symbols.tsv)。本书简明附录的命令见[命令文本](../../appendix-a/textbook-quickstart.txt)；原完整在线指南保留自己的A.1—A.19编号，不与新纸书小节号混用。

第9章评审修订补充HasMeshIntegral抽象定义与量词等价、两种语言的相邻区间接口及原生Riemann定义展开。完整分割数据的实现不包含在这个抽象接口中。

第10章补充局部可积性前提下的Coquelicot反常积分接口对应证明；误差预算的I、A、Q分别表示完整积分、有限截断和数值近似。一般反常收敛判据及极限交换仍以正文证明为准。

第11章补充双语自然顺序求和桥接，以及Lean一致收敛量词、误差上界与积滤子接口；一般幂级数与Fourier理论仍以正文证明和明确引用的经典结论为准。

第12章补充微分运算与内层模型的有限余项证书，并增加Rocq原生复合和非线性外层平方展开。54ρ²完整外层界、一般C1判据与完整库间等价仍为纸面证明，详见覆盖表。
