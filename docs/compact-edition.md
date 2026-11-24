# 《AI时代的形式化微积分——从滤子到微积分基本定理》代码导航

这是八章精简版的阅读与构建说明。下载或克隆后，以包含 `lean/`、`rocq/` 和 `Makefile` 的目录作为仓库根目录；不必再创建 `A/code` 子目录。

仓库保留完整证明及依赖，`Textbook/Ch01` 至 `Ch13` 沿用原十三章版本的模块编号。模块编号、声明命名空间与本版章号不是一回事。不要为了对应八章目录而重命名或删除模块。

| 本版章节 | 内容 | 源码模块（Lean 与 Rocq 相同） |
| --- | --- | --- |
| 第1—4章 | 语言、滤子、趋近关系、极限运算与连续性 | `Textbook/Ch01`—`Ch04` |
| 第5章 | 实数完备性 | `Textbook/Ch05` |
| 第6章 | 导数与微分法则 | `Textbook/Ch06` 和 `Ch07` |
| 第7章 | 渐近近似 | `Textbook/Ch08` |
| 第8章 | 积分与微积分基本定理 | `Textbook/Ch09` |

Lean入口是 `lean/Textbook/ChXX/All.lean`，Rocq入口是 `rocq/Textbook/ChXX/All.v`。各章末集中列出代码文件；入口用于汇集依赖。逐项对应见 [本版源码位置表](compact-source-locations.tsv)，保留教材标签与原声明位置，行号仅供辅助查找，以声明名称为准。

## 首次准备

依照[仓库README](../README.md)和[附录A指南](../appendix-a/README.md)安装锁定版本与依赖。版本仍为Lean 4.35.0、Mathlib v4.35.0、Rocq及标准库9.2.0、Coquelicot 3.4.5；OCaml为4.14.1。精确依赖以仓库配置为准。已有项目无需再次执行 `lake new`，日常检查无需反复下载缓存。

## 日常按章检查

在仓库根目录、已激活相容Rocq switch的Ubuntu终端执行：

```bash
# 本版第5章
make chapter CHAPTER=05
# 本版第6章：两组模块都要检查
make chapter CHAPTER=06
make chapter CHAPTER=07
# 本版第7章
make chapter CHAPTER=08
# 本版第8章
make chapter CHAPTER=09
```

第1—4章分别使用 `CHAPTER=01`—`04`。`make chapter` 同时构建两种语言；只检查一种时改用 `make chapter-lean` 或 `make chapter-rocq`，保留同一 `CHAPTER` 参数。

`make check-lean`、`make check-rocq` 检查完整仓库，范围大于精简版。构建某个入口也会构建其依赖：例如一维Riemann积分与Mathlib积分的桥接复用了 `Textbook/Ch13` 中的矩形阶梯界证明。它是技术依赖，不要求读者先学多重积分，也不能从发布源码中删除。

## 在编辑器中查阅

例如查阅本版第8章，先在仓库根目录执行 `make chapter CHAPTER=09`。随后从 `lean/` 打开VS Code，Lean文件可导入：

```lean
import Textbook.Ch09.All
```

Rocq项目使用 `rocq/` 为工作目录，由 `_CoqProjectTextbook` 中的 `-Q Textbook Textbook` 指定逻辑路径；可写：

```coq
From Textbook.Ch09 Require Import All.
```

编辑器必须使用与构建相同的工具链和逻辑路径，详见[编辑器与依赖](../appendix-a/editor-dependencies.md)。不要把源码位置的 `Ch09` 改成精简版章号 `Ch08`。

## 查找定义与定理

- 第2章2.6节的交错应用例子见 `lean/Textbook/Ch02/LimitApplications.lean`。`shifted_small`、`sum_small`、`square_small`、`changed_small`分别使用最终单调性、合取、分离和性质替换，证明对每个正 `ε` 都有相应的最终距离界；第三章将这一判定与滤子极限联系起来。它已由 `Textbook.Ch02.All` 导入，可用 `make chapter-lean CHAPTER=02` 构建。这里没有调用后续章节的和、乘积极限定理。
- [声明清单](textbook-symbols.tsv)和[覆盖说明](textbook-coverage.md)中的章号按原十三章版本编排，先用上表映射。
- 第5章重点查 `Ch05/Sequences.lean`、`ClosedIntervals.lean`；第6章查 `Ch06/Derivatives.lean` 与 `Ch07/Differentiation.lean`、`SignTests.lean`。
- 第7章查 `Ch08/Taylor.lean`、`Audit.lean`；第8章查 `Ch09/Integration.lean`、`Tagged.lean`、`DarbouxCriterion.lean`、`Accumulation.lean`、`MeasureBridge.lean`。
- Rocq对照文件主要为各模块中的 `Sequences.v`、`Derivatives.v`、`Differentiation.v`、`Taylor.v`、`Integration.v`。不是每一个Lean定理都有同名Rocq证明。
- 在线附录保留的A.1—A.19资料编号与精简版纸书附录小节号不同。按文件名查阅，不要按节号直接套用。

## 第6—8章穿插例子的源码

以下路径相对于仓库根目录；声明位于相应的 `Ch07`、`Ch08`、`Ch09` 命名空间。

| 本版章节 | Lean 文件 | 声明及用途 |
| --- | --- | --- |
| 第6章 | `lean/Textbook/Ch07/Statements.lean` | `linear_example`（仿射函数求导）、`mean_value_square`（平方函数的中值定理） |
| 第6章 | `lean/Textbook/Ch07/Applications.lean` | `area_product`（面积变化率） |
| 第7章 | `lean/Textbook/Ch08/Audit.lean` | `power_order`、`cubic_expansion`、`exp_rational_certificate`、`exp_second_limit`（高阶界、展开、误差证书及极限） |
| 第8章 | `lean/Textbook/Ch09/Examples.lean` | `linear_accumulation`、`variable_upper_endpoint`、`moving_square_interval`（累积积分及端点变化） |

第8章的 `HasMeshIntegral`、`HasTaggedIntegral` 与 `tagged_integral_iff` 在 `lean/Textbook/Ch09/Integration.lean` 中，分别给出抽象网格积分、具体带标记分割上的积分及其传统判定。Rocq 对照见 `rocq/Textbook/Ch09/Integration.v` 的 `riemann_filter_iff`。正文只节选部分证明，完整假设和结论以相应声明为准。
