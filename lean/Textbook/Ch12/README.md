# 第12章 多元极限、全微分与雅可比

入口 `All.lean` 导入本章的滤子定义与应用，沿用统一项目。仓库根目录执行 `make chapter CHAPTER=12`；仅检查本语言可用 `make chapter-lean CHAPTER=12`。

Lean提供小o教学定义与HasFDerivAt对应、连续线性映射、二元乘积及余项、F(x,y)=(x²+y,xy)的微分、线性输出复合和连续性。Rocq提供最大范数教学定义（含线性条件）、直接乘积余项证明、Coquelicot原生filterdiff的线性及二元乘积例子，以及复合矩阵系数恒等式。

注意：Lean的实数对默认范数为最大范数；Coquelicot乘积范数不按定义等同于size2，源码使用norm_prod比较。连续偏导判据在实数对的最大范数下验证。


评审修订：Lean增加 `linear_combination`、`product_rule` 及 `sensor_remainder_estimate`，后者证明两个输入坐标绝对值不超过r时，内层模型两个分量的线性预测余项各不超过r²。Rocq增加 `scaled_product_native`（实际调用filterdiff_comp）和 `outer_square_expansion`（非线性组合的平方展开）。

原有Lean链式法则调用 `hg.comp a hf` 已在锁定版本通过检查。库源文件Composition节的 `variable (x)` 使点参数显式，阅读单条声明时不能忽略其上下文。

非线性组合模型的 54ρ² 余项界在教材中给出纸面证明。Rocq 对照覆盖选定的微分规则和例子。Lean 依赖的精确提交见 `lean/lake-manifest.json`。
## 本章实际模块
- `Textbook.Ch12.Multivariable`：距离判定、二元乘积与传感器模型。
- `Textbook.Ch12.Audit`：多元极限、偏导数、方向导数、全微分及沿集合全微分的滤子定义与传统判定。全微分同时与 Mathlib 的 `HasFDerivAt`、`HasFDerivWithinAt` 对照。
- `Textbook.Ch12.Applications`：闭有界集上的极值与一致连续、线性映射有界、微分运算、局部极值和多元中值不等式。

- `Textbook.Ch12.ContinuousPartials`：二维开集上的连续偏导判据。
- `Textbook.Ch12.PathCounterexamples`、`Textbook.Ch12.DirectionCounterexamples`：逐坐标连续性、沿直线极限及方向导数的反例。
- `Textbook.Ch12.Coordinates`、`Textbook.Ch12.GradientModels`、`Textbook.Ch12.PlaneModels`：坐标与范数、梯度与雅可比、极坐标和模型算例。
- `Textbook.Ch12.SensorBudget`：两输入模型的分量变化、组合输出误差及输入容差。

编号条目的源码位置及核对状态见 [对应表](../../../docs/textbook-item-map.json)。
