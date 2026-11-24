# 第12章 多元极限、全微分与雅可比

入口 `All.v` 导入 `Textbook/Ch12/Multivariable.v`，沿用统一项目。仓库根目录执行 `make chapter CHAPTER=12`；仅检查本语言可用 `make chapter-rocq CHAPTER=12`。

Lean提供小o教学定义与HasFDerivAt对应、连续线性映射、二元乘积及余项、F(x,y)=(x²+y,xy)的微分、线性输出复合和连续性。Rocq提供最大范数教学定义（含线性条件）、直接乘积余项证明、Coquelicot原生filterdiff的线性及二元乘积例子，以及复合矩阵系数恒等式。

注意：Lean的实数对默认范数为最大范数；Coquelicot乘积范数不按定义等同于size2，源码使用norm_prod比较。一般C1判据、完整库间等价、所有反例和非线性外层误差证书未宣称全部编码；详见教材。


评审修订：Lean增加 `linear_combination`、`product_rule` 及 `sensor_remainder_estimate`，后者证明两个输入坐标绝对值不超过r时，内层模型两个分量的线性预测余项各不超过r²。Rocq增加 `scaled_product_native`（实际调用filterdiff_comp）和 `outer_square_expansion`（非线性组合的平方展开）。

原有Lean链式法则调用 `hg.comp a hf` 已在锁定版本通过检查。库源文件Composition节的 `variable (x)` 使点参数显式，阅读单条声明时不能忽略其上下文。

一般C1判据、完整教学/原生Rocq微分等价，以及非线性外层54ρ²完整界仍以纸面证明为准；平方展开的检查不等于完整误差界的检查。Lean依赖精确提交见仓库根下 `lean/lake-manifest.json`。
## 本章实际模块
- `Textbook.Ch12.Multivariable`
