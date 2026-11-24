# 第13章 多重积分与工程积分入门

入口 `All.lean` 导入本章的网格定义、原生库接口与计算实例。仓库根目录运行 `make chapter CHAPTER=13`，只检查本语言可用 `make chapter-lean CHAPTER=13`。

Lean：原生Fubini与换序接口、矩形可积性及乘积积分、三角形质量和两个一阶矩、质心归一化、极坐标行列式、原生极坐标区域换元及圆盘限制、Gauss积分的可积性与积分值、圆周功、平面叉积和面积/通量的参数积分。
Rocq：保留内层存在性的IsIterated接口、矩形乘积积分、三角形质量、行列式、圆盘面积、圆周功和平面通量；使用Rocq 9.2与Coquelicot 3.4.5。

几何参数化、原生区域积分、迭代积分和数值结果是不同层次。一般Riemann可积性理论、任意曲面和全部库间桥接未完成双语形式化。面积与体积无定向符号，功与通量需要核对方向。

`integral_affine` 是Rocq实现文件中先行证明的本书辅助引理，不是Coquelicot的库名称。Lean的 `polar_region_change` 使用Mathlib原生区域积分；`disk_region_polar` 进一步把圆盘限制转换为半径条件。参数积分的数值计算与这些区域换元是不同的核验步骤。
## 本章实际模块
- `Textbook.Ch13.MultipleIntegrals`：迭代积分、薄片、圆盘、Gauss 积分和功的计算。
- `Textbook.Ch13.Audit`：矩形和长方体的带标记网格、网格与滤子的等价判定、Fubini、Tonelli、原生换元以及折线长度的网格判定。
- `Textbook.Ch13.Applications`：质量、质心、惯性矩、曲线与曲面积分的参数表达和具体算例。

- `Textbook.Ch13.Bridges`：单段连续速度的弧长公式、上下界夹逼、非负积分的递增穷尽。
- `Textbook.Ch13.Darboux`：从可测上下阶梯界推导几乎处处可测、可积和积分值相等。
- `Textbook.Ch13.Surface`：复合微分的叉积缩放、定向符号及标量曲面积分的参数变换。
- `Textbook.Ch13.Examples`：反射对称、线性变换行列式和切片边界。

- `Textbook.Ch13.Grid`：半开网格的覆盖、唯一归属、阶梯函数与积分。
- `Textbook.Ch13.GridGap`：以两套合法标记逼近上下确界，从网格判定推出上下阶梯积分之差任意小。
- `Textbook.Ch13.GridAgreement`：矩形带标记积分与乘积 Lebesgue 积分的对应，并推广到可测区域的补零定义。
- `Textbook.Ch13.Refinement`：单段弦长上界、有序细分和全网格插点误差。

- `Textbook.Ch13.ContinuousGrid`：闭矩形上连续函数的带标记 Riemann 可积性及两种迭代积分。
- `Textbook.Ch13.Breakpoints`：从实际断点构造有序细分，控制折线长度改变量，并在给定各段极限时合并。
- `Textbook.Ch13.PieceGrid`：逐段标记分割、网格趋零、细分折线和重组及分片 C¹ 弧长公式。

- `Textbook.Ch13.Slices`：从每个切片的带标记积分推出两种外层积分。
- `Textbook.Ch13.IntegralRules`：矩形与区域积分的线性、保序、绝对值界和区域积分中值。
- `Textbook.Ch13.NullBoundary`：零面积闭集外连续的有界函数可积，零面积扰动不变性，以及零面积重叠时的区域可加性。

- `Textbook.Ch13.SimpleRegions`：简单区域补零的带标记可积性、各切片的带标记积分及三种换序算例。

- `Textbook.Ch13.SwapFailure`：非零切片可积、两种迭代积分值、零坐标切片与整体非绝对可积。

- `Textbook.Ch13.Tetrahedron`：单位四面体的三重积分限、体积、三个坐标矩及质心。
- `Textbook.Ch13.DoubleCover`：平方坐标映射的像集、原像个数、单射限制、雅可比及两种参数面积。

- `Textbook.Ch13.PolarApplications` 给出闭圆盘的极坐标积分，`RadialExamples` 核对圆柱的质量与惯性矩以及径向高斯的总量与尾部。`RoundVolumes` 用球体体积定理和球坐标迭代积分分别计算球体体积。
- `Textbook.Ch13.LaminaEstimates` 核对平行轴定理，`TriangleError` 将薄片密度误差传递到质量、一阶矩及质心。
- `Textbook.Ch13.CurveGeometry` 给出速度的定义和分片梯度场功公式，`Helix` 核对圆螺线速度及弧长。
- `Textbook.Ch13.SurfaceGeometry` 给出曲面的规则性、面积因子和圆柱侧面通量，`Paraboloid` 核对抛物面的面积和向上通量。

见 [编号条目对应表](../../../docs/textbook-item-map.json)。
