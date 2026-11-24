# 第9章 积分、累积量与微积分基本定理

- `Integration.lean` 给出带标记分割、细分滤子和积分的网格判定，以及 Mathlib 区间积分的基本示例。
- `Tagged.lean` 构造任意细的带标记分割，证明 Cauchy 判据、连续函数的积分桥接，以及正向区间上的 Newton–Leibniz 公式。累积函数的导数证明单独列出它所依赖的短区间增量关系。
- `MeasureBridge.lean` 从任意标记的收敛推出有界性，并将一维和写成矩形各行标记和的加权平均，复用第13章的可测阶梯界。结论包含 Mathlib 区间可积性及积分值相等。
- `FiniteChange.lean` 控制一个点能够成为标记的小段数，进而证明有限点修改不改变积分。`Monotone.lean` 用网格乘总变差估计单调函数的标记和。
- `Darboux.lean` 定义上下和。`DarbouxCriterion.lean` 证明三个可积条件等价、上下确界给出积分值，以及相邻区间的可积性和积分值相加。
- `All.lean` 是整章入口。

从源码仓库根目录运行 `make chapter-lean CHAPTER=09` 检查 Lean。
