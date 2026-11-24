# 第11章 级数、幂级数与函数近似

入口All.v导入Textbook/Ch11/Series.v，沿用统一项目。根目录运行 `make chapter CHAPTER=11`，仅本语言运行 `make chapter-rocq CHAPTER=11`。

源码定义前N项部分和并提供几何和、余项等例子。Lean另提供自然顺序级数与Mathlib conditional求和滤子的等价、必要条件、Cauchy接口、一致几何上界和指数级数；Rocq提供sum_n的下标对应及Coquelicot级数/幂级数接口。

本章不会把默认HasSum（无条件求和）与条件收敛级数混同。Fourier和一般幂级数理论以教材证明与阅读案例为主，不宣称已全部双语形式化。


评审修订增加Lean的 `uniform_on_iff`、`uniform_of_error_bound` 与 `uniform_product_iff`，把一致收敛量词、统一误差界和积滤子接到Mathlib原生接口。Rocq的 `ordered_coquelicot_iff` 正式证明教学部分和收敛与 `is_series` 等价；`sum_n` 包含最后一项，移位不会改变项序。

所有BEGIN/END片段都来自可编译源码。一般重排不变性、Cauchy乘积、Abel端点定理、半径理论与Bessel结论目前采用教材的纸面证明，不宣称均已双语形式化。Lean精确依赖提交见 `lean/lake-manifest.json`（从仓库根目录起），工具链见 `lean/lean-toolchain`。
## 本章实际模块
- `Textbook.Ch11.Series`
