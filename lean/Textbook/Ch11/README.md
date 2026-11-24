# 第11章 级数、幂级数与函数近似

入口 `All.lean` 汇集本章的 Lean 模块。源码仓库根目录运行 `make chapter CHAPTER=11`，仅检查 Lean 时运行 `make chapter-lean CHAPTER=11`。

源码定义前N项部分和并提供几何和、余项等例子。Lean另提供自然顺序级数与Mathlib conditional求和滤子的等价、必要条件、Cauchy接口、一致几何上界和指数级数；Rocq提供sum_n的下标对应及Coquelicot级数/幂级数接口。

本章不会把默认HasSum（无条件求和）与条件收敛级数混同。Fourier和一般幂级数理论以教材证明与阅读案例为主，不宣称已全部双语形式化。


评审修订增加Lean的 `uniform_on_iff`、`uniform_of_error_bound` 与 `uniform_product_iff`，把一致收敛量词、统一误差界和积滤子接到Mathlib原生接口。Rocq的 `ordered_coquelicot_iff` 正式证明教学部分和收敛与 `is_series` 等价；`sum_n` 包含最后一项，移位不会改变项序。

所有 BEGIN/END 片段均从源码提取。逐条声明与正文的对应见 `docs/textbook-item-map.json`。Lean 依赖提交见 `lean/lake-manifest.json`，工具链见 `lean/lean-toolchain`。

## 本章实际模块

- `Series.lean` 与 `Audit.lean` 定义自然顺序求和，连接库接口，并给出基础收敛判据。
- `IntegralTest.lean` 连接带标记可积性、反常积分、非负级数和尾部界。
- `Radius.lean`、`RadiusExamples.lean`、`PowerOperations.lean` 与 `TaylorBridge.lean` 涵盖半径、内部运算和 Taylor 系数。
- `UniformDerivatives.lean` 与 `UniformExamples.lean` 涵盖导数一致收敛、反复出现的函数列及振荡信号算例。
- `SeriesExamples.lean`、`Rearrangement.lean`、`EndpointAndPrecision.lean` 和其他近似模块给出重排、Abel 端点及严格误差证书。
- `FourierExamples.lean` 给出方波的积分系数和有限谐波重建。`Bessel.lean` 核对有限频率的 Bessel 不等式。正文引用的 Dirichlet 收敛定理仍作为背景知识。
