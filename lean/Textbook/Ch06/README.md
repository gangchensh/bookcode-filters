# 第6章 导数与局部线性化

从仓库根目录运行 `make chapter-lean CHAPTER=06` 检查 Lean 入口 `Textbook/Ch06/All.lean`。运行 `make chapter CHAPTER=06` 同时检查本章的 Lean 与 Rocq 入口。

- `Derivatives.lean` 定义普通导数、左右导数和沿集合的导数，并证明传统判定。
- `Statements.lean` 给出增量形式、小量、线性余项与切线模型。
- `Estimates.lean` 验证余项距离界、局部增量界及工程模型的推导。
- `Examples.lean` 包括数列判定、相对输入趋零的扰动与对称差商。
- `Counterexamples.lean` 和 `Piecewise.lean` 包括绝对值、零点倒数、平方根、分段接合及导函数振荡等例子。

在 Lean 文件中导入 `Textbook.Ch06.Derivatives` 后，可用 `#print axioms Ch06.derivative_right_epsilon_iff` 等命令核对等价引理的公理依赖。其他距离判定为 `derivative_epsilon_iff`、`derivative_left_epsilon_iff` 和 `derivative_along_distance_iff`。
