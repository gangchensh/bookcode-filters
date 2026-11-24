# 第8章 泰勒公式、渐近关系与误差界

`All.v` 是按当前教材章号排列的可编译入口。完整证明位于它导入的文件，集中使用本语言的同一个项目配置。

- `Textbook/Ch08/Taylor.v`

从仓库根目录运行 `make chapter CHAPTER=08` 同时检查两种语言；运行 `make chapter-rocq CHAPTER=08` 只检查Rocq。第9章Rocq需要Coquelicot。

实际覆盖：小o/大O教学定义；Lean还提供与Mathlib等价、小量加法、代入、乘积规则、Lagrange余项及上界；两种语言都有倒数恒等式与多项式/三次尺度估计。一般泰勒定理没有另写Rocq版本，不把全部纸面例题视作已经双语形式化。
## 本章实际模块
- `Textbook.Ch08.Taylor`
