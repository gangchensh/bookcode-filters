# 第9章 积分、累积量与微积分基本定理

`All.v` 是按当前教材章号排列的可编译入口。完整证明位于它导入的文件，集中使用本语言的同一个项目配置。

- `Textbook/Ch09/Integration.v`

从仓库根目录运行 `make chapter CHAPTER=09` 同时检查两种语言；运行 `make chapter-rocq CHAPTER=09` 只检查Rocq。第9章Rocq需要Coquelicot。

本章新增：Lean的HasMeshIntegral与网格量词等价、积分三角不等式和相邻区间拼接；Rocq的riemann_filter_iff展开Coquelicot的原生积分定义，并提供相邻区间拼接。一般合法带标记分割构造、上下和判定及一般库间桥接仍以纸面证明为主，未宣称全部双语形式化。
## 本章实际模块
- `Textbook.Ch09.Integration`
