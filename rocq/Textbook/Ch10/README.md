# 第10章 积分方法、反常积分与工程量

All.v导入Textbook/Ch10/Methods.v。沿用本语言统一项目的依赖和版本配置。

从仓库根目录执行 `make chapter CHAPTER=10`；仅检查本语言可用 `make chapter-rocq CHAPTER=10`。

源码含换元/分部积分的库接口（Lean）、两种语言的多项式与指数有限积分、截断积分以及误差合并。两种语言均证明指数反常积分收敛；Rocq另给出教学反常谓词及Coquelicot关系型反常接口。正文一般比较、幂判据、模型推导等不宣称全部双语形式化。

评审修订补充：Rocq的 `improper_library_iff` 在每个有限截断可积的前提下，证明教学反常谓词与Coquelicot端点滤子接口等价。两种语言的 `total_error_budget` 统一以I、A、Q表示完整积分、有限截断和数值近似，先传截断界，再传求积界。一般Cauchy判据、极限比较和共同尾部下的极限交换目前为正文证明，未全部编码。
## 本章实际模块
- `Textbook.Ch10.Methods`
