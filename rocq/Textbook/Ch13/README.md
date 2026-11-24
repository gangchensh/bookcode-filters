# 第13章 多重积分与工程积分入门

入口 `All.v` 导入 `Textbook/Ch13/MultipleIntegrals.v`。仓库根目录运行 `make chapter CHAPTER=13`，只检查本语言可用 `make chapter-rocq CHAPTER=13`。

Lean：原生Fubini与换序接口、矩形可积性及乘积积分、三角形质量和两个一阶矩、质心归一化、极坐标行列式、原生极坐标区域换元及圆盘限制、Gauss积分的可积性与积分值、圆周功、平面叉积和面积/通量的参数积分。
Rocq：保留内层存在性的IsIterated接口、矩形乘积积分、三角形质量、行列式、圆盘面积、圆周功和平面通量；使用Rocq 9.2与Coquelicot 3.4.5。

几何参数化、原生区域积分、迭代积分和数值结果是不同层次。一般Riemann可积性理论、任意曲面和全部库间桥接未完成双语形式化。面积与体积无定向符号，功与通量需要核对方向。

`integral_affine` 是Rocq实现文件中先行证明的本书辅助引理，不是Coquelicot的库名称。Lean的 `polar_region_change` 使用Mathlib原生区域积分；`disk_region_polar` 进一步把圆盘限制转换为半径条件。参数积分的数值计算与这些区域换元是不同的核验步骤。
## 本章实际模块
- `Textbook.Ch13.MultipleIntegrals`
