# 第10章 积分方法、反常积分与工程量

- `Methods.lean` 收录换元、分部积分、右侧反常积分及指数截断的基础证明。
- `Audit.lean` 收录其他端点的滤子与量词判定、带标记积分对应、反常积分的 Cauchy 判据和若干计算。
- `PowerCriteria.lean` 和 `PowerBudgets.lean` 收录两个端点的幂判据、发散到正无穷的证明及截断误差估计。
- `Comparison.lean` 收录有限起点的调整、非负积分的比较判据与极限比较判据。
- `LimitExchange.lean` 收录绝对收敛的尾界，以及固定区间和共同尾界下的极限交换。
- `ImproperParts.lean` 收录反常积分的分部积分公式。`CutoffExamples.lean` 与 `PrincipalValue.lean` 收录截断路径和主值的反例。
- `FiniteExamples.lean`、`RootExamples.lean`、`EngineeringExamples.lean` 与 `ExponentialModels.lean` 收录有限区间、根式奇点、质心及指数模型的计算。
- `ImproperSubstitution.lean` 验证递增换元所用的截断滤子等式。`EndpointExamples.lean` 验证倒数换元和双端根式积分。
- `Counterexamples.lean` 验证独立端点、分部积分的发散项和移动尖峰。`DampedOscillation.lean` 验证有限截断公式和两个无穷积分。
- `RationalExamples.lean` 与 `SingularDensity.lean` 验证部分分式、端点比较以及奇异密度的质量和一阶矩。
- `All.lean` 是整章入口。

在源码仓库根目录运行 `make chapter-lean CHAPTER=10` 检查 Lean。逐条核验状态见 `docs/textbook-item-map.json`。
