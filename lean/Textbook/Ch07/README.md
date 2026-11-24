# 第7章 微分法则、中值定理与优化

`All.lean` 是按当前教材章号排列的可编译入口。完整证明位于它导入的文件，集中使用本语言的同一个项目配置。

- `Differentiation.lean` 和 `Statements.lean` 收录微分法则及基本定理。
- `SignTests.lean` 收录导数符号与单调性、极值判别和右侧洛必达。
- `Applications.lean` 和 `Certificates.lean` 收录例题、反例和工程模型的证明。

从仓库根目录运行 `make chapter CHAPTER=07` 同时检查两种语言；运行 `make chapter-lean CHAPTER=07` 只检查Lean。
