# 仓库目录与模块约定

仓库根目录只有代码、安装材料和读者说明，不包含教材TeX、PDF或作者讨论稿。

| 目录 | 用途 |
| --- | --- |
| lean/Textbook/Ch01—Ch13/ | Lean各章的完整定义、证明与例子；All.lean聚合本章模块 |
| rocq/Textbook/Ch01—Ch13/ | Rocq各章的定义与代表性证明；All.v聚合本章模块 |
| 各语言的 Textbook/IntroductionExamples | 引言中命题含义、完整邻域与去心极限的例子 |
| 各语言的 Theories/ | 附录使用的公共小例子 |
| 各语言的 AppendixA/、templates/、examples/ | 安装检查、独立配置模板和多文件练习 |
| appendix-a/、config/ | 安装命令、脚本、截图和环境配置样例 |
| docs/textbook/ | 十三章导航和从源码同步的阅读摘录 |
| scripts/ | 声明索引与源码打包工具 |

章号与教材一致。Lean命名空间以Ch01—Ch13为前缀，例如Ch02、Ch03Approach、Ch03Rules、Ch05Recursion；后缀说明同章不同模块的用途。Rocq导入以物理模块Textbook.ChNN.File为准，文件内的Module同样采用对应章号前缀。两个系统的命名与参数语法不同，不把简单同名当作定理自动等价。

Lean项目根目录是lean/，共享lean-toolchain、lakefile.toml和lake-manifest.json。Rocq项目根目录是rocq/，共享_CoqProjectTextbook及_CoqProject。使用make check检查教材，make all检查默认项目；完整Rocq环境包含Coquelicot。

目录或导入改变后应重新构建。旧布局到新布局的机械迁移记录保存在chapter-migration.json，只用于核对历史引用；读者不必使用旧路径。
