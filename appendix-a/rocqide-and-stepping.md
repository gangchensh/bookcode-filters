# RocqIDE 与 VsRocq 单步操作

## RocqIDE 界面

[官方手册与真实界面图](https://rocq-prover.org/doc/V9.2.0/refman/practical-tools/coqide.html)。截图保留旧标题 CoqIDE，各系统主题可能不同。

- 顶部菜单与工具栏：文件、编辑、执行与回退。
- 左侧：源码输入区，保存 .v 文件；已执行部分通常有背景色。
- 右上：证明目标与当前可使用的假设。
- 右下：Messages、Errors、Warnings、Jobs，显示反馈及后台检查信息。
- 底部：状态与处理进度。

## 分步例子

打开本目录的 `examples/AndDemo.v`。这是学习练习，不是安装要求。用 Navigation / Forward（Alt+Down）前进、Backward（Alt+Up）回退：

| 检查点 | 目标变化 |
| --- | --- |
| Example and_demo 声明 | 一个 True /\ True 目标 |
| Proof. | 进入证明，目标不变 |
| split. | 分为两个 True 子目标 |
| 第一条 - exact I. | 完成第一个 True |
| 第二条 - exact I. | 完成另一个 True |
| Qed. | 关闭并登记证明 |

True 是恒真命题，I 是它的标准证明；/\ 表示且，split 拆合取，exact 提交现成证明，- 是组织子目标的 bullet。bullet 可能需要单独处理，检查点不一定对应一次按键。回退撤销处理状态，不删除源码。

保存和完成检查是不同操作。异步模式可能还需 Fully check the document；项目最终用命令行构建核验。

## VsRocq

点击 .v 代码区，确认语言模式为 Rocq。合并仓库中的 `config/vsrocq-stepping.example.json` 所示设置。工具栏按钮在编辑区右上角，不在终端上方；窄窗口可能折叠进省略号菜单。

无需按钮也可用命令面板：Step Forward、Step Backward、Interpret to point、Interpret to end、Display Proof View。Alt+Down / Up / Right / End 分别对应前进、回退、运行到光标和末尾。与系统快捷键冲突时使用命令面板。

没有命令则检查扩展及其安装位置；有命令但目标不更新则检查语言服务器及日志。[VsRocq FAQ](https://github.com/rocq-prover/vsrocq/blob/main/docs/FAQ.md)。
