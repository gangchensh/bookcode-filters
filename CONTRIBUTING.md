# 参与改进

请先阅读README及对应章节入口。报告问题时给出操作系统、版本、执行目录、完整命令、第一条报错及最小可复现文件。

修改证明后运行 `make check-lean` 与 `make check-rocq`；只改一章时可先运行 `make chapter CHAPTER=03`。不要加入sorry、admit或Admitted作为完成的证明。需要新假设时，在陈述与说明中明确指出，不要以修改命题替代修复证明。

保留lean-toolchain、lakefile.toml、lake-manifest.json及Rocq项目清单。更新工具版本时，应连同依赖、全部章节和CI一起核验。编译生成文件、依赖缓存、个人编辑器配置及凭据不提交。

提交的原创修改按本仓库MIT许可证提供。请保留第三方来源及许可证信息。
