# Lake 简写与显式工具链选择

对应附录 A.8“日常检查”，版本原理见 A.12，排错见 A.16。

`elan run "$project_toolchain"` 为这次调用选择工具链；后面的 Lake 命令决定执行什么工作。直接 `lake` 已使用项目要求的工具链时，可以省去前缀。正常 elan 代理会按项目的 lean-toolchain 自动选择，日常不必反复赋值。

## 首次核对，之后按需使用

在当前 Lean 项目根目录（含 lean-toolchain 和 lakefile 的目录）执行，不限于 CalculusLean：

```bash
cat lean-toolchain
lean --version
lake --version
```

例如，项目要求4.35.0时，后两条显示的 Lean 版本也应为4.35.0。重点看 `lake --version` 中的 Lean 版本，而不是只看 Lake 自己的版本号。路径查询不能单独证明版本正确；同版自编译工具链也未必兼容发行版缓存，应使用项目指定的发行工具链。

| 情况 | 使用方式 |
| --- | --- |
| 正常 elan 代理选对项目工具链 | 使用 lake 简写；换项目时由代理选择 |
| 直接调用固定版本，已核实与当前项目相容 | 当前项目可简写；换项目或修改 PATH 后重新核对 |
| 直接 lake 版本不符或选择不明，可能有环境变量、目录覆盖或 alias 影响 | 暂用显式 elan run，并排查入口和覆盖 |
| 脚本、自动化、排错希望明确记录所用版本 | 可保留显式写法或用 check-lean.sh |

项目需要的版本与实际工具版本一致、工具链相容时，在项目根目录按任务选择：

```bash
lake env lean MathlibSmoke.lean
lake build
```

第一条检查保存的独立练习，默认不为它写出 .olean；第二条构建配置目标，不自动检查所有独立文件。

首次准备、更新依赖或需要补齐缓存时，才按需执行：

```bash
lake exe cache get
```

项目须已经配置 mathlib 并有 cache 程序。不是每次打开文件都要运行，也不能代替证明检查。

## 显式选择的写法

在当前项目根目录逐行输入：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake exe cache get
elan run "$project_toolchain" lake build
```

这是需要准备缓存、构建目标时的一组例子，不是日常必做流程。赋值与 elan run 必须分行，不能粘成 `lean-toolchain)elan run`。新终端或切换项目后重新赋值，不沿用另一项目的变量。

两种写法在工具链、目录、参数相同的条件下执行相同工作。长写法不会自动加速、修复缓存或切换已运行的编辑器服务器。无需一定使用这一段长命令；关键是保证使用正确的工具链和依赖环境。正常环境用简写，需要显式控制时可用长写法或 [check-lean.sh](scripts/check-lean.sh)。

参考：[elan 工具链选择](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/)、[Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)。

## 如果两者不一致

优先保持项目：可临时用 elan run 选版，或在当前终端安装并选择所需工具，使简写可用。只有主动升级时才修改项目要求，必须同时处理 mathlib 等依赖；修改项目自身的 version 字段不能切换 Lean。三种办法的具体操作见 [版本处理步骤](lean-version-actions.md)（正文 A.12）。
