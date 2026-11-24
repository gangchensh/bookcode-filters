# Mathlib 使用与分类排查

本说明对应附录 A.16。安装与首次项目准备见 A.8，版本选择原理见 A.12；排错命令只在相应现象出现时使用，不是每次运行前的步骤。

排查原则：先保存并记录最早的完整错误，分清下载、构建、载入、版本与证明步骤。先查目录、版本、日志，再做对应修复；不要以删除 .lake、反复 lake update 或升级工具链代替定位。同一项目的恢复、清理、构建串行执行；强制解包仍须满足后文条件。

## 日常流程

在声明了 mathlib 的项目根目录，保存文件后执行：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake env lean MathlibSmoke.lean
```

编辑器打开该项目，WSL 用户确认 WSL: Ubuntu。正常使用无需反复 new、get 或 unpack!。已核实直接 lake 选对工具链时，可省去 elan run 前缀；适用条件见 [两种命令写法](lake-command-forms.md)。交付前按项目要求构建目标，独立练习文件仍应明确检查。

## 按现象选择检查顺序

| 现象 | 优先检查 |
| --- | --- |
| 没报错但等待较长 | 下载、构建还是库载入；文件系统与进程活动 |
| 终端与编辑器结果不同 | 实际程序路径、版本、项目根目录、WSL位置 |
| invalid toolchain name | 标识拼写、CRLF隐藏字符、BOM |
| unknown module prefix Mathlib | 项目是否声明依赖、文件是否属于正确项目 |
| incompatible header | 读取者与模块版本、依赖提交是否相容 |
| Imports are out of date | 保存后Restart File，失败再看具体依赖错误 |
| object file does not exist | 实际产物、构建范围、本地缓存是否完整 |

## 载入耗时

预编译缓存避免从源码重建，但不免除import Mathlib的载入和语言服务器启动。冷文件缓存、其他大型任务、首次依赖准备以及/mnt/d跨文件系统访问大量文件，均可能增加耗时。可在Ubuntu主目录建立独立副本比较，不在构建时搬动项目。按需缩小import范围后重新检查；本书滤子例子的具体导入和完整源码见 [按需导入说明](lean-infoview.md)。check-lean.sh 也需要等待同样的库载入过程，开始时会显示所用文件与版本，暂时安静不等于失败。

## 程序、版本与换行

查看[版本与配置](../docs/versions-and-config.md)，比较lean-toolchain、直接lean/lake、显式elan run，以及编辑器日志中的实际路径。stable是通道，不是固定版本保证。集成终端的环境不会反向修改已启动扩展。

不同项目可以使用不同版本。兼容换行的变量赋值仅移除CR/LF，不是安装、升级或修复所有文本错误。修改工具链版本时应同时核对mathlib、其他依赖、清单、编译缓存与编辑器固定路径；先保存工作，在独立分支或副本中验证。

## 项目与依赖

MathlibSmoke.lean应与其所属项目的lean-toolchain和lakefile同处项目根目录。基础模板CalculusBasics不声明mathlib；本书将CalculusLean与它并列放在练习目录。即使误把CalculusLean建成子目录，它的依赖也不会自动提供给父项目。

配置中应声明mathlib，通常存于.lake/packages/mathlib。保留已有清单，不为导入错误随意升级依赖。版本相容而确需准备依赖时，逐行执行，每行成功后继续：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake exe cache get
elan run "$project_toolchain" lake build
elan run "$project_toolchain" lake env lean MathlibSmoke.lean
```

默认build只检查配置目标。库入口未导入MathlibSmoke时，build成功并不证明该独立文件可用。

## 刷新导入状态

保存文件及修改过的依赖，单击当前Lean文件源码区，再点击InfoView的Restart File；也可在命令面板搜索该命令。它刷新当前文件所需依赖，不重启电脑、不重装Lean。等待完成，不反复点击。

命令行成功而编辑器失败时核对相同项目、系统和版本，必要时Developer: Reload Window。先处理最早的具体错误，不立即删库或升级。

## 缺失产物与缓存恢复

.hash/.trace存在不保证所有.olean都存在。增量缓存可能依据记录跳过解包。部分复制、同步清理、写入中断及交叉构建都可能造成残缺，但须结合日志查明，不能仅凭现象断言原因。

先核对版本、避免并行构建。如果本地有相容压缩缓存而产物缺失或需覆盖恢复，可执行：

```bash
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake exe cache unpack!
elan run "$project_toolchain" lake env lean MathlibSmoke.lean
```

unpack!强制解包，不补下载。get!会强制重新下载，可能重复传输大量内容，不作常规步骤。先查看当前项目cache --help。预防时保持版本相容、串行构建、不挑选复制生成文件、不实时合并不同机器的.lake，并预留磁盘空间。

## 阅读公理依赖输出

#print axioms列出基础依赖，不是待证明引理清单。propext、Classical.choice、Quot.sound分别涉及命题外延性、选择与商类型；sorryAx则提示占位或未完成证明。用户声明的额外公理也应阅读说明。完整短例子见[公理查询示例](../lean/AppendixA/AxiomAudit.lean)。

参考：[Lean扩展手册](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)、[缓存工具](https://github.com/leanprover-community/mathlib4/blob/master/Cache/Main.lean)、[证明验证](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)、[WSL文件系统](https://learn.microsoft.com/en-us/windows/dev-environment/wsl-interop)。
