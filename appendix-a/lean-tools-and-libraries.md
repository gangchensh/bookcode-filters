# elan、Lake与mathlib

## 工具分工

- elan：下载和保存Lean工具链，按项目或临时指定选择版本。工具链包含Lean、Lake及标准库。
- lake：创建项目、管理依赖清单、准备环境、调用工具和组织构建。
- lean：检查Lean源码；lake env后面的lean就是这个程序名。

## math项目准备了什么

建立依赖mathlib的数学项目，准备相容工具链、数学库源码、依赖及编译缓存。Std随工具链提供；mathlib另由项目管理，包含实数、拓扑、分析等内容。

创建命令通过elan先获取mathlib所要求的工具链，随后Lake生成项目、取得依赖。mathlib更新钩子可能已自动下载缓存，因此创建时就可能持续联网。

```bash
elan run --install leanprover-community/mathlib4:lean-toolchain lake new CalculusLean math
cd CalculusLean
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run "$project_toolchain" lake exe cache get
elan run "$project_toolchain" lake build
```

后两个elan run都使用本项目记录的版本：

- exe cache get：运行mathlib缓存工具，下载缺少的相容编译结果并解压；此前已获取时复用，不再次下载整套。
- build：构建配置目标，复用未改变的结果，编译缺失或失配的结果。通常不重复下载整个mathlib，但依赖及远程缓存准备仍可能联网。

下载量与占用预算见 [资源与下载](resources-and-downloads.md)。创建源码、取得缓存和本机编译是不同阶段。

## 日常检查

以上创建项目和准备缓存通常只在首次准备时执行。此后在 CalculusLean 保存文件，运行 `lake env lean MathlibSmoke.lean` 检查独立文件，或用 `lake build` 构建配置目标。正常 elan 代理根据 lean-toolchain 选版。

可选：从 CalculusLean 运行 `cp -i ../code/appendix-a/scripts/check-lean.sh check-lean.sh`，以后 `bash check-lean.sh` 检查默认例子，`bash check-lean.sh 文件名.lean` 检查已存在文件，`bash check-lean.sh --build` 构建目标。脚本显式选择项目版本；不重复 new、升级依赖或强制解包。附件与项目不并列时修改复制路径。

## ∀ᶠ 的含义

∀ᶠ n in atTop, P n表示“沿atTop最终成立”。对自然数，它等价于存在N，使所有n≥N满足P(n)。它不要求最前面的所有自然数都满足性质，例如100≤n最终成立，但并非对每个n成立。

上标f标识滤子意义的eventually，不是幂，也不是函数f。atTop指定自然数越来越大的趋近方式；hP/hQ是两项性质的证明，hP.and hQ合并它们。

参考：[滤子记号](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)、[mathlib配置](https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean)、[Lake模板](https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/CLI/Init.lean)。

导入报错见 [Mathlib排查](mathlib-import-troubleshooting.md)；版本安装和检查／编译术语见 [工具链对照](toolchain-comparison.md)。
