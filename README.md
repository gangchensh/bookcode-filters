# 形式化微积分的滤子基础：Lean与Rocq代码

八章精简版《AI时代的形式化微积分——从滤子到微积分基本定理》的读者，请先看[精简版章节与源码映射](docs/compact-edition.md)。下文的第1—13章指原版源码模块编号，不能直接代入精简版第5—8章的章号。

《形式化微积分的滤子基础》的开源配套代码，作者：陈钢，南京航空航天大学计算机科学与技术学院/人工智能学院。

本目录可直接作为独立GitHub仓库根目录。提供当前第1—13章的可编译入口、完整证明源码、安装说明和构建工具。教材TeX、PDF和作者讨论材料不放在仓库中。

## 版本与首次准备

- Lean **4.35.0**、Mathlib **v4.35.0**；精确依赖提交由 `lean/lake-manifest.json` 保存。
- Rocq **9.2.0**、标准库 **9.2.0**、Coquelicot **3.4.5**；已验证的OCaml为 **4.14.1**，依赖见 `formal-filter-calculus.opam`。

在 Ubuntu 或 WSL Ubuntu 的终端中准备系统工具。Windows 用户可参阅 [附录 A](appendix-a/README.md) 安装 WSL 和编辑器。

```bash
sudo apt update
sudo apt install git curl make build-essential opam bubblewrap m4 pkg-config libgmp-dev unzip python3
```

**Lean。** 首次安装 Elan 时运行下列命令。已有 Elan 的读者可从进入 `lean/` 的步骤开始。

```bash
curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
source "$HOME/.elan/env"
```

在仓库根目录准备锁定版本的 Lean 工具链和 Mathlib 缓存：

```bash
cd lean
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan run --install "$project_toolchain" lean --version
elan run "$project_toolchain" lake exe cache get
cd ..
```

**Rocq。** 在仓库根目录执行下列命令。已初始化 opam 的读者可跳过第一行。若同名 switch 已存在，跳过创建步骤，直接激活它。安装 OCaml 编译器和 Rocq 依赖可能需要较长时间。

```bash
opam init --bare --no-setup
opam switch create calculus-rocq-9.2 ocaml-base-compiler.4.14.1
eval "$(opam env --switch=calculus-rocq-9.2 --set-switch)"
opam repository add rocq-released https://rocq-prover.org/opam/released
opam install . --deps-only
rocq -v
opam list --installed coq-coquelicot
```

若已为该 switch 添加同名 Rocq 发布源，可直接安装依赖。以后打开新的 Ubuntu 终端，运行上面的 `eval` 命令即可在该终端使用此 switch。

## 检查代码

```bash
make check-lean                 # Lean 全部章节与配套示例
make check-rocq                 # Rocq 全部章节与配套示例，含 Coquelicot
make chapter CHAPTER=03         # 只构建第3章及其依赖
```

`make check` 顺序执行两种语言的完整检查。成功通常显示Lake构建成功或Make目标完成；单个文件检查可能没有额外输出。首次数学库载入与构建可能较慢；不会每次重新下载Mathlib。

Lean编辑器打开 `lean/`，Rocq编辑器打开 `rocq/`，两边各只有一个项目根目录。Windows版VS Code应连接WSL后再打开Ubuntu中的项目。运行例子前先构建依赖，不能只复制一个使用文件而忽略它导入的库。

## 按本书章号阅读

`Textbook/ChXX/All` 是每章聚合入口。它导入完整证明，不复制第二套数学定义；具体实现文件保持稳定，位置见每章README和 [详细对应表](docs/textbook/README.md)。

| 章 | 内容 | Lean入口 | Rocq入口 |
| --- | --- | --- | --- |
| 1 | 数学语言、证明器与AI辅助证明 | [Ch01](lean/Textbook/Ch01/All.lean) | [Ch01](rocq/Textbook/Ch01/All.v) |
| 2 | 最终成立、邻域与滤子 | [Ch02](lean/Textbook/Ch02/All.lean) | [Ch02](rocq/Textbook/Ch02/All.v) |
| 3 | 滤子趋近关系与各类极限 | [Ch03](lean/Textbook/Ch03/All.lean) | [Ch03](rocq/Textbook/Ch03/All.v) |
| 4 | 极限运算、连续性与局部行为 | [Ch04](lean/Textbook/Ch04/All.lean) | [Ch04](rocq/Textbook/Ch04/All.v) |
| 5 | 实数完备性与数列收敛 | [Ch05](lean/Textbook/Ch05/All.lean) | [Ch05](rocq/Textbook/Ch05/All.v) |
| 6 | 导数与局部线性化 | [Ch06](lean/Textbook/Ch06/All.lean) | [Ch06](rocq/Textbook/Ch06/All.v) |
| 7 | 微分法则、中值定理与优化 | [Ch07](lean/Textbook/Ch07/All.lean) | [Ch07](rocq/Textbook/Ch07/All.v) |
| 8 | 泰勒公式、渐近关系与误差界 | [Ch08](lean/Textbook/Ch08/All.lean) | [Ch08](rocq/Textbook/Ch08/All.v) |
| 9 | 积分、累积量与微积分基本定理 | [Ch09](lean/Textbook/Ch09/All.lean) | [Ch09](rocq/Textbook/Ch09/All.v) |
| 10 | 积分方法、反常积分与工程量 | [Ch10](lean/Textbook/Ch10/All.lean) | [Ch10](rocq/Textbook/Ch10/All.v) |
| 11 | 级数、幂级数与函数近似 | [Ch11](lean/Textbook/Ch11/All.lean) | [Ch11](rocq/Textbook/Ch11/All.v) |
| 12 | 多元极限、全微分与雅可比 | [Ch12](lean/Textbook/Ch12/All.lean) | [Ch12](rocq/Textbook/Ch12/All.v) |
| 13 | 多重积分与工程积分入门 | [Ch13](lean/Textbook/Ch13/All.lean) | [Ch13](rocq/Textbook/Ch13/All.v) |

## 仓库内容

- `lean/`、`rocq/`：两个统一证明项目，`Textbook/Ch01—Ch13/`按教材章号同时保存入口、完整定义、证明和例子；`Theories/`保存附录公共练习。
- `appendix-a/`、`config/`：安装命令、环境与编辑器配置样例。
- `docs/textbook/`：当前教材源码导航；摘录文本用于阅读，不一定含独立运行的全部导入。
- `.github/workflows/proofs.yml`：提交后分别检查Lean和Rocq。该云端流程需要在实际GitHub仓库运行；本地核验范围见[构建记录](docs/build-validation.md)。
- `scripts/package-release.py`：生成不含缓存、编译结果与本机设置的源码发布包。

目录与命名空间前缀均对应教材章号。[补充练习](docs/legacy-course.md)说明引言和附录的独立例子。

## 发布与许可

```bash
make release
```

发布包生成于 `.release/filter-calculus-code.zip`，含文件清单和SHA256摘要。上传GitHub时以本目录或该包解压后的目录作为仓库根目录。`lean-toolchain`、Lake配置、锁文件和Rocq清单都需保留；`.lake`依赖缓存、`.olean`、`.vo`和本机配置不上传。

原创代码和说明采用 [MIT许可证](LICENSE)，第三方来源与许可范围见 [NOTICE](NOTICE.md)。改进方法见 [CONTRIBUTING](CONTRIBUTING.md)。

各章的实际实现及未覆盖边界见[十三章代码覆盖表](docs/textbook-coverage.md)，按章可搜索的源码名称见[声明清单](docs/textbook-symbols.tsv)。本书纸面简明附录的命令见[命令文本](appendix-a/textbook-quickstart.txt)；详细在线指南保留原编号。
