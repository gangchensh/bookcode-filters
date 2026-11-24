# Rocq环境、opam与Coquelicot

Rocq、语言服务器和数学库的版本需要相互兼容，不同课程或旧项目可能要求不同组合。为避免更新一个项目的软件时影响另一个项目，可分别建立独立开发环境。opam 是 OCaml 的包和环境管理器，将这种环境称为 switch；其中包含 OCaml 编译器及随后安装的 Rocq、语言服务器和库。创建 switch 不会自动装齐这些包；apt 另负责 Ubuntu 系统工具。

选中 switch 后，还需让当前终端找到其中的程序。例如，在已创建本书示例环境后执行：

```bash
eval "$(opam env --switch=calculus-rocq-9.2 --set-switch)"
rocq -v
```

opam env 输出该环境所需的变量设置，命令替换取得输出，eval 将设置应用到当前 shell。随后启动的程序使用这个环境；已打开的编辑器不会自动切换服务器，项目也不会自动重新构建。switch 名不等于 Rocq 版本，以 rocq -v 核验；本书使用9.2.0。

calculus-rocq-9.2是本书的示例switch名字，不是软件包。可以自选名字，但create和env命令需一致；用opam var prefix看实际安装前缀。m4是构建用宏处理工具，pkg-config查询系统开发库的路径和链接参数，它们都不是数学库。

Windows与Ubuntu各有RocqIDE，须与对应证明器/库环境配套。Ubuntu编译出的库应由同环境的Ubuntu RocqIDE或VS Code连接WSL使用。源码.v可共享，.vo和插件不保证跨系统或版本相容，应在目标环境重新安装依赖和编译。路径可访问不代表能导入。

Coquelicot是Rocq/Coq实分析库，提供极限、导数、积分等，并使用滤子组织分析概念。检查目标环境：

```bash
opam switch show
opam list --installed coq-coquelicot
opam list --installed | grep -i coquelicot
command -v rocq
rocq -v
```

search/show不能代替已安装检查。opam不知道另一套apt或Platform二进制安装时，用实际证明器测试导入，从代码根目录执行：

```bash
rocq compile rocq/AppendixA/CoquelicotSmoke.v
```

Windows RocqIDE也可打开此源文件逐句执行。通过后无需重复安装；失败则检查版本、逻辑路径和实际安装环境。

参考：[opam](https://opam.ocaml.org/doc/Usage.html)、[Coquelicot](https://coquelicot.gitlabpages.inria.fr/coquelicot/)、[跨平台库讨论](https://discourse.rocq-prover.org/t/is-it-possible-to-share-binary-only-libraries-across-oses/1825)。
