# WSL 资源配置与高负载任务限制

对应附录 A.5。先区分两层：`.wslconfig` 限制整个 WSL 2 虚拟机；单个任务及其子进程需另外设置 cgroup 额度。多个 WSL 2 发行版共享虚拟机资源，分别装两个 Ubuntu 不能代替任务隔离。

## WSL 总额度：按需修改一次

在普通 Windows PowerShell 中打开当前 Windows 用户的配置：

```powershell
notepad "$env:USERPROFILE\.wslconfig"
```

`$env:USERPROFILE` 是 Windows 用户主目录。以主机16GB内存、至少4个逻辑处理器为例，[配置样例](../config/wslconfig.example)为：

```ini
[wsl2]
memory=8GB
processors=4
swap=4GB
```

已有配置应保留其他设置，修改已有 `[wsl2]` 下的相应条目，不重复小节；新文件确认没有被保存为 `.wslconfig.txt`。memory 是内存上限，processors 是可用逻辑处理器数，swap 是磁盘上的交换空间。按主机实际资源调整，给 Windows 及其他应用留余量。Ubuntu 的 `/etc/wsl.conf` 是发行版配置，与这个文件不同。

保存工作并结束所有 WSL 任务后，在 PowerShell 执行：

```powershell
wsl --shutdown
wsl -d Ubuntu
```

第一条停止全部 WSL 发行版及进程；第二条的 Ubuntu 按实际名称替换。重新进入后用 `free -h`、`nproc` 检查。free 显示的是 Linux 环境可用内存及使用情况，通常小于主机物理内存。

## 任务额度：每次启动高负载任务时使用

Linux 的进程是运行中的程序；智能体启动的证明器是它的子进程。cgroup 将整组进程统一计量与限制，避免只限制智能体本身、遗漏它启动的工具。本例通过 systemd 服务管理程序建立资源组，要求 systemd >=253、cgroup v2、可连接的当前用户服务管理程序。

在 Ubuntu 任意目录检查：

```bash
ps -p 1 -o comm=
systemd --version
stat -fc %T /sys/fs/cgroup
systemctl --user show-environment
```

预期分别包含 systemd、版本号、cgroup2fs、当前用户服务管理程序的环境变量。检查失败不要忽略。未启用 systemd 时按微软文档在 `/etc/wsl.conf` 的 `[boot]` 下设置 `systemd=true`，保留已有内容，保存工作后重启 WSL。更新或配置步骤见文末官方说明。

在任务的项目目录启动受限子终端：

```bash
systemd-run --user --scope \
  -p MemoryHigh=3G -p MemoryMax=4G \
  -p MemorySwapMax=1G -p CPUQuota=200% \
  -p OOMPolicy=kill bash
```

`--user` 使用当前用户的服务管理程序；`--scope` 为 Bash 及普通子进程建立资源组，继承原来的目录和环境；`-p` 设置属性。默认示例适用于8GB WSL额度：

| 属性 | 作用 |
| --- | --- |
| MemoryHigh=3G | 组内内存超过3GiB后加强回收并使任务减速 |
| MemoryMax=4G | 组内内存硬上限4GiB，无法回收时在组内处理 OOM |
| MemorySwapMax=1G | 该组交换空间另限1GiB |
| CPUQuota=200% | 合计约两个逻辑处理器的计算能力，不是固定占有两个处理器 |
| OOMPolicy=kill | 发生 OOM 终止时结束整组任务，避免残留部分子进程 |

现在在子终端启动已安装的智能体或证明命令；`exit` 离开子终端。不同任务分别启动，所有组额度之和也要给系统、编辑器和组外程序留余量。

从开源代码根目录可用[便捷脚本](scripts/run-limited.sh)，下面两个例子任选一个：

```bash
bash appendix-a/scripts/run-limited.sh bash
bash appendix-a/scripts/run-limited.sh make lean
```

第二条须先安装 Lean，`make lean` 的多文件构建见 A.11。脚本默认值与直接命令相同；可通过 `LIMIT_MEMORY_HIGH`、`LIMIT_MEMORY_MAX`、`LIMIT_SWAP_MAX`、`LIMIT_CPU_QUOTA` 调整。例如，仅对本次启动采用更小额度：

```bash
LIMIT_MEMORY_HIGH=1G LIMIT_MEMORY_MAX=2G \
  bash appendix-a/scripts/run-limited.sh bash
```

脚本未满足前提或无法建立资源组时会报错，不会退回无约束执行。它只限制本次启动的命令及继承该组的子进程，不会改变其他进程或系统配置。已运行的 VS Code/智能体后台服务不自动加入；`code .` 可能复用已有服务，因此不保证编辑器受限。每次脚本启动建立新组，别把无关任务都放进同一个子终端。

内存额度降低组内 OOM 连带影响其他进程的风险，不能保证系统永不崩溃。组外程序、多个组总量过大或 WSL 故障仍可能影响整个环境。CPUQuota、nice 不代替内存限额。

## 内存耗尽后的处理

未设置任务额度时，Linux 可能终止某些进程释放内存，不是必然停止所有 WSL 进程。编辑器服务被终止会使多个窗口断开；严重资源压力或虚拟机异常也可能导致 WSL 失去响应。

重新进入 Ubuntu 后查看本次启动的内核日志末尾：

```bash
sudo journalctl -k -b -n 80 --no-pager
```

查找 Out of memory、oom-kill、Killed process。上次崩溃后日志可能未保留，当前日志没有记录不能排除 OOM。若只有受限任务结束，降低搜索规模或并行度再重试；若整个 WSL 无响应，确认无法继续保存的工作后才用 `wsl --shutdown` 重启。已保存源码通常仍在，未保存内容可能丢失，中断构建的目标文件可能需要重建。

官方资料：[WSL 配置](https://learn.microsoft.com/en-us/windows/wsl/wsl-config)、[在 WSL 启用 systemd](https://learn.microsoft.com/en-us/windows/wsl/systemd)、[systemd 资源控制](https://www.freedesktop.org/software/systemd/man/latest/systemd.resource-control.html)、[scope 的 OOM 策略](https://www.freedesktop.org/software/systemd/man/latest/systemd.scope.html)、[cgroup v2](https://docs.kernel.org/admin-guide/cgroup-v2.html)。完整网址另见附录末尾与 [网址清单](web-resources.txt)。
