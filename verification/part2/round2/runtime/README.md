# Part 2 第二轮运行入口恢复证据

本目录归档 **2026-10-12 已实际完成**的运行入口恢复：原装 Lake 调用官方
`Lean.Elab.runFrontend`，在 `trustLevel := 0`、`warningAsError := true` 下编译
`Part2RuntimeProbe`，随后原装 `leanchecker` 重放该 probe。
归档操作只复制既有文件，没有启动新的 Lean 编译或重放进程。

运行方法和六个既有 P2 producer 来自 P0 固定回执提交：

```text
cce2334906f068fda2f58c400646366f2aa2d417
```

P0 验证的六模块源码绑定到证明提交：

```text
278f949444748a30b5165ff47bfa283ab0bad0d8
```

这里保存的成功 probe 只确认运行入口、导入和所列输出可复现到实际执行记录。
**本目录不把 probe 的编译或重放记作六个生产模块重新验证通过，也不记录后续
Geometry/Data/Prefix 模块或组合 audit 的验证结论。** 六个既有生产模块的验证
范围见上述 P0 提交中的 `verification/parts/p0/round2/p2-first/` 和
`verification/parts/p0/round2/p2-coarse/`。

## 实际运行结果

| 动作 | 结果 | 耗时 | 子进程最大 RSS |
| --- | --- | --- | --- |
| strict frontend 编译 `Part2RuntimeProbe` | exit 0；`FRONTEND_OK` | 10.705 秒 | 4,613,728 KiB |
| stock kernel 重放 `Part2RuntimeProbe` | exit 0；`replaying Part2RuntimeProbe` | 3.273 秒 | 3,230,956 KiB |

编译与重放后的 probe `.olean` SHA-256 均为：

```text
5fa0a58ebfd69bf90f15505402900193905fead4e1a1ba3c7d7684ebe8e7e85f
```

Probe 通过 `PairedV2` 和 `AboveMuSecondCoarse` 导入全部六个既有 P2 模块。
原始编译日志给出 `firstIntegral_bounds` 和 `adopted_coarse_lower` 的真实 Lean
类型，并分别报告仅有 `propext`、`Classical.choice`、`Quot.sound`。
原装 checker 本次选择重放的是 **`Part2RuntimeProbe` 自身定义的声明**；导入六个
生产模块不等于本次重放全部六模块。

源代码、共享 producer 源/对象和工具链二进制摘要在 probe 前后保持一致；从
P0 复制的六个本地 producer 对象也在运行后重新核对一致。可检查 `probe/`
中的原始 `.log` 与逐次 `.json` receipt，不必仅相信此说明或汇总 JSON。

## 锁定工具链与官方启动生命周期

工具链固定为 `leanprover/lean4:v4.33.0-rc1`，Lean githash：

```text
62eed1db4d67327ec8120be05f1a1b0847d74561
```

官方发行 Linux archive 的已核对 SHA-256：

```text
25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210
```

当前环境直接运行 stock `lean --version` 仍出现
`error: failed to locate application`。实际可用编译路径为 stock `lake` 运行
独立脚本，调用未经修改的官方 frontend API；本目录据此使用“官方 frontend
编译”和“stock kernel replay”的表述，**不声称普通 `lake build` 已运行成功**。

`frontend-driver.lean.txt` 是从 P0 已用驱动按原字节复制的存档，Git blob 为
`5ba2cfb3d298145e6f273bc7f59c716c055655e8`，SHA-256 为：

```text
ede18bb7c68c9950c2096ed79211c4c26948c21c28ba1985bf9f38d909024f50
```

驱动中的 `unsafe Lean.enableInitializersExecution` 恢复官方 frontend 启动时的
初始化执行生命周期。固定版本的 `Lean/ImportingFlag.lean` 对此有说明，官方
`lake/Lake/Load/Lean/Elab.lean` 也使用同一 API。它位于独立运行驱动，不向生产
证明环境加入公理，不改变 `trustLevel := 0`，也不替换内核。每个模块单独启动
Lake 进程，不在一个进程中混载同名模块的多个 native 版本。

编译和重放均明确记录 `metadata_adapter: false`。未向 PATH 放入假 `lean`
程序，未改工具链二进制或内核，也未更改项目锁定依赖。Stock checker 设置
`LEAN_SYSROOT` 后，直接使用其官方 `findSysroot` 环境入口启动。

## 文件索引与原字节校验

| 文件 | 含义 |
| --- | --- |
| `frontend-driver.lean.txt` | P0 官方 frontend API 驱动的原文存档；运行副本需命名为 `frontend-driver/lakefile.lean` |
| `invoke-probe-tested.py` | 成功 probe 实际使用的 Python runner 的精确代码快照 |
| `verify_project.py` | 后续单模块 project runner 的只读快照；含本地 producer 前后哈希检查，源码/对象根绑定到当时 P2 仓库 |
| `Part2RuntimeProbe.lean.txt` | 实际成功 probe 源码的原字节存档 |
| `environment.json` | 成功 probe 的完整环境路径与单线程设置 |
| `project-environment.json` | project runner 的完整环境；本仓库对象目录在搜索路径首位 |
| `recovery-provenance.json` | 原装二进制哈希、11 个 exact pin 依赖及六个 P0 producer 的源/对象对应 |
| `project-cache-transfer.json` | 六模块从 P0 对象目录到 P2 本仓库对象目录的来源/目标哈希与独立文件记录 |
| `recovery-summary.json` | 恢复过程汇总及精确验证范围；原始日志是实际命令输出依据 |
| `probe/*.json`、`probe/*.log` | 两次成功实际运行的完整命令、环境、摘要、exit status 与原始 stdout/stderr |
| `ARCHIVE_MANIFEST.json` | 每个复制文件的观察来源路径、字节数和来源/目标 SHA-256 |
| `SHA256SUMS` | 本目录所有其余交付文件的 SHA-256 清单 |

13 个原始输入文件全部按字节复制；没有重排 JSON、规范换行、替换历史绝对路径
或改写日志。文件名改为 `.lean.txt` 仅用于区分证据存档与生产 Lean 模块。

在本目录可以只运行普通文件校验：

```bash
sha256sum -c SHA256SUMS
```

该校验确认归档字节，没有重新执行 Lean 或验证积分。

## 已观察的路径与缓存来源

| 用途 | 观察时的绝对路径 |
| --- | --- |
| 本轮 P2 仓库 | `/workspace/scratch/1334dbd5a747/goldbach-formalization` |
| P2 原装工具链 | `/workspace/scratch/1334dbd5a747/lean-runtime-p2/lean-4.33.0-rc1-linux` |
| P2 运行工作区 | `/workspace/scratch/1334dbd5a747/lean-runtime-p2/recovery` |
| P0 已验证生产对象 | `/workspace/scratch/535d89efd063/p0-round2/validation/.lake/build/lib/lean` |
| 共享 P1 完成对象和 exact pin 依赖 | `/workspace/scratch/127408f63891/goldbach-formalization` |

11 个依赖 Git HEAD 与锁定清单逐项一致，tracked clean。P2 和 P1 两份原装
`lean`、`lake`、`leanchecker` 的 SHA-256 逐一一致；实际使用的是表中的 P2
原装工具链。

六个 P0 producer 为 `RationalLogCertificate`、`PairedFibreIntegral`、
`PairedCertificateChecker`、`PairedV2Data`、`PairedV2`、`AboveMuSecondCoarse`。
复制前，本轮 P2 六个源码均与 P0 validated 源码 SHA-256 相同；复制后每个对象
来源/目标 SHA-256 相同。复制的是独立字节文件，没有 hardlink 或指向共享
对象的输出 symlink。复制规则检查所有实际存在的 `.olean*` 文件；这六个
producer 当时只有主 `.olean`，没有 `.olean.server` 或 `.olean.private`。

Lean 的顶层模块目录选择可能使一个局部 `ImbalancedChen` 目录遮蔽后续根中的
同名目录。本轮因此把六个精确 producer 同时放到 P2 自己的输出根，使三个新增
证书模块可以在同一根中找到既有依赖。后续如引入其他 Part 的
`ImbalancedChen` 模块，需明确选择并加入其已验证对象，不能假设后续根自动补齐。

## 重定位与复现入口

本目录是**历史原字节存档**。保存的绝对路径描述实际执行环境，不能直接当作
另一台机器已经拥有的目录。`verify_project.py` 也保留了原来的 `PROJECT`
常量和原样环境输入，便于核对真实命令；不要在这个证据目录中直接改写它们。

若原观察工作区仍可读，可直接使用原 runner，单次运行指定模块：

```bash
python /workspace/scratch/1334dbd5a747/lean-runtime-p2/recovery/verify_project.py compile MODULE
python /workspace/scratch/1334dbd5a747/lean-runtime-p2/recovery/verify_project.py replay MODULE
```

`MODULE` 是显式指定的完整 Lean 模块名。`compile` 默认从 P2 仓库的对应
模块路径读取源码，也接受第四参数指定绝对源码路径。对象只写入 P2 自己的
`.lake/build/lib/lean`；该 runner 不自动构建缺失依赖。

在新环境复现，应先校验存档，然后在**独立运行工作区的副本**中重定位：

1. 安装并核对上述准确官方工具链及锁定依赖；准备所需的准确已验证 producer
   对象。此 Git 存档不内嵌工具链、mathlib cache 或六个 `.olean` 二进制。
2. 将驱动原文字节复制到运行副本的 `frontend-driver/lakefile.lean`，将
   project runner、`project-environment.json` 和 `recovery-provenance.json`
   复制到该运行工作区。驱动内容和 Lean 工具链版本保持不变。
3. 在 runner 的运行副本中把 `PROJECT` 改为重定位后的 P2 源码根；`BASE`
   由 runner 自己的位置决定，`OBJECTS` 仍为该项目的 `.lake/build/lib/lean`。
4. 在环境副本中更新 `LEAN_SYSROOT`、`LAKE_HOME`、`LEAN_PATH`、
   `LEAN_SRC_PATH` 的路径。保持准确版本、`LEAN_NUM_THREADS=1`、自有输出根
   优先及每个模块唯一选定 producer 的语义。
5. `recovery-provenance.json` 的路径字段也需指向实际复用的同字节源码/对象与
   工具链；保留并检查原哈希。若必须从源码重新生成 producer，其对象哈希可能
   不同，应先独立完成该 producer 的 strict 编译、kernel replay 和 axiom
   audit，并形成新的来源/对象回执；不能把新对象改填为“原 P0 同对象”。
6. 为重定位后的源码、运行副本、环境、依赖对象和结果产生新哈希及新 receipt。
   新环境的成功应由实际执行确认，不能从本次历史 probe 推断。

准确底层入口记录在原始 receipts 的 `command` 数组中：stock `lake -d DRIVER
-f lakefile.lean script run compileOne SOURCE MODULE OUTPUT strict`，随后 stock
`leanchecker --verbose MODULE`。runner 显式设置环境；驱动固定 `trustLevel := 0`
并由 `strict` 选择 `warningAsError := true`。

## 资源和使用限制

观察时共享 memory cgroup 上限为 8 GiB。仅导入/type probe 已达到约 4.4 GiB
RSS，checker 达到约 3.1 GiB。保持 `LEAN_NUM_THREADS=1`，每次只运行一个
frontend 或 checker，并与其他 Part 的大型运行错开。复用完成且已核对的缓存，
不要重复启动大型依赖闭包，也不要向共享 producer 目录写对象。

这里的积分类型输出分别涉及一个实际 B fibre 和 A 的 two-chart integral。
运行恢复不扩大其数学作用范围，不补出所有 17,572 个单元、完整误差总账或
物理域换元/历史极限语义；这些仍应按对应生产证明及各 Part 接口判断。
