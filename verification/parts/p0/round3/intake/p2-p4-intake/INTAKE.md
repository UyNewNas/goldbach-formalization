# Part 0 第三批：P2 / P4 固定源码与验证接收回执

## 接收结论

本次只读接收核对已完成。**建议接收 P2 的三个新模块，共 56 个新增所属声明；P4 本次没有达到接收门槛的新模块。** 没有启动 Lean、内核重放、CI 或 Codex 任务，没有更改 P2、P4 的源码分支，也没有向现有构建发送信号。

固定源码、原始执行证据与本次纯接收检查分别登记。机读总入口是 [INTAKE.json](INTAKE.json)。本次产生的记录不是新的 Lean 执行回执：实际证明门来自固定生产者执行和 GitHub 已完成的同源专项验证。

共同证明基线为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`，手稿为 `ba6ec11d800eccc54406490631895e174de85766`。Lean、Mathlib、goldbach 和全部十一项依赖 pin 保持不变。远端树内无适用的 `AGENTS.md`；已读取现存项目说明、当前手稿映射、外部复用审计及两个 Part 的固定交接。

## 1. 正式取得的版本

| 对象 | 完整 SHA | 本批身份 |
|---|---|---|
| P2 最新交接 | `076473720210ee602e6e9735902e16bb6c5f1398` | 元数据子提交；九份生产源码与下行固定证明提交相同 |
| P2 固定证明 | `6acf61cc28f227a9154363f2347c386ec01dffb0` | 三个新增模块及接收 P0 的六个修复版 |
| P2 固定证明树 | `1b8eb30cccc97d19bff25a533f51e3c9ba927d31` | receipt 绑定的固定树 |
| P2 证明父提交 | `b2ecfdc74b1ebb17be8509c3664f3ca558538b3e` | 不含本批三个新文件 |
| P4 最新固定提交 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` | 只变更核心工作流时限；五生产源码不变 |
| P4 固定生产源码检查点 | `262f69822a386a9d44efc059bceba11049668d68` | 五模块仍是未完成验证的候选 |

本次通过 GitHub 连接器读取了两个固定引用、完整固定树、提交元数据、交接正文、P2 receipt、新三模块及审计源码、P4 五个固定源码。其余接收文件从现有 P2 目录取出并逐 Git blob 对照远端固定树：**129 个选定文件全匹配，0 个缺失，0 个不一致**。P2 工作目录的 `.git` 已不在，未用工作目录名推断源码身份。原始元数据在 `remote/`，逐文件清单在 [p2/fixed-source-manifest.json](p2/fixed-source-manifest.json)。

末次引用回读仍为上表两个最新固定 SHA。P4 的未提交修改独立冻结于 [p4/live-snapshot-manifest.json](p4/live-snapshot-manifest.json)，没有与固定证据混合。

## 2. P2 最小可接收批

以下三个生产文件均在 `ImbalancedChen/Certificates/`，归 P2 所有。公共根导入由 P0 负责。

| 模块 | 完整源码 SHA256 | Git blob | 所属声明数 | 严格编译 / 重放 |
|---|---|---|---:|---|
| `PairedV2Geometry` | `68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238` | `f7bb75a4a2c1b4debc41a334df30d64bf81647f5` | 10 | 4.919 / 3.160 秒 |
| `PairedV2Prefix4Data` | `25ffbba57b5fdff9ce23290ade00fbeaa2b38c2e44ffe9e8637404c8287aab2c` | `3bfedf4c0c6222adb6afa747b2a4c394de841bc5` | 11 | 3.696 / 3.105 秒 |
| `PairedV2Prefix4` | `dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395` | `40dfff1c63af27d15da9f22e88b4b11e96369672` | 35 | 7.675 / 3.496 秒 |

每个生产模块的严格编译、原装 `leanchecker --verbose MODULE` 重放均实际退出 0。官方 frontend 参数为 `trustLevel=0`、`warningAsError=true`，`metadata_adapter=false`。三份 `.olean` 当前仍可读取，均与原始门绑定的哈希相同：

| 模块 | 对象 SHA256 |
|---|---|
| `PairedV2Geometry` | `97383a88879ade52298b58954f6e825d97e17ab4d964e9a3ea57eb51fabd72fd` |
| `PairedV2Prefix4Data` | `41dc48727c4e788c9f5518c6acdf7d8590cc9dca761955ec92eba171d9c8eee0` |
| `PairedV2Prefix4` | `2d90266fee10f47d425bb18c80be306fe4a33b9e9bc8aaedbff93fbd2558af45` |

联合 `CertificateAudit` 实际运行 62.203 秒，覆盖九模块 **309** 个所属声明，含 private/generated。旧六模块的 **253** 条完整记录与 P0 已验收记录逐条相同，旧六个生产文件 SHA256 也全部保持 P0 已验收值。本次新增计数只加 **56**，不能再加旧 253。

原始门前后源码、生产导入对象、共享输入与重放目标身份保持稳定。联合审计实际导入的九生产对象逐项匹配各自成功门；全部完整类型没有 `⋯` 截断，新增自定义公理和所属 unsafe 声明为 0，传递公理并集仅 `propext`、`Classical.choice`、`Quot.sound`。本地运行器中官方初始化器的调用位于生产证明树外，已由生产者透明归档；没有改 Lean 二进制或内核。

本次实际执行的纯接收命令：

```sh
python3 verification/part2/round2/prefix4/verify_acceptance.py
```

在 `p2/fixed/` 中退出 0，输出 `PASS_ARCHIVED_PREFIX4_ACCEPTANCE`、3 新模块、6 复用模块、309 声明、56 新声明，以及 `new_lean_compile_or_replay_in_this_receiving_check: false`。本次另执行 `build_intake_report.py`，核对远端 blob、当前对象、P0 六模块指纹及 CI 完整类型一致性，返回 `PASS_READONLY_INTAKE`。

证据入口：

- [生产者完整回执](p2/fixed/verification/part2/round2/prefix4/receipt.json)、[全部实际 gates](p2/fixed/verification/part2/round2/prefix4/gates/)。
- [56 条新增完整编译器类型](p2/COMPILER_TYPES_NEW.md)；机读 [compiler-confirmed-new-declarations.json](p2/compiler-confirmed-new-declarations.json)。
- [关键完整类型](KEY_THEOREM_TYPES.md)。
- [接收脚本原始结果](p2/archived-receiving-check.json)。

## 3. 同一 P2 SHA 的正常 GitHub 验证

正式读取固定 `076473720210ee602e6e9735902e16bb6c5f1398` 的 Actions，三个工作流均已完成。

| 工作流 | Run | 实际结论 |
|---|---:|---|
| Part 2 numerical certificates | `38233341120` | success |
| Variable envelope verification | `38233341402` | success |
| Lean core verification | `38233341407` | success |

专项 job `114757885703` 原始日志已保存为 [p2/ci/job-114757885703.log](p2/ci/job-114757885703.log)。日志包含九个生产目标逐个显式 `Built`、警告作为错误的逐源 elaboration、九个原装 `leanchecker` 目标重放，以及 `P2_AUDIT_COUNT 309`。该正常托管环境的 **309 条完整类型记录与固定生产者联合审计逐条全等**。没有发起新的 CI，也没有把本次纯接收检查当作新的 Lean 执行。

本次只把该固定 SHA 的专项结果用于相同生产源码；P0 未来集成 SHA 的整根验证须另行记录。这里的原装逐模块重放也不声称是 `--fresh` 全依赖闭包重放。

## 4. 实际四格对象、采用范围与未闭合输入

采用 same-mask-v2 原始数据，手稿文件 SHA256 保持 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`，Git blob 保持 `49499697cca96de5f7b779e95077874ce5f9d119`。本批只用原始零基行 `0,1,2,3`，全部为 E0；行流 SHA256 为 `96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235`。

| 行 | `(t_index,u_index)` | 实际 `Z` |
|---:|---|---|
| 0 | `(422,510)` | `76088109/532480000` |
| 1 | `(422,511)` | `1170333/8192000` |
| 2 | `(423,509)` | `9511851/66560000` |
| 3 | `(423,510)` | `9509793/66560000` |

四项为真实四重积分的有限和，系数仍是 `K/80 = (K/4)*(1/20)`，核仍是 `1/(t*u*z^2*w)`。已证明的上下界分别为：

```text
12676565261567 / 100000000000000000000
12676572571081 / 100000000000000000000
```

证明链显式给出实际数值检查、证书参数与四行实际端点的身份、真实积分语义和求和有理界。没有以存储 Q160 区间为命题假设。Geometry 的几何条件不含积分收益，证明整个开纤维的顺序、非空、E0 残量门与 Buchstab 参数至少 `7/3`。

四格前缀**含旧首格**，不能与旧首格积分再次相加。`K/80` 已计入 Buchstab 的 `1/20` 增益，不可重复乘入。E0 几何条件不能用来重标 E1。允许开域的末格外端点等于 `h` 或 `d`，以及 `Z=uLower`；排除 `a=Z` 和零外层宽度。

下列仍未完成：其余实际行与 E1、saved-floor 语义、并域积分身份与不重计、完整历史算术父许可、Y6/Y11 实际配对插入、完整误差总账与两份 reserve、完整 K/c 和最终上下界。原先已接收的 Coarse 仍只是上界政策中带负号的一个节省项；其物理换元、覆盖和实际 rho 身份仍需 P1/P4 供应。

P2 的 `PART1_INTERFACE.md` 仍是单方接口草案，不因为本次接收自动变成 P1 已签署契约。可立即转交 P1 / P5 的是上述具体积分和与几何定理；P4-A/P4-B 仍可用既有 Coarse 局部结果，不能用四格下界代替完整 K 上界。

## 5. P2 首处真实诊断与修复身份

两次原失败完整记录均保留于 [p2/first-diagnostics.json](p2/first-diagnostics.json) 和生产者 `attempts/`。

| 目标 | 失败源码 SHA256 | 首诊断 | 成功源码 |
|---|---|---|---|
| Geometry | `30ec2fab9836cffc0d50118afaa6132b5ae475585272f0dfcf1be717ecf602a5` | 82:4，`mod_cast` 的有理表达式与所需实数强制转换形状不同；103:4 第二处同类问题 | `68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238` |
| Prefix4 | `be93294540e84e0334b73f6acd8a2311ccb5ebc7393a2ad4705c33b3e5ab395c` | 95:44，`simp only [← integral]` 不允许用定义名反折叠；其后目标类型不匹配 | `dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395` |

Geometry 成功源码使用 `Rat.cast_le.mpr` 和显式 cast 化简；其旧源码正文没有归档，本次不伪造它。Prefix4 的失败正文已保存，实际修复只是将 `← integral` 改为 `integral`；本次从两份真实正文生成 [Prefix4-preserved-repair.patch](p2/Prefix4-preserved-repair.patch)。这两处修复均属于 P2 的固定证明交付，本次没有另作生产源码修复。

## 6. P4：有运行器、有实际步骤，但五目标尚未到达

固定 `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` 的核心与 Variable envelope 工作流均 success；**Part 4 专项 run `38227776544`、job `114739426423` 为 failure**。旧根未导入五个新增 P4 模块，核心成功不能覆盖它们。

本次下载并校验 artifact `11738303921`，ZIP SHA256：

```text
e095c679e32191e32bb206bb6ab190212bfba1d7b433f2800c8f6401d8f273d9
```

真实 report 显示 checkout、基线祖先、依赖和锁定工具链启动均通过；调用五目标的依赖构建于 `2026-10-12 09:08:46 UTC` 开始，在 1800.053 秒后被 Python 子进程时限终止。最后真实完成项是 `9326/9404 MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension`。构建日志没有 Lean `error:`，没有任何五目标的 `Built`，尚无五目标的严格编译、重放或完整审计。

明确的失败为：

```text
Command ['lake', 'build', 'ImbalancedChen.ActualUpperPolicyDensity',
'ImbalancedChen.UpperCoefficientPerturbation',
'ImbalancedChen.ActualUpperDensityAssembly',
'ImbalancedChen.RealPhysicalUpperWeightBridge',
'ImbalancedChen.RealUpperCountingAssembly'] timed out after 1799.999990722 seconds
```

这是已取得运行器后的依赖构建超时，不是“无步骤 CI”，也不是 Lean 证明错误。没有将超时改写为证明失败，更没有从无错误推导证明成功。[CI_RECEIPT.json](p4/CI_RECEIPT.json) 绑定五份固定源码与原 report，原 artifact 及原始日志都在 `p4/ci/`。

## 7. P4 未提交候选和真实接口

在 `2026-10-12 11:58:36 UTC` 读取的本地快照中，三份生产文件与固定源不同：

| 文件 | live SHA256 | 本次身份 |
|---|---|---|
| `UpperCoefficientPerturbation.lean` | `e4d1d84fa128f7f84fb4f7d4f0b03acf8401312de1ceaed045de3aaf3b5d6e86` | 未提交候选 |
| `ActualUpperDensityAssembly.lean` | `659aa3d8cfa50345f912ba070e30cd57a6caa1738e4146d1c051a7506f944cec` | 未提交候选 |
| `RealPhysicalUpperWeightBridge.lean` | `8a86c2e7fd2383fcae243b5958f3447675a4f5b7a4c9078ba1ba832ea067878f` | 未提交候选 |

另外两份生产文件仍与固定源码相同。live 工作流和验证器也有修改：拟给依赖构建 90 分钟，并在五个独立目标重放后进行一次覆盖全部五模块导入闭包的 fresh 审计重放。这些更改只作为快照记录，未在本次执行或接受。完整差异在 [p4/live-vs-fixed.patch](p4/live-vs-fixed.patch)。

五个固定文件共提取 **53 个完整公开定理签名**，在 [p4/SOURCE_THEOREM_TYPES.md](p4/SOURCE_THEOREM_TYPES.md) 和 [p4/source-theorem-types.json](p4/source-theorem-types.json) 中；明确标注源码提取，编译器确认数为 0。

真实未闭合接口仍为：完整实际 policy 与 compiled rough coefficient；raw carrier 到共同 carrier 的零延拓；同一权的点态 majorant；实际主积分和全部采用数值证书；实际 `M * Σ |compiled-raw|/φ` 编译误差，其中 `M=V*(1+Esmall)`；`log D` 到 `log N` 的精确因子；同一个 `Q delta N` / `rho delta N` 的密度、互素修正与带符号分布误差。

误差账仍要把 `E+u` 与第二份编译 reserve 分开，并真正证明 `E+2u≤K` 所服务的两个实际误差界。Raw 的 K 界不自动留下编译余量。`hIntegral` 所需精确 `Tendsto` 不能以仅有的积分上包络替代；外层超过 N 的光滑源还需整数平移适配，不能用自然数减法直接替换。参数 `b,kappa,sieveExponent` 先于 `delta` 的量词顺序保留。

**没有实际 K 导出或 hUpper 供应者在本次闭合。P5 继续只等待 P4-A，无需等待 P4-B。** P0 可以立即接收本次三份 P2 生产源码和证据，再在自己的明确集成 SHA 上完成公共根与后续验证。
