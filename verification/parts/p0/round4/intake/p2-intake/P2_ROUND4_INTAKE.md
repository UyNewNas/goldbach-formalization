# Part 0 — P2 rows 4–63 intake

## 接收结论

**PASS：可原样接收 3 个新生产模块，共 400 个所属声明。** 新增原始零基行
[4,64)，合计 60 行；复用 [0,4) 后形成 [0,64) 的 64 行实际四重积分有限和。
P0 本次只执行固定源码、归档及实际 CI 的纯证据接收，没有运行 Lean、Lake、
leanchecker、CI 或 Codex，也没有修改集成工作树或其他 Part 分支。

- 交接 head：`101bb2291cd51f9717544ce477122fdd44eda44d`
- 固定 proof：`f0c00f9ccce98e04af439321a92eb9fd0dd26203`
- proof tree：`1ec3ba0eee387938878156d5d76fb1e396e54938`
- 实际成功专项 CI 源：`e6d6d57323cc358cef060fb243ec386c13cb662d`
- 本次 P0 集成起点：`28fd630ef7cc38eba86beb6c0ba123336b5d05f2`
- 共同证明基线：`1a80c1bcce67886f699d097fc37fd245cd3620bf`
- 冻结手稿：`ba6ec11d800eccc54406490631895e174de85766`

101bb 仅比 e6d6 修改 ROUND3_HANDOFF.md，记录已有成功 CI 并纠正旧区间宽度笔误。
e6d6 是 proof f0c0 的元数据后继；所有 41 个 gate source_inputs 与固定 proof
Git blob 一致。完整 487 个提取文件均匹配固定 head 的 Git blob，检查前后不变。

## 三个新生产模块与真实门

| 模块（ImbalancedChen.Certificates.） | 所属声明 | strict / 秒 | stock replay / 秒 |
|---|---:|---:|---:|
| PairedV2Batch4To64Data | 72 | 7.281 | 4.014 |
| PairedV2Batch4To64 | 207 | 222.062 | 18.479 |
| PairedV2Prefix64 | 121 | 36.238 | 36.114 |

原始完整 audit 138.067 秒，所有 12 个 P2 模块共 709 项，其中旧 309 项完整
编译器记录逐条不变，新 400 项均通过。每个最终 strict/replay/audit 退出 0，
只使用固定官方 frontend、trustLevel=0、warningAsError=true、原装 leanchecker。
原始 gate 中 source/shared/local_producer 前后相等，重放前后对象相等，
独立重建的新 3 模块依赖闭包加最终 audit 共核对 50 个实际导入对象绑定。
原始 7 段验收运行串行，audit 在生产门之后。

| 模块 | 源 SHA256 | 生产者对象 SHA256 |
|---|---|---|
| Data | `4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c` | `61b3d3eeef416c6293ebdba0b5b1ac89a1d0d44e99be316f6139c2d51d60b259` |
| Batch | `c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4` | `6beb6f075f9d8539026bdd18716d9f3e6175a7253ec04244f7b1f8bf80637562` |
| Prefix64 | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` | `43adce492a503e2fc3bae8ab1d5f1e2586f17f20307bb1bc78258a2810436bca` |

生产对象字节没有内嵌在本 CI ZIP；这里的对象结论来自原始编译、重放、审计
哈希与输入绑定。CI 另外实际编译、重放并审计相同的固定源码；没有声称 ZIP
保存了所有 .olean。

## 实际专项 CI

[run 38252572597](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38252572597)，
job 114822365913，attempt 1，head e6d6d57323cc358cef060fb243ec386c13cb662d：
实际 completed / success。

| 阶段 | 真实范围 | 时间 |
|---|---|---:|
| Explicit build + strict | 12 个指定模块，均有 Built 与 strict 日志 | 239 秒 |
| 原装 replay | 12 个确切模块，逐个 exact replay marker | 104 秒 |
| Owned audit | 709 项，全部 pp.all 类型及标准公理依赖 | 43 秒 |

实际 Lean 为 4.33.0-rc1，commit 62eed1db4d67327ec8120be05f1a1b0847d74561。
11 个依赖 pin 及工具链、lakefile、手稿 map、EXTERNAL_REUSE、
CurrentMainTheorem、CurrentNumericalTransfer 与 P0 集成起点字节一致。

- artifact 11749278994，260451 bytes，41 个成员；
- ZIP SHA256：
  `4f0b9cc1232226392515eda5ccf880a40241cc5afc8d6defcbac45206089d663`；
- 180 个 CI 源输入对 CI commit 与交接 head 共 360 项字节检查通过；
- 709 条记录在原始 producer audit log、CI axioms.log、CI declarations.json、
  下载的完整 CI job log 中逐条相等；
- 所属公理声明与 unsafe 声明为 0；
- 传递公理并集仅 propext、Classical.choice、Quot.sound。

这些是 P2 专项验证，P0 新集成 SHA 的根构建/根内核/根审计需由 P0 另行执行。

## 采用数据、界和不重计

冻结 same-mask-v2 原文件 SHA256：
`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。
原字节 CRLF 3604398 bytes 保留。七字段 LF 行流：

| 原始范围 | bytes | SHA256 |
|---|---:|---|
| [0,4) | 457 | `96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235` |
| [4,64) | 6930 | `86c9f08228f08e98a9f1467fc353f1f01bdb5878e0d01e8a678debc664c661ab` |
| [0,64) | 7387 | `f89caa496a9672c1dc9285a22f1e010008a0d6ea6e9ff850fb09747586afaaf9` |

旧流串接新流与累计流逐字节相等。新行全部 E0、discarded floor 为 0；保留原
Q160 字段，但不把原存储上下界当作 Lean 证明假设。新批每行先由实际
PairedIntegralCertificate.check 认证，再由 check_sound 对接 rowIntegral；
总界调用 sum_check_sound。

| 实际积分和 | 下界 | 上界 |
|---|---|---|
| 旧 Prefix4 | 12676565261567 / 10^20 | 12676572571081 / 10^20 |
| 新 Batch4To64 | 190579962282066 / 10^20 | 190580072663307 / 10^20 |
| 累计 Prefix64 | 203256527543633 / 10^20 | 203256645234388 / 10^20 |

每个 rowIntegral 是原 pairedLocalIntegral：
K/80 乘以 (t,u,z,w) 四重积分，核 1/(t*u*z^2*w)。
K=8452171/1250000、a=417/5000、h=19/125、d=59/250、mu=25/128 均原值。
K/80 已含 Chen 的 1/4 与 Buchstab 的 1/20，仅使用一次。

Prefix64 的 rowIndices、rowZ、rowOrdinal 由 Fin.append 拼接；
prefixIndex=Fin.castAdd 60，batchIndex=Fin.natAdd 4。证明原始行号范围不交、
覆盖恰为 n<64，且 rowOrdinal i=i.val。63 个相邻整数键不等式经
Fin.strictMono_iff_lt_succ 推出实际 rowIndices 单射，因此有限采用行和实际
网格索引均不重复。真实积分按 Fin.sum_univ_add 分解：

```lean
theorem integral_eq_parts :
  integral = Prefix4.integral + Batch4To64.integral
```

累计界只加旧 4 行与新 60 行各一次，旧首格不再次加入。实际积分有限和的关系
已经证明；几何并域不交、完整历史 mask 身份及 prime-box 边界身份尚未因此证明。

## 完整接口与精确输出格式

- NEW_400_COMPLETE_TYPES.json：全部新增 400 项真实 pp.all 字段与便读字段。
- KEY_INTERFACES_COMPILER.json：19 个关键接口，保留原完整 pp.all。
- KEY_INTERFACES_COMPILER.md：这 19 项的实际编译器便读输出；隐式参数、实例、
  Fin 域等全部细节以同名 JSON 的 type 字段为准。
- 固定源码原始完整输出：fixed-source/verification/part2/round3/batch4-to64/
  compiler-types.json（709 项）以及 key-theorem-types.txt。

本批不使用“源码声明头”等价替代编译器确认。实际检查了审计源的 pp.all、
pp.proofs、pp.deepTerms、足够打印预算与 private/generated 的 declaring-module
枚举，所有 type/readable_type 都非空且无省略标记。

## 最小接收清单

MINIMAL_RECEIVE_FILES.json 给出完整路径、源提交、字节数、Git blob 与 SHA256。

**必须新增：**

1. ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean
2. ImbalancedChen/Certificates/PairedV2Batch4To64.lean
3. ImbalancedChen/Certificates/PairedV2Prefix64.lean

以上三源取自 proof f0c00f9，和 e6d6/101bb 同字节。旧九模块、data 输入不用修改。
公共根三个 import 和 P0 新统一 audit 的计数仅由 Part 0 编辑。

**需要扩展 owner 工具时可更新：**

- verification/part2/generate_paired_prefix.py：
  `45dcd50cd60f00bc676f5a2510a613b790a94eab17757f1147fb0129b0a3ab3f`
- verification/part2/CertificateAudit.lean：
  `78d45ffba85b40aa9f52e01f95473db904c270fbd299dea42f649a9572336d00`

生成器默认前四行代码与旧报告保持原字节；新增 --start 4 --count 60。
新 owner audit 显式覆盖全部 12 个模块、709 声明。

**按原件归档而不直接覆盖旧验收：**

- 新 verification/part2/round3/ 和 docs/part2/ROUND3_HANDOFF.md；
- 新 check.sh / 专项 workflow 的固定源可随证据归档；
- ROUND2_HANDOFF 和旧 prefix4 receipt 的后继仅补固定 proof/tree 元数据；
  P0 保持原接收件原字节，并保留后继作为独立证据。

新的原始 verify_acceptance.py 故意锁定完整 P2 父 424 文件，只能在固定 P2
提取树执行。P0 公共根已改，直接调用这个 receiver 或前置调用它的新 check.sh
会产生范围不符；不要删减检查来让它在混合树“通过”。P0 可将固定接收回执
复用，并由自己的新增模块显式构建/根审计/完整类型门覆盖整合。

## 已保留的第一处失败及修复归属

第一处真实 Lean 诊断位于旧 Prefix64 attempt 源 SHA256
ab9cf26bddd2a5734e9aefe5185e2740e315a9b6fa76ffe1bc02a47af340f1ae：

```text
PairedV2Prefix64.lean:142:0: error: (deterministic) timeout at whnf,
maximum number of heartbeats (200000) has been reached
```

随后 rowKey_adjacent 缺失触发一条下游 unknown constant；完整原始文字及位置
在 FIRST_DIAGNOSTICS.json 和原始 attempt log。P2 仅给该 63 项相邻检查定理
增加有限 maxHeartbeats 1000000，固定源码已通过 strict/replay/audit。

更早 Data frontend 虽 exit 0，但 shared 清单在运行中从 15 扩为 21 个键，
guard 报 shared_cache_changed；该次不接收。另一次 replay/audit 交叠被 P2
中断排除，原始中断记录保留，之后两门顺序重跑。P0 没有中断它们，也没有
把这些未验收尝试计作成功。本次 P0 生产证明修复为 0。

## 接收方与未闭合输入

Part 5 可以消费新增 60 项 B 的实际积分和下界，或消费累计 64 项完整区间。
Part 1 / Part 5 仍须将这组采用区域与历史 parent 限制、真实计数对象和
pairedLocalIntegral 相连。Part 2 自己可复用这一可追加层；Part 0 可整合三个
已核验叶模块。Part 4-A 的上界证书范围本轮没有扩展。

仍缺：E0 [64,6091)、E1 [6091,17572)、saved-floor 真实 estimator、
完整几何并域及历史许可、误差支付、完整 K/c 解析支持、hLower、hUpper。
P5 依赖 P4-A，不依赖 P4-B。没有把缺口包装成新的结构或类型类。

## 可直接执行的纯证据接收入口

本目录已经保留固定提取树、原始 CI ZIP、API 元数据和原始 job log：

```bash
python3 -B verify_intake.py \
  --git-repo /path/to/goldbach-formalization \
  --evidence-dir /path/to/p2-intake
```

verify_intake.py 只读取固定 Git 对象，核对原始证据，再执行固定提取树中已检查
的纯 Python receiver；它不运行 Lean、Lake、leanchecker、生成器、CI、网络，
不修改 Git ref 或集成源码。P2_INTAKE_RECEIPT.json 是这次实际运行的回执。

