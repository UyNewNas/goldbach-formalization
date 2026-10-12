# Part 2 第三轮交接：追加 E0 原始第 4—63 行，累计前 64 行

## 1. 本检查点的完成范围

**本轮新增认证原始零基行 `[4,64)`，共 60 行；与已验收 `[0,4)` 的 4 行合并，得到 `[0,64)` 共 64 行真实四重积分有限和的有理上下界。三个新增生产模块均通过固定官方 frontend 的严格编译和原装 leanchecker 重放；全 12 模块审计覆盖 709 个所属声明，其中旧 309 条完整编译器记录逐条不变，新增 400 条全部通过。**

本轮在这一个批次结束。第 64 行及之后没有计入认证数量。E1、saved-floor 语义、完整历史并域、算术父许可、全部 17,572 行、完整 K/c、hLower/hUpper 的状态保持第二轮结论。

| 版本 | 固定身份 |
|---|---|
| 本轮接收的真实分支头 | `076473720210ee602e6e9735902e16bb6c5f1398` |
| 本轮固定证明提交 | `PENDING_PROOF_COMMIT` |
| 旧九模块固定证明提交 | `6acf61cc28f227a9154363f2347c386ec01dffb0` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 冻结手稿 | `ba6ec11d800eccc54406490631895e174de85766` |
| 分支 | `chatgpt/chen-p2-certificates` |
| Lean | `leanprover/lean4:v4.33.0-rc1`，githash `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| Mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| goldbach | `09b97db5764ade1246bfb77206baa1b124760958` |

交接元数据由固定证明提交的后继提交绑定；所有生产源码和门的身份在绑定前后相同。本轮没有更新锁文件、共同基线、手稿 map 或其他 Part 的源码。发布前已逐项核对接收头的 424 个 Git blob。父提交中仅四个已有 Part 2 工具文件改变：生成器、专项 workflow、CertificateAudit 和 check.sh；九个旧生产源及第二轮全部 94 个历史证据文件均保持原字节。

入口：[本轮总回执](../../verification/part2/round3/batch4-to64/receipt.json)、[接收校验器](../../verification/part2/round3/batch4-to64/verify_acceptance.py)、[精确追加账](../../verification/part2/round3/batch4-to64/append-ledger.json)。旧结果仍以 [ROUND2_HANDOFF.md](ROUND2_HANDOFF.md) 和 [采用目录](ADOPTED_EVIDENCE_CATALOG.md) 为准。

## 2. 准确采用数据及范围

唯一数值输入为冻结手稿采用的 `corpus-renewal-paired-certificate-v2-20261010.json`，本仓库原字节副本位于 [verification/part2/data/](../../verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json)。

| 身份或行流 | 字节数 | SHA256 / Git blob |
|---|---:|---|
| 完整 CRLF 源文件 | 3,604,398 | SHA256 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7` |
| 完整源文件 Git blob | 同上 | `49499697cca96de5f7b779e95077874ce5f9d119` |
| 旧 `[0,4)` 的 LF 七字段流 | 457 | `96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235` |
| 新 `[4,64)` 的 LF 七字段流 | 6,930 | `86c9f08228f08e98a9f1467fc353f1f01bdb5878e0d01e8a678debc664c661ab` |
| 累计 `[0,64)` 的 LF 七字段流 | 7,387 | `f89caa496a9672c1dc9285a22f1e010008a0d6ea6e9ff850fb09747586afaaf9` |

LF 行流严格按原 JSON 顺序，将原七字段用逗号连接，每行末尾追加一个 LF。它没有把 CRLF 源文件重新规范化后冒充原文件哈希。`旧4行流 || 新60行流 = 前64行流` 已作逐字节比较。

字段顺序保持 `group,t_index,u_index,exact_Z,discarded_floor_Q80,extra_lower_Q160,extra_upper_Q160`。后两项分别表示原整数除以 `2^160`；discarded floor 是原整数除以 `2^80`，转 Chen 单位另有 `/4`。本批原始 floor 全为 0。原 Q160 端点只保留为来源字段，未作为新积分界的证明假设。

新批开头是原始第 4 行 `(423,511)`、`Z=1901547/13312000`；结尾是原始第 63 行 `(430,505)`、`Z=76092309/532480000`。原始第 64 行 `(430,506)` 被排除。新批内部 `Fin 60` 的值 0 对应原始 ordinal 4；`rowOrdinal i = 4+i.val`，证书名为 `certificate0004` 至 `certificate0063`。

每行的原始七字段、全局编号、实际坐标、cutoff、E0 端点残量、三组对数端点和最终单元界都记录在 [generated-report.json](../../verification/part2/round3/batch4-to64/generated-report.json) 的 `decoded_rows` 中。60 行全部满足 E0 和既有几何条件。原始行 4、9、15、23、32、43、55 有 `uUpper=h`，按已验收开纤维端点约定合法；没有为避开这些端点跳过行。

## 3. 实际积分、检查器和精确界

常量仍为

```text
a = 417/5000, h = 19/125, d = 59/250, mu = 25/128
K = 8452171/1250000
dt = 651/8192000, du = 343/2560000
```

对原始行索引 `(i,j)`，按 `(t,u,z,w)` 的坐标顺序使用

```text
tl = mu+i*dt, tr = mu+(i+1)*dt
ul = a+j*du,  ur = a+(j+1)*du
Z  = min(ul, 3*(1-tr-ur)/13)
```

每项是既有 `pairedLocalIntegral`，即

\[
\frac K{80}\int_{tl}^{tr}\int_{ul}^{ur}\int_a^Z\int_a^z
\frac{1}{tuz^2w}\,dw\,dz\,du\,dt.
\]

真实开纤维为 `tl<t<tr`、`ul<u<ur`、`a<w<z<Z`。`E0Geometry` 的已证正确性给出顺序、非空性以及整个纤维上的 Buchstab 参数至少 `7/3`。积分接口和几何接口未假设任何最终增益。

`K/80` 已经包含 `1/20` 与 Chen 的 `1/4`，只使用一次；没有追加归一化或排列因子。通用闭式仍是

\[
\frac K{80}\log(tr/tl)\log(ur/ul)
\left(\frac1a-\frac{1+\log(Z/a)}Z\right).
\]

生成器复用既有精确有理对数算法。外层两个对数各用 1 项，`log(Z/a)` 用 6 项；对数在 `10^15` 尺度向外舍入，单元值在 `10^20` 尺度向外舍入。负号中的 `log(Z/a)` 使用正确方向的界，乘积检查包含所有必要非负性。

每行 `rowNNNN_checked` 的证明项先通过实际 `PairedIntegralCertificate.check`。`certificate_inputs` 把证书字段识别为该原始采用行的真实参数；`rowIntegral_eq_certificate` 识别实际积分；`rowIntegral_bounds` 逐行应用已验收 `check_sound`。新批总界直接使用已验收 `PairedIntegralCertificate.sum_check_sound`。

| 已认证真实积分和 | 原始范围 / 行数 | 精确下界 | 精确上界 |
|---|---|---|---|
| `Prefix4.integral`，复用旧验收 | `[0,4)` / 4 | `12676565261567/10^20` | `12676572571081/10^20` |
| `Batch4To64.integral`，本轮新增 | `[4,64)` / 60 | `190579962282066/10^20` | `190580072663307/10^20` |
| `Prefix64.integral`，累计 | `[0,64)` / 64 | `203256527543633/10^20` | `203256645234388/10^20` |

Lean 中新批下界约分为 `95289981141033/50000000000000000000`，累计上界约分为 `50814161308597/25000000000000000000`。累计区间的十进制端点是精确有限小数 `[0.00000203256527543633, 0.00000203256645234388]`。

新批区间宽度为 `110381241/10^20`；旧四行宽度为 `7319514/10^20`；累计宽度为 `117690755/10^20`。`append-ledger.json` 保存未舍入对数乘积区间宽度、下端向外舍入量、上端向外舍入量及三者精确相加的完整有理账。每侧 60 次单元舍入总量严格小于 `60/10^20`。本批采用精确积分恒等式，没有新增数值求积误差。上述区间宽度已包含所用对数余项及有理向外舍入；没有在最终上下界外重复加减该宽度。

## 4. 可追加关系与有限不重计

累计模块使用标准 `Fin.append`，旧批嵌入为 `Fin.castAdd 60`，新批嵌入为 `Fin.natAdd 4`。已证明两个原始 ordinal 范围不交，联合恰好为 `n<64`，而且累计 `rowOrdinal i=i.val`。因此局部数组下标与原始行号的关系明确保留。

实际网格索引另有独立证明：整数键 `512*t_index+u_index` 的 63 个相邻差全部严格为正，利用通用 `Fin.strictMono_iff_lt_succ` 推出 `rowIndices` 单射。这同时排除了批内重复和两批之间的实际格子重复。

`Prefix64.rowIntegral` 从拼接后的真实坐标定义，不定义为已存证书数值。两个限制定理把它分别识别为旧批和新批的 `rowIntegral`，再用通用 `Fin.sum_univ_add` 得到

```lean
theorem ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts :
    Prefix64.integral = Prefix4.integral + Batch4To64.integral
```

其累计界只使用旧 `Prefix4.integral_bounds` 与新 `Batch4To64.integral_bounds` 的相加，没有重新生成或重证旧四行数值检查，也没有再加一次首格收益。标准有限元组和有限和 API 就是可复用追加层，没有另建无关积分模型。

这里的不重计是**有限采用行和实际网格索引的不重计**。没有声称已证明几何并域互不相交、原始半开 prime-box 边界身份或完整 mask 积分身份。

## 5. 关键已验收定理类型

以下用通常 Lean 记法，`open` 只缩短已固定命名空间。全部 709 个声明的 `pp.all` 完整编译器类型保存在 [compiler-types.json](../../verification/part2/round3/batch4-to64/compiler-types.json)，全部便读类型在 [compiler-readable-types.txt](../../verification/part2/round3/batch4-to64/compiler-readable-types.txt)；17 个接口的编译器原文另见 [key-theorem-types.txt](../../verification/part2/round3/batch4-to64/key-theorem-types.txt)。

```lean
open ImbalancedChen.Certificates
open ImbalancedChen.Certificates.PairedV2

theorem Batch4To64.rowOrdinal_range (i : Fin 60) :
    4 ≤ Batch4To64.rowOrdinal i ∧ Batch4To64.rowOrdinal i < 64

theorem Batch4To64.certificates_checked (i : Fin 60) :
    (Batch4To64.certificates i).check = true

theorem Batch4To64.geometry_checked (i : Fin 60) :
    E0Geometry (Batch4To64.rowIndices i).1
      (Batch4To64.rowIndices i).2 (Batch4To64.rowZ i)

theorem Batch4To64.certificate_inputs (i : Fin 60) :
    (Batch4To64.certificates i).K = K ∧
    (Batch4To64.certificates i).a = a ∧
    (Batch4To64.certificates i).tl = tLower (Batch4To64.rowIndices i).1 ∧
    (Batch4To64.certificates i).tr = tUpper (Batch4To64.rowIndices i).1 ∧
    (Batch4To64.certificates i).ul = uLower (Batch4To64.rowIndices i).2 ∧
    (Batch4To64.certificates i).ur = uUpper (Batch4To64.rowIndices i).2 ∧
    (Batch4To64.certificates i).Z = Batch4To64.rowZ i

theorem Batch4To64.rowIntegral_eq_certificate (i : Fin 60) :
    Batch4To64.rowIntegral i =
      pairedLocalIntegral ((Batch4To64.certificates i).K : ℝ)
        (Batch4To64.certificates i).a (Batch4To64.certificates i).tl
        (Batch4To64.certificates i).tr (Batch4To64.certificates i).ul
        (Batch4To64.certificates i).ur (Batch4To64.certificates i).Z

theorem Batch4To64.rowIntegral_bounds (i : Fin 60) :
    ((Batch4To64.certificates i).lower : ℝ) ≤ Batch4To64.rowIntegral i ∧
      Batch4To64.rowIntegral i ≤ ((Batch4To64.certificates i).upper : ℝ)

theorem Batch4To64.integral_bounds :
    (Batch4To64.lowerBound : ℝ) ≤ Batch4To64.integral ∧
      Batch4To64.integral ≤ (Batch4To64.upperBound : ℝ)

theorem Prefix64.source_ranges_disjoint (i : Fin 4) (j : Fin 60) :
    Prefix4.rowOrdinal i ≠ Batch4To64.rowOrdinal j

theorem Prefix64.source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 4, Prefix4.rowOrdinal i = n) ∨
      (∃ i : Fin 60, Batch4To64.rowOrdinal i = n)) ↔ n < 64

theorem Prefix64.rowIndices_injective :
    Function.Injective Prefix64.rowIndices

theorem Prefix64.prefix_batch_indices_disjoint (i : Fin 4) (j : Fin 60) :
    Prefix4.rowIndices i ≠ Batch4To64.rowIndices j

theorem Prefix64.integral_eq_parts :
    Prefix64.integral = Prefix4.integral + Batch4To64.integral

theorem Prefix64.integral_bounds :
    (Prefix64.lowerBound : ℝ) ≤ Prefix64.integral ∧
      Prefix64.integral ≤ (Prefix64.upperBound : ℝ)
```

`Batch4To64.integral_semantics` 和 `Prefix64.integral_semantics` 分别把有限和完整展开为第三节的四重积分核，项数为 `Fin 60` 和 `Fin 64`；编译器完整类型在上述文件中。它们与有限数值检查及通用检查器正确性共同形成实际积分认证，Python 读取或比较 JSON 不承担该数学结论。

## 6. 实际执行、源码和对象身份

| 新生产模块 | 所属声明数 | strict 秒数 | stock replay 秒数 |
|---|---:|---:|---:|
| `PairedV2Batch4To64Data` | 72 | 7.281 | 4.014 |
| `PairedV2Batch4To64` | 207 | 222.062 | 18.479 |
| `PairedV2Prefix64` | 121 | 36.238 | 36.114 |

最终三次 strict、三次 replay 和完整 audit 的退出码均为 0，全部输入稳定性门通过。验收记录的时间段按串行顺序执行，审计位于生产门之后。完整 12 模块 audit 用时 138.067 秒，覆盖 709 声明；含 private/generated，传递公理依赖仅 `propext`、`Classical.choice`、`Quot.sound`，新增公理声明和所属 unsafe 声明为 0。

| 模块 | 源 SHA256 | `.olean` SHA256 |
|---|---|---|
| `PairedV2Batch4To64Data` | `4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c` | `61b3d3eeef416c6293ebdba0b5b1ac89a1d0d44e99be316f6139c2d51d60b259` |
| `PairedV2Batch4To64` | `c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4` | `6beb6f075f9d8539026bdd18716d9f3e6175a7253ec04244f7b1f8bf80637562` |
| `PairedV2Prefix64` | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` | `43adce492a503e2fc3bae8ab1d5f1e2586f17f20307bb1bc78258a2810436bca` |

audit 对象 SHA256 为 `42542de7287d86afa125968ffd1f6f95907d9ab5b1da6011b0dbe860e7af6cc9`。各完整命令、环境、输入和输出哈希、退出码、内存、原始 log 均位于 [gates/](../../verification/part2/round3/batch4-to64/gates/)，运行输入和重定位链位于 [runtime/](../../verification/part2/round3/runtime/README.md)。

旧九模块的编译和重放复用固定第二轮验收；本轮没有重写那些回执，也没有宣称在本地重新编译旧九模块。联合 audit 对旧 309 条记录重新枚举并逐条比较。旧 Prefix4 接收器锁定九模块及当时工具字节，故先在修改前执行并保存 PASS；扩展后由新接收器核对固定历史范围和新的 12 模块范围。

未验收尝试完整保留于 [attempts/](../../verification/part2/round3/batch4-to64/attempts/)：初次 Data 遇到运行名单扩充导致稳定性 guard 拒绝；Prefix64 相邻检查初次达到默认 200,000 heartbeats 后，仅对该定理提高有限预算为 1,000,000；一次审计提前与尚未结束的 replay 交叠，被中断并排除，随后 replay 和 audit 均独立重跑。原始 receipt/log 不改写，调度排除记录另存 [scheduling-rejections.json](../../verification/part2/round3/batch4-to64/scheduling-rejections.json)。这些记录均不计入最终成功门。

## 7. 复现、专项 CI 与检查点

```bash
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --check-generated ImbalancedChen/Certificates

python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --start 4 --count 60 --check-generated ImbalancedChen/Certificates

python3 verification/part2/round3/batch4-to64/verify_acceptance.py

bash verification/part2/check.sh
```

前三条已实际运行成功。第一条同时核对旧默认前四行源码；另存的报告比较证明其旧报告也逐字节不变。第二条核对新两源和逐行报告。第三条校验来源和归档执行证据，不启动 Lean。最后一条是在通常支持环境中重新执行专项编译、重放和审计的入口，本地此次使用第六节的等价官方 frontend 入口逐模块运行；没有将命令清单本身当作执行成功。

`.github/workflows/part2-certificates.yml`、`check.sh` 与 `CertificateAudit.lean` 均显式列入三个新模块，实际生产清单严格要求旧九加新三共 12 模块。旧门槛保留：冻结工具链和依赖、所有生产文件精确覆盖、逃逸扫描、逐模块 `lake build`、strict elaboration、原装 replay、全声明及完整类型审计。专项 CI 还运行新批生成一致性和本轮归档接收校验。

**专项 CI 发布时状态：尚未触发本检查点的远端 run。** 本地三个独立数学验证门已经完成；发布后的当前 SHA、Actions run 和完成状态在最终交接中给出。旧检查点 CI 的成功不移用为本检查点成功，失败、跳过或中断也不计作通过。

## 8. 接收方与仍缺的最小接口

Part 5 可接收本轮 B 的 60 项新增实际积分和下界，以及前 64 项实际积分和双侧界。要把这个有限积分和识别为实际配对修正的一部分，仍需 Part 1 / Part 5 接上真实采用区域、历史 parent 限制、实际计数对象与 `pairedLocalIntegral` 的身份；本轮没有提供这些算术或并域前提。

Part 4 的 A 证书范围未扩展。已验收的 `AboveMuSecondCoarse` 等旧接口及采用目录保持原状态，same-mask-v2 的 17,572 行和 `7/3` 没有被解释成全部上界 K 证书。被替换的 `12/5` 增益、撤回的 `1.9728` 和旧首格均未重复加入。

本轮剩余未认证 E0 原始范围为 `[64,6091)`；本检查点没有自动继续该范围。E1 的 `[6091,17572)`、saved-floor estimator 的真实语义、完整历史并域和误差支付、全部 K/c 与最终 `hLower` / `hUpper` 均继续保留原来的待接状态。
