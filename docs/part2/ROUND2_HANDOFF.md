# Part 2 第二轮交接：已验收组件、实际积分与待接接口

## 1. 当前结论与版本

**本轮新增 E0 Geometry / Prefix4 三模块已各自通过严格编译与原版内核重放；联合公理审计实际覆盖全部 9 个生产模块、309 个所属声明。旧六模块的编译和重放按确切同源码复用 P0 验收，新三模块的编译和重放由本轮独立执行。已认证 B 的实际四格积分有限和以及 A 的采用粗双图积分，完整 mask 和完整 K/c 尚未闭合。**

下表的本轮证明提交在创建 Git proof commit 后绑定；其源码内容由本轮 receipt 中的 SHA256 精确标识。原证明基线和 `docs/CURRENT_MANUSCRIPT_MAP.md` 不在本 Part 修改范围内。

| 对象 | 完整 SHA / 当前状态 |
|---|---|
| 当前 P2 远程父提交 | `b2ecfdc74b1ebb17be8509c3664f3ca558538b3e` |
| 本轮固定证明提交 | `P2_PROOF_COMMIT_TO_BIND` |
| 接收的统一 P0 证明源码 | `278f949444748a30b5165ff47bfa283ab0bad0d8` |
| P0 原始验收证据提交 | `cce2334906f068fda2f58c400646366f2aa2d417` |
| P0 receipt 记录的原 P2 交接源 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 冻结手稿 | `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` |
| 锁定 Lean | `leanprover/lean4:v4.33.0-rc1` |
| 锁定 Mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| 锁定 goldbach | `09b97db5764ade1246bfb77206baa1b124760958` |
| 本轮新增 Geometry / Prefix4 | **3 模块独立严格编译和原版重放均 PASS；9 模块联合审计 309 声明 PASS** |

本文件更新 [首轮 HANDOFF](HANDOFF.md) 的验证状态。首轮文件中的“未编译候选”描述保留为当时记录；它不否定后来对确定源码取得的 P0 验收和本轮新模块验收。完整采用判断和误差总账仍以 [ADOPTED_EVIDENCE_CATALOG.md](ADOPTED_EVIDENCE_CATALOG.md) 及 [机器目录](adopted-evidence-catalog.json) 为准。

## 2. 六模块同源码验收

六个模块均位于 `ImbalancedChen/Certificates/`，共同通过 `PASS_STRICT_TRUST0`、`PASS_ORIGINAL_LEANCHECKER`、`PASS_OWNED_DECLARATIONS` 和源码保护检查。

| 模块 | 所属声明数 | 验收源 SHA256 |
|---|---:|---|
| `RationalLogCertificate` | 47 | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` |
| `PairedFibreIntegral` | 13 | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` |
| `PairedCertificateChecker` | 58 | `454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c` |
| `PairedV2Data` | 18 | `a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82` |
| `PairedV2` | 46 | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` |
| `AboveMuSecondCoarse` | 71 | `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2` |

253 个声明包含私有及编译器生成声明。传递公理依赖的并集仅有 `Classical.choice`、`Quot.sound`、`propext`；新增公理声明和所属 `unsafe` 声明均为 0。原始完整类型输出、每声明公理列表、源和目标 `.olean` SHA256 均已保存。

本节的 253 指 P0 既有验收批次。本轮对全部九模块重新执行联合所属声明公理审计，共 309 条；其中旧 253 条完整编译器记录与 P0 记录逐条全等。新增 56 条由 Geometry 的 10 条、Prefix4Data 的 11 条和 Prefix4 的 35 条构成。六个旧模块的编译和内核重放没有在本轮重新执行。

严格编译由原版锁定 Lake 调用官方 `Lean.Elab.runFrontend`，参数为 `trustLevel=0`、`warningAsError=true`，不使用 metadata adapter。原版 `leanchecker --verbose MODULE` 对六个指定生产模块逐一重放；没有声称 `--fresh` 全导入闭包重放。全声明审计按 defining module 枚举，审计程序本身经过严格编译；没有把该编译当作审计程序的内核重放。

各成功门的退出码均为 0，源和记录到的导入对象在门前后保持相同；编译产物与重放目标绑定一致。首格 182 条、粗积分 71 条完整类型记录与对应审计 log 逐条全等且未截断。接收工作区的六个源文件、生成器及锁定输入已与固定 P0 对象匹配。因此这六个旧模块的编译和重放验收方式为 `EXACT_SOURCE_UPSTREAM_REUSE`，不是重新编译六模块的声明，也不是整项目成功构建的声明。根 CI 的整项状态不改写这些逐模块的成功 receipt。

P2 父提交 `b2ecfd…` 中，只有 `PairedV2.lean` 本身与验收源相同；另外五文件需要接收 P0 修复。修复只涉及字段标型、结构排版、当前库中的积分定理名和证明步骤，没有改变有理数、积分定义、假设或定理命题。补丁逆向精确重建原源哈希，所有定理声明头保持相同。原未编译源没有可比较的成功编译产物；验收后的完整类型另附。

生成器 `verification/part2/import_paired_v2.py` 同步排版修复，验收 SHA256 为 `2f214ac7631f40ed1ca9016df0f155f3003d1ce23f6ecc847d202dc7bc779486`。P0 的 `--check-generated` 返回 0，生成结果正是上表 `PairedV2Data` 的验收字节。

证据入口为 [UPSTREAM_ACCEPTANCE.md](../../verification/part2/round2/upstream/UPSTREAM_ACCEPTANCE.md) 与 [UPSTREAM_ACCEPTANCE.json](../../verification/part2/round2/upstream/UPSTREAM_ACCEPTANCE.json)。保存了 40 个必要原始文件，957,558 字节；每项保留固定 Git blob、SHA256、原路径和本地映射。最终 ledger 仅派生提取六个 P2 条目，明确标注为投影，没有复制或冒充其他 Part 的完整记录。

## 3. B：已验收的实际 same-mask-v2 首格

### 3.1 原始数据与实际对象

采用数据是冻结手稿的 `verification/data/corpus-renewal-paired-certificate-v2-20261010.json`，本仓库按原字节保存于 [本地数据副本](../../verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json)。

- 原始 Git blob：`49499697cca96de5f7b779e95077874ce5f9d119`。
- 原始 SHA256：`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。
- 原文件是 CRLF；行流哈希另用指定 LF 协议，不与文件哈希混同。
- 七列：`group, t_index, u_index, exact_Z, discarded_floor_Q80, extra_lower_Q160, extra_upper_Q160`。后两列除以 `2^160`；saved floor 除以 `2^80`，转 Chen 单位时再除 4。

首格是原始零基序号 `0`、组 `E0`、索引 `(422,510)`，坐标按 `(t,u,z,w)` 排列：

| 参数 | 精确有理数 |
|---|---|
| `K` | `8452171/1250000` |
| `a` | `417/5000` |
| `tl`, `tr` | `937361/4096000`, `1875373/8192000` |
| `ul`, `ur` | `194217/1280000`, `388777/2560000` |
| `Z` | `76088109/532480000` |

实际开纤维为 `tl<t<tr`、`ul<u<ur`、`a<w<z<Z`，其中 `Z=min(ul,3*(1-tr-ur)/13)` 在外层端点冻结。证明采用真实四层 `intervalIntegral`，以 `K/80=K*(1/20)*(1/4)` 为系数；没有额外排列因子或因子 2。

### 3.2 已验收的完整证明链

以下类型使用 Lean 的便读记法；所有声明的原始完整编译器类型见 [首格 compiler-types.json](../../verification/part2/round2/upstream/p2-first/compiler-types.json) 和 [可读类型](../../verification/part2/round2/upstream/p2-first/compiler-readable-types.txt)。

```lean
theorem ImbalancedChen.Certificates.RationalLogCertificate.check_sound
    (c : ImbalancedChen.Certificates.RationalLogCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
      Real.log (c.argument : ℝ) ≤ (c.upper : ℝ)

theorem ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound
    (c : ImbalancedChen.Certificates.PairedIntegralCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤
        ImbalancedChen.Certificates.pairedLocalIntegral
          (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ∧
      ImbalancedChen.Certificates.pairedLocalIntegral
          (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ≤ (c.upper : ℝ)

theorem ImbalancedChen.Certificates.PairedV2.first_certificate_checked :
    ImbalancedChen.Certificates.PairedV2.firstCertificate.check = true

theorem ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics :
    ImbalancedChen.Certificates.PairedV2.firstIntegral =
      (((8452171 : ℝ) / 1250000) / 80) *
        (∫ t in (937361 : ℝ) / 4096000..1875373 / 8192000,
          ∫ u in (194217 : ℝ) / 1280000..388777 / 2560000,
            ∫ z in (417 : ℝ) / 5000..76088109 / 532480000,
              ∫ w in (417 : ℝ) / 5000..z, 1 / (t * u * z ^ 2 * w))

theorem ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤
        ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
      ImbalancedChen.Certificates.PairedV2.firstIntegral ≤
        (31704 / 1000000000000 : ℝ)
```

这形成了“具体证书检查通过 + 检查器正确性 + 实际对象语义等式 ⇒ 实际积分有理界”。其中通用积分闭式由真实积分恒等式推出；被减去的 `log(Z/a)` 采用上界，两个外层对数采用下界，并明确证明乘法所需非负性。

已验收区间为 `[3.1703e-8,3.1704e-8]`。这是独立较宽有理界，未声称证明了原 JSON 的更紧 Q160 区间。原 Q160 数字仍是来源字段，不是积分命题的假设。

## 4. B：已验收的 E0 Geometry / Prefix4 实际四格积分和

三个新增模块的独立门和联合审计结果记录于 [本轮 receipt.json](../../verification/part2/round2/prefix4/receipt.json)，状态为 `PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT`。完整门 receipt 和原始 logs 位于其 [gates/](../../verification/part2/round2/prefix4/gates/)；修复前尝试保留在 [attempts/](../../verification/part2/round2/prefix4/attempts/)。以下时间均为相应成功运行的记录值。

| 新模块 | 声明数 | 严格编译 / 原版重放秒数 | 已验收源 SHA256 |
|---|---:|---|---|
| `PairedV2Geometry` | 10 | `4.919 / 3.160` | `68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238` |
| `PairedV2Prefix4Data` | 11 | `3.696 / 3.105` | `25ffbba57b5fdff9ce23290ade00fbeaa2b38c2e44ffe9e8637404c8287aab2c` |
| `PairedV2Prefix4` | 35 | `7.675 / 3.496` | `dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395` |

本轮联合审计运行 `62.203` 秒，实际覆盖九模块 309 个所属声明。完整类型见 [compiler-types.json](../../verification/part2/round2/prefix4/compiler-types.json)，其可读原文见 [compiler-readable-types.txt](../../verification/part2/round2/prefix4/compiler-readable-types.txt)，关键声明摘录见 [key-theorem-types.txt](../../verification/part2/round2/prefix4/key-theorem-types.txt)。所有完整类型和公理记录均未截断，新增公理声明和所属 `unsafe` 声明为 0，传递公理依赖仍限三项标准公理。

实际前缀采用原 JSON 的第 `0..3` 行，全部为 E0：

| 原始零基序号 | `(t_index,u_index)` | `Z` | discarded Q80 |
|---:|---|---|---:|
| 0 | `(422,510)` | `76088109/532480000` | 0 |
| 1 | `(422,511)` | `1170333/8192000` | 0 |
| 2 | `(423,509)` | `9511851/66560000` | 0 |
| 3 | `(423,510)` | `9509793/66560000` | 0 |

选取行流 SHA256 为 `96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235`。[generated-report.json](../../verification/part2/round2/prefix4/generated-report.json) 使用 `10^15` 对数向外舍入和 `10^20` 单元向外舍入提供数值候选；本轮独立编译、内核重放和审计现已把其实际四项积分和认证为以下有理区间：

```text
lowerBound = 12676565261567/100000000000000000000
upperBound = 12676572571081/100000000000000000000
```

对象定义为 `Prefix4.integral = ∑ i : Fin 4, Prefix4.rowIntegral i`，每项使用该行实际端点的 `pairedLocalIntegral`。具体证书检查、实际行输入识别、真实积分语义和有理界均已验收。下列为便读的完整类型；代码块中 `open` 只缩短已列命名空间名称，对应原始编译器输出在上述文件中：

```lean
open ImbalancedChen.Certificates
open ImbalancedChen.Certificates.PairedV2
open ImbalancedChen.Certificates.PairedV2.Prefix4

theorem ImbalancedChen.Certificates.PairedV2.Prefix4.certificates_checked
    (i : Fin 4) : (certificates i).check = true

theorem ImbalancedChen.Certificates.PairedV2.Prefix4.geometry_checked
    (i : Fin 4) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i)

theorem ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral_eq_certificate
    (i : Fin 4) :
    rowIntegral i = pairedLocalIntegral ((certificates i).K : ℝ)
      (certificates i).a (certificates i).tl (certificates i).tr
      (certificates i).ul (certificates i).ur (certificates i).Z

theorem ImbalancedChen.Certificates.PairedV2.Prefix4.integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 4,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
        ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
          ∫ z in (a : ℝ)..(rowZ i : ℝ),
            ∫ w in (a : ℝ)..z, 1 / (t * u * z ^ 2 * w)

theorem ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds :
    (ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound : ℝ) ≤
        ImbalancedChen.Certificates.PairedV2.Prefix4.integral ∧
      ImbalancedChen.Certificates.PairedV2.Prefix4.integral ≤
        (ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound : ℝ)
```

`row0000_checked` 至 `row0003_checked` 为各行的实际数值检查提供独立证明项。`certificate_inputs` 与 `rowIntegral_eq_certificate` 识别采用行的参数和真实积分；`integral_semantics` 展开实际四重积分核，`integral_bounds` 应用已经验收的 `PairedIntegralCertificate.sum_check_sound` 与实际四行检查，推出上下界。没有把存储 Q160 值作为命题前提。

生成报告仍原样保留 `candidate_lower`、`candidate_upper`、`candidate_lean_status` 字段，其中 `candidate_lean_status` 为 `REQUIRES_SEPARATE_STRICT_COMPILE_KERNEL_REPLAY_AND_AUDIT`。这些字段描述生成器本身的职责；验收来自与生成源哈希绑定的后续成功 gate 和审计 receipt，不能仅凭生成报告的字段或存储数字判断。

Geometry 的有限条件不含任何积分收益：索引小于 512，`0<a<Z`，采用 cutoff 等式，`Z≤uLower`，外层宽度严格正，`uUpper≤h`、`h<tLower`、`tUpper≤d`，以及 E0 端点残量门 `57/64-(5/2)*tLower-uLower≤2*a`。已验收的正确性定理把这些条件传到整个开纤维，给出顺序、非空和 Buchstab 参数至少 `7/3`。

端点约定需要保持：最后一格的 `uUpper=h` 或 `tUpper=d` 可以满足开域内的严格不等式；`Z=uLower` 也允许。`a=Z` 和零外层宽度排除。该 E0 残量门只用于 E0，不能据此把 E1 重标为 E0。

**前缀含有原首格，不能将已认证的四格和与首格收益再次相加。** 它扩展对同一采用数据的认证范围。已证明的对象是上述真实积分有限和，没有断言它等于整 mask 的并域积分或完整配对增益。

17,572 行的全量认证仍未闭合：其中 E0 共 6,091 格，E1 共 11,481 格；当前四格前缀没有 E1。全量还需实际每格检查、E1 自己的合法性与 saved-floor 语义、覆盖和不重计身份、真实父限制及完整误差总账。Python 对全部行的解码、存储数字求和或候选精确算术不单独完成这些义务。

## 5. A：已验收的采用粗双图积分

此模块处理 A 的第 5 项 `above_mu_second_coarse_only`。采用来源是冻结的 `second-prefix-upper-fallback-independent-review-20261009.json:no_grid_coarse_lower`，值为 `640339/15210735000`；更大的 2,048 格 fine-grid 结果没有作为额外收益采用。

冻结解析原文 [second-prefix-upper-fallback-20261009.tex](../../verification/part2/data/second-prefix-upper-fallback-20261009.tex) 的 SHA256 为 `355954ab0d4d1d23ce6045a4baa2dee3b71f124a8550e8f1eae71fbcae70821d`；[small review JSON](../../verification/part2/data/second-prefix-upper-fallback-independent-review-20261009.json) 的 SHA256 为 `6aa6886728dfa9ddb7bdaa97727067eb040bb592ba65fa7ddceda3a51a437c45`。二者都按冻结原字节保存。

物理域为 `mu<x<rho`、`25/32-3*x<y<x`，`mu=25/128`、`rho=19/96`、`step=1/384`。两张图的参数 `k=-3,1`、`0<u,v<1` 对应：

```text
x  = (75+u)/384
y  = (75+k*u*v)/384
Ro = (159-5*u-2*k*u*v)/768
Rn = (159-2*u-(2*k+3)*u*v)/768
```

实际图核为 `6*abs(k)*step^3*u^2*(1-v)/(x*y*Ro*Rn)`。已验收证明在整个闭方块上建立正分母和粗分母上界，再对真实分子和函数积分，给出：

```lean
theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower :
    (3 / 95000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral (-3)

theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower :
    (32 / 3042147 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral 1

theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

完整类型和审计证据见 [粗积分 compiler-types.json](../../verification/part2/round2/upstream/p2-coarse/compiler-types.json) 和 [可读类型](../../verification/part2/round2/upstream/p2-coarse/compiler-readable-types.txt)。实际 endpoint min 分支、旧/新 residual、物理核带指定 Jacobian 的逐点 pullback 等式也在该模块验收范围内。

仍未完成的是物理域单积分与这两张图积分之间的换元、覆盖和边界身份，以及它与实际普通筛密度、旧树、同一算术 rho 的识别。逐点 pullback 等式不替代积分换元。该项是上界政策中的一个节省项，在 `E` 中带负号；一个节省项的下界不能冒充全部 `K` 的上界证书。A 的其他 compact complete-record 仍可能只含总量、盒号或 stream hash，不能代替缺失的原盒、精确节点和几何 witness。

## 6. 不重计和完整误差总账

采用目录的 A 账式保持为

```text
E = 4/Theta + I1 + I3_compact + I3_full_small_tail - sum(G1,...,G22)
```

其后支付两份独立且相等的 reserve `u`。`I3_full_small_tail` 的整体替换只入账一次；粗界和 fine-grid 界估计同一量，不叠加。目录中的 `K-E-2u>0` 是已复核的精确有理关系；全部实际分量积分及两个实际误差界尚未接入，故完整上界政策仍未闭合。

下界采用关系为：

| 项目 | 精确值 |
|---|---|
| 当前额外 gross | `558583/1000000000` |
| 被替换的旧 saved-floor 损失支付 | `1186047/500000000` |
| 新 saved-floor 损失支付 | `466977/200000000` |
| 损失回收 | `37209/1000000000` |
| 原始增量 `Delta` | `37237/62500000` |
| 每份 reserve 的增加 `Delta/8` | `37237/500000000` |
| 两份 reserve 后净增量 `3*Delta/4` | `111711/250000000` |

17,572 格与 `7/3` 只属 B 下界采用数据。`7/3` 替换原 `12/5` 增量，旧 E0/E1 gross 和被替换的 whole-box restoration 不重加，撤回分支 `1.9728` 不使用。后续 feedback 只有额外 gross 除以 `K` 进入斜率；saved-floor 损失回收不按同一方式除以 `K`。这些采用语义不因首格或前缀的局部认证而新增收益。

字面 discarded Q80 和为 `11290806845175652020270`；E0 floor 全零，E1 中另有 227 个 crossing 零 floor。此支付对应丢弃的已保存正估计器，不自动成为真实被删除 Y6 计数的上界。对应恒等式、全部保留/替换项和两份实际 reserve 均须在接收侧闭合。

## 7. Part 1 接口仍待签署；最小待接类型

[PART1_INTERFACE.md](PART1_INTERFACE.md) 仍是单方提出的接口契约，没有 Part 1 会话签署或确认。P0 对独立分析模块的验收不等于 Part 1 已接受该接口，也不供应最终增益假设。下表只说明缺失命题的形状和责任，不引入公理或新的假设定义。

| 接收 Part | 已可接收的对象 | 最小仍需接入的命题/数据 |
|---|---|---|
| Part 0 | 六个固定源码组件同源码验收、本轮三模块独立门和九模块联合审计 | 按固定 proof commit 接收；完整 root 的结果单列 |
| Part 1 | 实际迭代纤维积分、已验收通用解析/检查器；A 两图积分和逐点 pullback | 明确实际历史 joint-cell/区域/策略字典；若需并域积分，证明 Fubini、边界与不交覆盖；A 物理域换元；算术所有权与实际许可条件 |
| Part 4-A / Part 4-B | A5 两图积分粗下界及完整 A 采用目录 | 实际 ordinary parent / old tree / 同一 rho 身份；其余采用分量；真实 signed upper ledger；rough-cutoff 尾项、严格有限缓冲、极限顺序和两份 reserve |
| Part 5 | 已验收 B 首格及含首格的实际四格积分和；有限和检查器；全量原始数据 | 其余实际行检查与 E1 语义；Buchstab `11/20` 下界及其 `7/3` 应用；Y6/Y11 配对、实际父限制、saved-estimator 身份、全 lower ledger 与两份 reserve |

所需输入可以是“在显式可积、覆盖、端点和许可条件下，实际对象等于这些积分”的定理，不能是预先假定最终 `gain`、完整 `K/c` 或期望积分数值。普通 fifth-prefix 的既有身份不能代替完整历史策略的 joint-cell 身份。当前未供应完整 `hLower` 或 `hUpper`。

## 8. 实际验证记录与复核入口

本轮已运行的同源码接收检查记录为 [RECEIVING_VERIFY_RESULT.json](../../verification/part2/round2/upstream/RECEIVING_VERIFY_RESULT.json)，退出码 0，状态 `PASS_EXACT_SOURCE_UPSTREAM_REUSE`。可从任意工作目录复核：

```sh
python3 verification/part2/round2/upstream/verify_upstream_acceptance.py
```

该脚本只校验归档、当前源和锁定输入、receipt/log/类型/公理记录与 ledger 投影，不调用 Lean。真正的六模块 Lean 编译与内核结果来自固定 P0 原始 receipt。

新增 Geometry / Prefix4 的独立严格编译和原版内核重放各 3 次均已通过；本轮 `CertificateAudit` 实际审计全部 9 个生产模块，共 309 个声明。完整结果和对象绑定见 [prefix4/receipt.json](../../verification/part2/round2/prefix4/receipt.json)。本轮的 [接收检查记录](../../verification/part2/round2/prefix4/receiving-checks/receipt.json) 还记录首格数据重解码、前缀数据重解码和 P0 验收接收检查均返回 0；这些 Python 检查不替代 Lean 门。

本轮接收复核脚本也已通过，命令为：

```sh
python3 verification/part2/round2/prefix4/verify_acceptance.py
```

该脚本读取固定 receipt、当前源码与锁定输入、生成报告和完整类型；检查新三模块的编译/重放源对象绑定，以及本轮完整审计中旧 253 条记录与 P0 原记录逐条全等。复核脚本不调用 Lean；其成功表示已记录的真实门与当前确切源码一致。本次文档更新又只读复查三份源 SHA256、receipt 所列归档 SHA256、309 条完整类型、公理名单和旧 253 条一致性，全部相符。

验收范围没有扩大到普通 `lake build`、`--fresh` 全导入闭包重放、全部 17,572 行、完整历史 mask、完整 K/c 或 `hLower` / `hUpper` 供应。物理域换元、并域身份、算术父许可和总账接口仍按 §5–§7 明列。
