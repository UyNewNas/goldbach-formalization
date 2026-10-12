# Part 2：Part 0 固定源码验收接收记录

## 结论与固定版本

本记录复用 Part 0 对 **6 个生产模块、253 个声明**的既有严格编译、原版内核重放与全声明公理审计。接收时已独立核对原始证据字节、源文件及目标对象绑定、完整类型输出和最终 ledger 的 P2 条目；当前接收工作区的 6 个 Lean 文件、生成器和锁定输入均与已验收对象相同。验收方式为 `EXACT_SOURCE_UPSTREAM_REUSE`，本轮没有重新调用 Lean 编译或内核重放。

| 项目 | 固定完整 SHA |
|---|---|
| 接收的 P0 证明源码 | `278f949444748a30b5165ff47bfa283ab0bad0d8` |
| 原始 P0 证据提交 | `cce2334906f068fda2f58c400646366f2aa2d417` |
| 修复前 P2 最新提交 | `b2ecfdc74b1ebb17be8509c3664f3ca558538b3e` |
| P0 receipt 记录的原 P2 交接源 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 冻结手稿 | `ba6ec11d800eccc54406490631895e174de85766` |

首格五模块最初接受于 P0 `c9f407efe66240c08c2e8a678330ba7b98b74db5`，粗积分模块最初接受于 `5e31713690daba5ff926da61875a99171718fd1d`。接收采用上述统一证明提交 `278f949…`；其六个源码的 Git blob 与证据提交 `cce233…` 完全相同。修复前 P2 提交只有 `PairedV2.lean` 与验收源相同；其余五文件必须接收修复字节后才可复用验收。已完成该接收核对。

## 逐模块源文件与结果

以下每个模块均为 `PASS_STRICT_TRUST0`、`PASS_ORIGINAL_LEANCHECKER`、`PASS_OWNED_DECLARATIONS`，源码检查也通过。文件均位于 `ImbalancedChen/Certificates/`。

| 模块 | 所属声明数 | 已验收源 SHA256 |
|---|---:|---|
| `RationalLogCertificate` | 47 | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` |
| `PairedFibreIntegral` | 13 | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` |
| `PairedCertificateChecker` | 58 | `454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c` |
| `PairedV2Data` | 18 | `a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82` |
| `PairedV2` | 46 | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` |
| `AboveMuSecondCoarse` | 71 | `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2` |

253 个声明包含所属模块的私有及编译器生成声明。逐声明传递公理依赖的并集仅为 `Classical.choice`、`Quot.sound`、`propext`；新增公理声明为 0，所属 `unsafe` 声明为 0。逐项完整类型和公理列表保存在 [首格 compiler-types.json](p2-first/compiler-types.json) 与 [粗积分 compiler-types.json](p2-coarse/compiler-types.json)。两份 JSON 分别为 182 和 71 条，与原审计日志的 `P0_AUDIT_DECL` 记录逐条全等；模块计数也与 `P0_AUDIT_MODULE` 逐条全等，所有完整及可读类型均无省略符。

严格编译用锁定的 `leanprover/lean4:v4.33.0-rc1`：原版 Lake 调用官方 `Lean.Elab.runFrontend`，`trustLevel=0`，`warningAsError=true`，`metadata_adapter=false`；日志所报 Lean Git SHA 为 `62eed1db4d67327ec8120be05f1a1b0847d74561`。它是逐模块严格编译。内核重放命令为原版 `leanchecker --verbose MODULE`，对六个指定生产模块各执行一次，使用 receipt 中按 SHA256 记录的导入对象。未声称以 `--fresh` 重放整个导入闭包。公理审计源本身经过严格编译；没有把审计源的编译写成审计源的内核重放。

所有成功门的返回码均为 0；源 SHA256 前后相同，编译产物 SHA256 与重放目标相同，记录到的导入对象在门前后也相同。原始 log 首行对象、命令和源绑定与 receipt 相符。全工程 `lake build`、全根项目内核与公理门以及最终 `hLower` / `hUpper` 供应均不在本接收结论中；根 CI 的整项状态不改写这些独立模块的成功 receipt。

## 修复范围

完整原始补丁保存在 [p2-first/repairs](p2-first/repairs) 和 [p2-coarse/repairs](p2-coarse/repairs)。接收时将补丁逆向应用于验收源，逐份精确重建 receipt 中的原 SHA256 和 Git blob；该原 blob 亦与 `b2ecfd…` 的对应文件一致。全部定理声明头保持相同，补丁未更改数值数据、积分定义、假设或最终命题。具体改动为：

- `RationalLogCertificate`：证明 tactic 分行，并加入乘除归一化。
- `PairedFibreIntegral`：导数证明使用 `congr_deriv`，采用当前锁定库中正确的积分定理名，并调整证明步骤。
- `PairedCertificateChecker`：每个结构字段明确单独标型；修复加法保序证明的参数顺序。
- `PairedV2Data`：结构字面量按当前 Lean 解析器要求换行；有理数全部保持不变。
- `PairedV2`：没有源码变化。
- `AboveMuSecondCoarse`：积分减法指定参数，使用正确积分定理名，并修复证明 tactic 结构。

原始未修复源码不能全部编译，因此这里的接口对比是声明、参数和常数的源级核对。验收后的完整编译器类型另附；没有虚构一份旧源的成功编译产物来声称类型等同。

生成器同步接受同一排版修复，SHA256 为 `2f214ac7631f40ed1ca9016df0f155f3003d1ce23f6ecc847d202dc7bc779486`。P0 的 [生成器 receipt](p2-first/emitter/paired-v2-emitter-repair-receipt.json) 记录 `--check-generated` 返回 0，生成前后 `PairedV2Data.lean` 均为表中 `a9fa2f53…`；解码统计和所有算术常数未变。

## 已认证积分与语义边界

### B：实际 same-mask-v2 首格

原始采用 JSON 的 SHA256 为 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`，Git blob 为 `49499697cca96de5f7b779e95077874ce5f9d119`。采用的是 `E0`、零基 t 索引 `422`、u 索引 `510`，`Z = 76088109 / 532480000` 的首格。以下检查与语义等式共同支持积分结论：

- `ImbalancedChen.Certificates.RationalLogCertificate.check_sound`：有限有理检查给出真实 `Real.log` 的界。
- `ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound`：具体证书检查通过蕴含真实 `pairedLocalIntegral` 的上下界。
- `ImbalancedChen.Certificates.PairedV2.first_certificate_checked`：实际首格证书的 `check = true`。
- `ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics`：首格对象等于实际四重积分。

```lean
ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics :
  ImbalancedChen.Certificates.PairedV2.firstIntegral =
    (((8452171 : ℝ) / 1250000) / 80) *
      (∫ t in (937361 : ℝ) / 4096000..1875373 / 8192000,
        ∫ u in (194217 : ℝ) / 1280000..388777 / 2560000,
          ∫ z in (417 : ℝ) / 5000..76088109 / 532480000,
            ∫ w in (417 : ℝ) / 5000..z, 1 / (t * u * z ^ 2 * w))

ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds :
  (31703 : ℝ) / 1000000000000 ≤
      ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
    ImbalancedChen.Certificates.PairedV2.firstIntegral ≤
      (31704 : ℝ) / 1000000000000
```

以上为便读的记法；完整编译器类型保存在原始类型文件中。该界是独立证明的较宽有理区间 `[3.1703e-8, 3.1704e-8]`，未声称复证 JSON 存储的 Q160 端点。通用求和正确性定理已验收，但其前提仍要求每个实际单元检查通过；本次不构成全部 17,572 格或完整下界总账的认证。全覆盖、与实际父掩码及构造的识别仍需 Part 1；算术分布与误差需 Part 3 和相应接收 Part。17,572 格、7/3 仍属 B；12/5 不累计，撤回的 1.9728 不进入结论。主要接收方为 Part 5，相关同 rho 密度接口交 Part 4-A。

### A：采用的 above-mu-second 粗双图积分

```lean
ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower :
  (3 : ℝ) / 95000 ≤
    ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral (-3)

ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower :
  (32 : ℝ) / 3042147 ≤
    ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral 1

ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower :
  (640339 : ℝ) / 15210735000 ≤
    ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

已认证的是实际两张有理图的真实积分。图参数为 `k = -3` 或 `k = 1`，`u,v ∈ [0,1]`，`mu = 25/128`、`rho = 19/96`、`step = 1/384`，积分核为 `6 |k| step³ u² (1-v) / (x y Ro Rn)`。真实被积函数的逐点 pullback 等式也已验收。

把图积分接到物理域积分，仍需换元定理、覆盖和边界处理；逐点恒等式本身不提供整个积分换元。与实际普通筛密度、旧树以及同一算术 rho 的识别，以及粗截断尾项、严格有限缓冲、极限顺序仍由 Part 1 / Part 4-A / Part 4-B 接入。粗界与细网格界估计同一量，不得相加；此项不是全部 K 证书。A 类 compact 的 complete-record 仍不能代替完整原盒和精确节点。

## 证据目录与复核

[UPSTREAM_ACCEPTANCE.json](UPSTREAM_ACCEPTANCE.json) 列出所有原始证据的完整路径、Git blob、SHA256、字节数、逐模块源与对象 SHA256，以及剩余输入。共原样保存 40 个文件，957,558 字节，未复制其他 Part 的内容。两份 [首格 receipt](p2-first/receipt.json)、[粗积分 receipt](p2-coarse/receipt.json) 的原路径分别为 `verification/parts/p0/round2/p2-first/` 和 `verification/parts/p0/round2/p2-coarse/`。目录名变化不改变文件字节，映射逐项写入总收据。

[P0_LEDGER_P2_SELECTION.json](P0_LEDGER_P2_SELECTION.json) 是明确标记的派生 P2 投影，仅提取固定 `ledger-final/ledger-index.json` 的六个 P2 条目，并保存原 ledger 的 Git blob 与 SHA256；它没有冒充原始完整 ledger。完整类型同时保留原始 JSON 与可读 TXT，没有截断。

在仓库中运行：

```sh
python3 verification/part2/round2/upstream/verify_upstream_acceptance.py
```

该脚本可以从任意工作目录启动，也支持 `--repo-root PATH`。它检查本证据包和当前源码／锁定输入的同一性、receipt 与 log 的绑定、253 条完整类型与公理记录以及 P2 ledger 投影。成功输出 `PASS_EXACT_SOURCE_UPSTREAM_REUSE`。这是对既有验收证据的接收复核；它不产生新的 Lean 编译或积分证明。
