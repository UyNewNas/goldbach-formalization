# P5 bd83 补充：两个 Initial 候选、台账输入及有限接口

编写时间：`2026-10-12T05:39:51.852925+00:00`。固定来源盘点：`2026-10-12T05:24:40.984363+00:00`；既有执行/对象盘点截至 05:26:45 UTC。本文件只补充文档，不启动 Lean，不改主文档、历史 JSON 或生产源码。

## 可用于主文档的范围说明

P5 固定提交 `bd83a110ee52626daf9e68535c007eb73a93daca` 交付了实际 Chen 有限十一项台账与因子四的有限计数预算。`CurrentChenMeanLedger` 与 `CurrentChenLowerScale` 的严格编译和原装重放已按精确源哈希匹配；生产者旧完整公理审查覆盖这两个模块的 98 个所属声明，并另覆盖已有 Buchstab 的 5 个声明。旧审计缺少导入生产对象的前后哈希记录，P0 正单独补齐这一绑定门。

两个有限模块保留真实 prime carrier、自然数接收量、带标签 tuple 重数、相同 mask 的补集与原归一化。逐项界和有限权预算仍是显式输入；它们尚未供应最终 adopted mask 的十一项渐近均值、真实 c/K 的解析证明或 hLower。Part 5 后续只需等待 Part 4-A 的同一实际 rho/K，不必等待 Part 4-B。

同一 bd83 还含有 `CurrentChenInitialSource` 与 `CurrentChenInitialMean` 两个新源码候选。前者固定源码已有真实编译失败，后者固定源码尚无匹配目标的完成记录。live 未提交修改及其验证单独保留，不能移给固定失败/未编译源码。

**P0 补审计状态：** 据 root 最新状态消息，约 05:30:21 启动的首次 `ChenFiniteAudit` 在 `1:0` 报告 P0 对象根内缺少 `CurrentChenMeanLedger.olean`，未回退到 P5 额外对象根。这是启动/导入查找诊断，不是生产证明错误。Root 正修正对象查找后只补审计；本文件未记录新的 P0 PASS。

## 两个固定 Initial 候选的身份与诊断

共同固定提交：`bd83a110ee52626daf9e68535c007eb73a93daca`。以下保存副本均由固定 GitHub API 取回，并重新核对 SHA256 与 Git blob SHA1。

### ImbalancedChen.CurrentChenInitialSource

- 固定仓库路径：`ImbalancedChen/CurrentChenInitialSource.lean`
- 固定 source SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`
- Git blob SHA1：`75b04cb3982d24329f5f775c04c591cbfa505cf0`
- 固定源码副本：[源码](sandbox:/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialSource.lean)
- live 未提交副本 SHA256：`4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956`；与固定源不同。

固定源实际 strict/trustLevel0 编译：开始 `20261012T045632402531Z`，exit `1`，耗时 `428.784` 秒；编译前后源码哈希相同。第一处真实诊断原文：

```text
/workspace/scratch/cd30ec11ea1d/goldbach-formalization/ImbalancedChen/CurrentChenInitialSource.lean:41:14: error: unsolved goals
p : ℕ
h : p ∉ {p | Nat.Prime p ∧ 2 < p}
hp : 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p ≠ 1
⊢ Nat.Prime p → 2 < p → ↑p - 1 = 0
```

完整原日志副本：[20261012T045632402531Z-compile-ImbalancedChen.CurrentChenInitialSource.log](sandbox:/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/evidence/20261012T045632402531Z-compile-ImbalancedChen.CurrentChenInitialSource.log)；SHA256 `82b8cb5a4aad3ce782bced8e88a8b1435931c1f9a7b25c896f38fb02d3b279d8`。另保留同次 41:78、87:17、90:12、88:76 的后续诊断。

固定源码三门：严格编译 FAIL；没有同固定源码的成功重放；没有同固定源码的完整 P0 对象绑定审计。不同 live 修复源有 producer strict compile、stock replay 及随后 InitialSourceAudit 成功记录，只能归于该未提交源。

### ImbalancedChen.CurrentChenInitialMean

- 固定仓库路径：`ImbalancedChen/CurrentChenInitialMean.lean`
- 固定 source SHA256：`adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5`
- Git blob SHA1：`eedc3b6b1c8fe97bd46f17ab5ecbbe89d593c408`
- 固定源码副本：[源码](sandbox:/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialMean.lean)
- live 未提交副本 SHA256：`5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`；与固定源不同。

第一处真实诊断：**无可归属该固定源码的目标诊断**。已读取的执行记录没有该目标、同源的 compile/replay 完成记录；因此登记为“未编译候选/暂无目标完成记录”，不伪造失败位置，也不把导入依赖 InitialSource 的失败当作本目标已运行。

固定源码三门：compile 未确认、stock replay 未确认、完整公理审计未确认。源中目标系数是 `(33 / 4 : ℝ) * Real.log 3`，只涉及 actual Upsilon1；这是源提取范围，不是编译器已确认的定理。

## 可直接合并进 ledger 配置的 JSON

下列键与 `ledger-draft/build_ledger_v2.py` 实际 schema 对齐：将 `additional_modules` 追加到同名数组，将 `module_overrides` 按模块名合并到同名对象；保留现有配置其余键。明确的固定 `source_path` 防止无意选中 live 修复源。不要把这些模块添加到 `accepted_components`；验证状态仍由匹配源哈希的真实执行日志计算。

```json
{
  "additional_modules": [
    {
      "module": "ImbalancedChen.CurrentChenInitialSource",
      "path": "ImbalancedChen/CurrentChenInitialSource.lean",
      "source_part": "p5",
      "part_owner": "P5",
      "source_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialSource.lean",
      "source_original": {
        "commit": "bd83a110ee52626daf9e68535c007eb73a93daca",
        "based_on_commit": "1a80c1bcce67886f699d097fc37fd245cd3620bf",
        "sha256": "2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767",
        "git_blob_sha1": "75b04cb3982d24329f5f775c04c591cbfa505cf0",
        "local_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialSource.lean",
        "formal_fixed_delivery": true,
        "observed_utc": "2026-10-12T05:24:40.984363+00:00"
      },
      "receiving_parts": [
        "P5",
        "P0"
      ],
      "interface_scope_review": "固定来源候选：实际 prime-difference S1 向 current sifted source 的有限转移、两个奇异级数一致性、固定比值四系数与 primeFactors 误差可忽略性；固定源码编译失败。",
      "unclosed_inputs": [
        "固定 bd83 源 SHA256 2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767 有 strict/trustLevel0 编译失败；首诊断见 20261012T045632402531Z 日志 41:14 unsolved goals。",
        "不同的 live 未提交源 4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956 有 producer compile/replay 和随后 InitialSourceAudit 成功记录；不可用于本固定源的门状态。",
        "本固定源尚无匹配成功的生产编译、原装重放及 P0 同对象完整公理审计；不得接收为已核验组件。",
        "源码拟提供实际 S1 源转移、奇异级数归一化等式、固定比值四系数及 primeFactors 误差；本模块不供应完整十一项均值、真实 c/K 或 hLower。"
      ]
    },
    {
      "module": "ImbalancedChen.CurrentChenInitialMean",
      "path": "ImbalancedChen/CurrentChenInitialMean.lean",
      "source_part": "p5",
      "part_owner": "P5",
      "source_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialMean.lean",
      "source_original": {
        "commit": "bd83a110ee52626daf9e68535c007eb73a93daca",
        "based_on_commit": "1a80c1bcce67886f699d097fc37fd245cd3620bf",
        "sha256": "adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5",
        "git_blob_sha1": "eedc3b6b1c8fe97bd46f17ab5ecbbe89d593c408",
        "local_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialMean.lean",
        "formal_fixed_delivery": true,
        "observed_utc": "2026-10-12T05:24:40.984363+00:00"
      },
      "receiving_parts": [
        "P5",
        "P0"
      ],
      "interface_scope_review": "固定来源候选：拟由已 pin 的普通 BV 固定比值四下筛与实际源字典推导 current Upsilon1 的非平凡渐近下界；尚无匹配目标完成记录。",
      "unclosed_inputs": [
        "固定 bd83 源 SHA256 adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5 尚无匹配目标的 compile/replay 完成记录或实际首诊断；保持未编译候选身份。",
        "不同的 live 未提交源 5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137 与本固定源分开登记，不能共享未经绑定的门状态。",
        "直接依赖 CurrentChenInitialSource 的固定 bd83 源已失败；其余依赖为 CurrentChenMeanLedger 和固定上游 LiLiuGoldbachS1BetaFixedNormalizedLower，尚需实际 supplier 闭包与三门验证。",
        "源提取目标仅为 actual Upsilon1 的 (33/4) log 3 下界；不是 adopted L1 端点，不闭合另外十项、真实 c/K 或 hLower。"
      ]
    }
  ],
  "module_overrides": {
    "ImbalancedChen.CurrentChenInitialSource": {
      "source_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialSource.lean",
      "fixed_source": {
        "ref": "bd83a110ee52626daf9e68535c007eb73a93daca",
        "sha256": "2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767",
        "git_blob_sha1": "75b04cb3982d24329f5f775c04c591cbfa505cf0",
        "local_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialSource.lean"
      },
      "unclosed_inputs": [
        "固定 bd83 源 SHA256 2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767 有 strict/trustLevel0 编译失败；首诊断见 20261012T045632402531Z 日志 41:14 unsolved goals。",
        "不同的 live 未提交源 4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956 有 producer compile/replay 和随后 InitialSourceAudit 成功记录；不可用于本固定源的门状态。",
        "本固定源尚无匹配成功的生产编译、原装重放及 P0 同对象完整公理审计；不得接收为已核验组件。",
        "源码拟提供实际 S1 源转移、奇异级数归一化等式、固定比值四系数及 primeFactors 误差；本模块不供应完整十一项均值、真实 c/K 或 hLower。"
      ],
      "reviewed_utc": "2026-10-12T05:39:51.852925+00:00"
    },
    "ImbalancedChen.CurrentChenInitialMean": {
      "source_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialMean.lean",
      "fixed_source": {
        "ref": "bd83a110ee52626daf9e68535c007eb73a93daca",
        "sha256": "adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5",
        "git_blob_sha1": "eedc3b6b1c8fe97bd46f17ab5ecbbe89d593c408",
        "local_path": "/workspace/scratch/535d89efd063/p0-round2/p2-p5-audit/p5-incremental/fixed-sources/bd83a110ee52626daf9e68535c007eb73a93daca/ImbalancedChen/CurrentChenInitialMean.lean"
      },
      "unclosed_inputs": [
        "固定 bd83 源 SHA256 adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5 尚无匹配目标的 compile/replay 完成记录或实际首诊断；保持未编译候选身份。",
        "不同的 live 未提交源 5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137 与本固定源分开登记，不能共享未经绑定的门状态。",
        "直接依赖 CurrentChenInitialSource 的固定 bd83 源已失败；其余依赖为 CurrentChenMeanLedger 和固定上游 LiLiuGoldbachS1BetaFixedNormalizedLower，尚需实际 supplier 闭包与三门验证。",
        "源提取目标仅为 actual Upsilon1 的 (33/4) log 3 下界；不是 adopted L1 端点，不闭合另外十项、真实 c/K 或 hLower。"
      ],
      "reviewed_utc": "2026-10-12T05:39:51.852925+00:00"
    }
  }
}
```

## 三个关键完整编译器类型

以下逐字取自 bd83 已成功执行的 producer `ChenP5Audit` 日志/`compiler-types.json`，不是仅从 `.lean` 文本提取。三者实际传递公理均为 `propext`、`Classical.choice`、`Quot.sound`。P0 同对象补审计门仍单列待补，不能据这些类型先记 PASS。

### ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon

```lean
ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon :
∀ (N : ℕ) (E : ℕ × ℕ → Prop),
  ImbalancedChen.currentChenPairedPrimeSum N E =
    3 * ImbalancedChen.currentChenUpsilon1 N + ImbalancedChen.currentChenUpsilon2 N -
                      ImbalancedChen.currentChenUpsilon3 N -
                    ImbalancedChen.currentChenUpsilon4 N +
                  ImbalancedChen.currentChenUpsilon5 N +
                ImbalancedChen.currentChenUpsilon6 N E -
              2 * ImbalancedChen.currentChenUpsilon7 N -
            ImbalancedChen.currentChenUpsilon8 N -
          ImbalancedChen.currentChenUpsilon9 N -
        ImbalancedChen.currentChenUpsilon10 N -
      ImbalancedChen.currentChenUpsilon11 N E
```

### ImbalancedChen.currentChenPairedPrimeSum_ge_of_joint_last_bounds

```lean
ImbalancedChen.currentChenPairedPrimeSum_ge_of_joint_last_bounds :
∀ (N : ℕ) (E : ℕ × ℕ → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : ℝ),
  l₁ ≤ ImbalancedChen.currentChenUpsilon1 N →
    l₂ ≤ ImbalancedChen.currentChenUpsilon2 N →
      ImbalancedChen.currentChenUpsilon3 N ≤ u₃ →
        ImbalancedChen.currentChenUpsilon4 N ≤ u₄ →
          l₅ ≤ ImbalancedChen.currentChenUpsilon5 N →
            l₆ ≤ ImbalancedChen.currentChenUpsilon6 N E →
              ImbalancedChen.currentChenUpsilon7 N ≤ u₇ →
                ImbalancedChen.currentChenUpsilon8 N ≤ u₈ →
                  ImbalancedChen.currentChenUpsilon9 N ≤ u₉ →
                    ImbalancedChen.currentChenUpsilon10 N + ImbalancedChen.currentChenUpsilon11 N E ≤ u₁₀₁₁ →
                      3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀₁₁ ≤
                        ImbalancedChen.currentChenPairedPrimeSum N E
```

### ImbalancedChen.currentChen_lower_scale_of_finite_budgets

```lean
ImbalancedChen.currentChen_lower_scale_of_finite_budgets :
∀ {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon etaMean etaCount : ℝ},
  etaMean + etaCount ≤ 4 * epsilon →
    (4 * ImbalancedChen.currentC - etaMean) * ImbalancedChen.singularNormalization N ≤
        ImbalancedChen.currentChenPairedPrimeSum N E →
      ImbalancedChen.currentChenPairedPrimeSum N E - etaCount * ImbalancedChen.singularNormalization N ≤
          4 * ↑(ImbalancedChen.D12 N) →
        (ImbalancedChen.currentC - epsilon) * ImbalancedChen.singularNormalization N ≤ ↑(ImbalancedChen.D12 N)
```

逐项消费方向：下界为第 1、2、5、6 项，上界为第 3、4、7、8、9、10、11 项；符号系数是 `(3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1)`。联合最后两项必须是实际和的上界；相同归一化下逐项 `delta` 总成本 `14 * delta`，联合最后两项占 `2 * delta`。有限因子四预算中的 `hweight` 保持显式，不构成渐近均值供应者。
