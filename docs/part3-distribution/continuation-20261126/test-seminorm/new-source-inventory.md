# P3.5 增量源码盘点

**本轮未在检索范围内找到六份登记源码或能补齐实际 Y04 连续谱依赖的替代来源。** P3.4 已验收的实际 cusp Fourier 截面是可重用的归一化组件。P3.6 新交付覆盖原 U5 几何与计数。

## 远端与本地增量

- `origin/codex/p3-5-full-kernel-20261125` 和工作树 HEAD 都是 `5285d4f5d8c40eddf92c108b492c909de8b43cef`。此次只读取工作树并 fetch 对象和远端跟踪 refs。
- 对照 P3.4 历史复现包内 `heads.tsv` 的 **468** 个远端分支，当前 **470** 个分支中有 **15** 个前移、**2** 个新增。以旧分支的全部 tip 为负根，解析新 tip 的可达对象，得到 **251** 个增量提交和 **3,623** 个新增或改变的普通文件 blob。单独按 `5285d4f` 的提交时刻之后过滤得到 **194** 个提交。较早时刻与本地 fetch 前后的差异不等同于新增远端工作。
- 在增量提交的所有改动路径中，六个目标名字均未出现。逐一读取 **1,239** 个新增或改变的 `.lean`、`.lean.txt`、`.patch`、`.diff`、`.raw`、`.b64` 候选的长度及内容，目标接口与相关模块名字的文本搜索没有命中。唯一与登记字节数相同的原始 blob 是 5,217 字节的 `a70dccb7a075cb13b6314466d6c5195c3c946e09`，其中 `P2OriginalSaving19RowNumerics.lean` 的 SHA-256 `4be5f94041cc77997b8ad720966bc87938824493287480dd13d8abc7d95ef98e` 与登记目标不符。五个 P3 相关增量归档中的 **457** 个第一层普通成员也没有同名或同长度候选。
- 本地工作区按 `2026-11-25T10:00:38Z` 之后的修改时间筛选，排除 Git 元数据、依赖及构建对象、本轮盘点证据后，没有新增候选。没有重复扫描旧历史、旧归档或 Library。私有 refs、未推送作者工作树、任意不透明包装文件及云工作空间不在本轮的检查范围。
- P3.4 历史报告明确包含同名同 SHA-256 的全部六项，每项 `recovered_matches` 都为空。P3.4 的历史快照 SHA-256 已与报告匹配。其原作者路径指向 `goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261026b-NativeAllCuspEisenstein/`、`20261026b-NativeAllCuspAutomorphy/`，以及 `goldbach-proof-continuation/docs/source-only/20261102-resume-30s/S/s21_full_spectral_classes/`。这些是登记的路径线索。 [历史报告](https://github.com/UyNewNas/goldbach-formalization/blob/f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e/docs/part3-distribution/p34-20261125/source-resolution-historical-supplement.json)

[远端 refs 增量](ref-delta.json)和[字节核验明细](source-byte-check.json)保留全部六个目标哈希、五个增量归档、可复用源码的提交、blob、大小及 SHA-256。

## 可复用来源与边界

| 已存在源码 | 提交和 Git blob | SHA-256 | 已验收范围及 P3.5 关系 |
| --- | --- | --- | --- |
| `Part3ActualCuspFourierSection` | `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7` / `b5388e27defea43a64f30d2de8c4204b41bf91bc` | `9b22ea058fa2d35803c396e8d6a9c5cc66e229f5a386860fb4fae15dc2dd8a1a` | P3.4 七模块、113 声明严格编译、内核重放及完整公理审计的一部分。实际 Γ₀ 不变函数在固定高度的截面归一化。 |
| `Part3SignedCuspFourierSection` | `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7` / `7a3eb0f22fe5044ff6f4d09c0f9de4b1d8a55b4a` | `9d3b7a9fc8a2157847d3190a257cd51a34279f5a20c0c3745a3ec154c4ae4967` | 同批验收。固定高度截面正负频相位与共轭。该批没有谱系数 (R(n)) 的高度无关识别、Eisenstein/oldform 行或能量界。 |
| 暂存的 `Part3OriginalSignedNativeCuspFourier` | `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7` / `25f60aab6efa7f3c8d58bbe04880685d722a1b22` | `a45c7651eff6a49aa117e2462319d781489a0b3188c655e45b9546ba55b8e886` | 排除于该批验收。余下 packet 行组合仍导入 `Part3OriginalPrimaryPacketRows`。 |
| 历史 `Part3OriginalSignedNativeCuspFourier` | `85c1c7a882125785e1c56a4c099e29b2adffc8e2` / `6966353da6b9663cdb1a620d0351c9f3b4a81e17` | `766d00b552b66d4467d857e9e02553fc9431410d9028276fdd491f45ec747336` | P3.4 旧 terminal 的字节确认，保留在 `fa22a568` 基线。没有整个 terminal 的验收。 |
| 历史 `Part3OriginalPrincipalTraceRow` | `85c1c7a882125785e1c56a4c099e29b2adffc8e2` / `772549efd5edb67db97afb6c2027b490432d58c7` | `734d59fb3b38808eb64c31843464440fbb6f22c0ded12edcbaa9c899d8550650` | P3.4 旧 terminal 的字节确认，保留在 `fa22a568` 基线。依赖 `Part3ActualPrincipalCuspOneRemoval` 和 `Part3OriginalSignedTraceInput`，没有整个 terminal 的验收。 |
| 历史 Y04 `Part3OriginalPrintedContinuousTrace` | `fa22a56829ee880404516a36d498ce27dcb32f92` / `238e341104ee6dd460bbff769dd9d929c65cc42c` | `f8a6bf428af58f29161f4ae82edec4b978e9f9670f2dbee52c10b7f01156ab7f` | 原印刷迹乘积及规范化来源，已列在 P3.5 REUSE 清单。本次没有确认其完整依赖和独立验收。 |
| 当前 `Part3ActualWeightedSpectralBudget` | `5285d4f5d8c40eddf92c108b492c909de8b43cef` / `cacaed686d11a368bab01f00a8f7b167a2131382` | `6750b47730d741b93dfe2eba25e2e042760b42ec6f57cc650942b4346fda521e` | 已复用历史 `10b89181754c78c0e77616677295ee2105de0bb6` 的 31 条声明。结果给实际采样 Fourier 的加权和界，行族参数 `U` 的谱行实现留给后续适配。 |

P3.4 当前 `f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e` 相对历史快照的同名分支 tip 只增加历史与归档诊断。七个已验收源码的哈希已逐个比对实际 Git bytes。 [P3.4 验收范围](https://github.com/UyNewNas/goldbach-formalization/blob/f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e/docs/part3-distribution/p34-20261125/README.md)

P3.6 的原 U5 分支当前 `102c46c652fd10138071582aab083d7e3c0140dd`。其接受记录覆盖 `3aafcd2464df9486f98788a657086db9d686b187` 的三个模块、28 条公开及内部声明，给原 pair word 的支撑、完整整数模数 pushforward、原 U5 模数 cap。后续 EXTRA4 归档为 `FAILED_NOT_ACCEPTED`。经典补集分支当前 `ff84f0706527fff718e3be59c448a4cc592d44fc`，给 U5 计数与保留分支对接的源码，README 把其严格编译、内核重放、完整公理审计列作待完成。二者都未提供 Y04 所需的 `printedR_cont`、`original_two_cumulative_windows` 或实际连续谱行依赖。 [P3.6 三模块验收](https://github.com/UyNewNas/goldbach-formalization/blob/102c46c652fd10138071582aab083d7e3c0140dd/docs/part3-distribution/continuation-20261125-p36/main-three-3aaf-audit-continuation/README.md) · [经典补集](https://github.com/UyNewNas/goldbach-formalization/blob/ff84f0706527fff718e3be59c448a4cc592d44fc/docs/part3-distribution/continuation-20261125-p36/classical-complement/README.md)

盘点未修改 Lean 源码，没有运行新的编译、内核重放或旧声明验收。

## 原 Bessel 测试的逐 Fourier 模式上确界预算

对十个相关分支和提交的 **112** 个不同 Lean 源、上述 **1,239** 个增量源码候选做定向复用检查，去重后 **1,350** 个 blobs。按 `spectralTest`、`spectralMode`、`normalizedTestJetMass`、`testJetConstant`、`testSeminorm` 等标识共命中 **8** 个 blobs，逐项核对后未发现先对每个模式和每阶导数取上确界再按 `‖actualCoeff‖` 求和的成品。 [命中明细](mode-test-seminorm-reuse-hits.txt)

| 已有候选（共同来源 `52098e403ac4b28c72ec5958fd738ae93d785ac5`） | Git blob 和 SHA-256 | 可复用范围 |
| --- | --- | --- |
| R20 `Part3OriginalFullModulusTestJets` | `d4ce9301a7c98f117937e614ca29577c09e98d19` / `cf4c4840f8bcdfa778848bb1ded656636dccf5e249e9f957092955a5f7b262dd` | `spectralTest_jet_bound` 给每个 `ell,n,Y` 的共同 `q` 上界 `testJetConstant n * (1 + |ell 0|)^n / Y^n`。后续三个预算固定共同 `q`。尚未核实本文件的完整独立验收。 |
| S22 `Part3OriginalUniformTestCutoffBudget` | `4ed252e2956690d46848cb14b4f8253a88050610` / `0db0af01d82e152dad6e153d86ce78eb3deaa46390c9ef1f11957a4623a6a1a0` | `normalizedTestJetMass` 先使用共同 `q`，再按模式求和；`exists_original_six_testSeminorm_cutoff_constant` 的结论仍是 `∀ q, normalizedTestJetMass ... q ≤ ...`。源码注释直接区分逐模上确界之和。尚未核实完整独立验收。 |
| `Part3NativePeriod64Reconstruction` | `5d5f92e55709d2b0b96cf11811fa560f05fe27cb` / `724b2fd91c84aad404bad66a023d9c9151ffe21358c22a141e96bbf17b7c31bb` | 原 `spectralMode`、`spectralTest`、`actualCoeff` 定义以及光滑性、重构。P3.4 的 113 声明验收排除此整模块。 |
| `Part3ActualLiteralPacketIntegral` | `2e8e3750502b8ea1ea7e4ae0bf5b53cb72ac41ed` / `500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55` | 已有 `spectralMode_norm_le_one` 及权重和、积分组装。P3.4 的 113 声明验收排除此整模块。 |

可由 R20 的逐模上界在 `q` 上取 supremum，以 `Y^n` 消去尺度因子。对 `n ≤ d` 可用同一阶数 `d` 的实际 Fourier 权重和支付有限阶之和。`Part3ActualWeightedSpectralBudget.actual_uniform_weighted_l1` 的已有选择次序把常数放在 `rho,sigma,Y` 之前。该候选只支付原 Bessel 测试输入的导数 seminorm，实际谱行及其能量仍独立待接。
