# CutoffData 首次真实编译后的四处表达修复候选

只修改 canonical `ImbalancedChen/P1OriginalSingletonCutoffData.lean`。原 F 是
`080d4178711ae042235104f7f4768649f51da2ab`，失败任务是
`job_f0761da7e6124e818d654afef54ff5c5`。根代理已报告同任务 HBWitnesses 完整接受、Cutoff 四处错误；本轮不重编、不修改 HB，也不执行或修改 pair collector。

## 冻结指纹

| 版本 | 字节数 | SHA256 | Git blob |
|---|---:|---|---|
| 原 F Cutoff | 12510 | `c61b80c930959e86f310299c8c4b1d0b86d358320f08a89be404dbadc33c8b1d` | `6c7256bc2958e59646bdfbf4bd8d25f52cfaea79` |
| 历史四处表达候选 | 12610 | `1bfd8d23ba2cbfbcb69e3cafbc15ed277b29808b03cc43f6c5b42fcc7563d5bf` | `78360ebec536bb2903109b6a2c0bc9c10d3b3f06` |
| 最终源码候选（含注释修正） | 12670 | `d0fb57566d511f7ab4ef9270e71f53fb13b98d1b793feca0abacc24f2db02ccc` | `2e84d291816e3d8d45982a108ed61a61ab799cd8` |

`REPAIR_CANDIDATE.json` 保存原 commit、原提取 owner、匹配官方 API 文件指纹、完整七条声明 header，以及五段精确 UTF-8 byte splices（一个注释修正、四个证明表达修正）。区间为原文件中的半开区间，按降序应用：

| 原行 / 字节区间 | 最小改变 | 根因分类 |
|---|---|---|
| 5 / `[131,212)` | 文件头改为原 namespaces/statements 保持、四处 Lean API adaptations | 说明性修正，删除当前已不准确的 proof bytes 全不变说法 |
| 30 / `[1203,1225)` | 归纳前加 `rw [List.forall₂_map_right_iff] at hwin` | Lean 将原第二列表 elaboration 成 `ps.map Nat.cast`，它不是归纳所需的变量 index；现成 map-right 等价还原原 Nat 列表索引 |
| 152 / `[6530,6566)` | `by linarith` 改为 `zero_le_one.trans hA` | `A` 是原右端的局部 let 缩写；无需让线性算术自动展开，直接用 `0≤1≤A` 的既有证据 |
| 230 / `[10102,10150)` | `hrough.trans_le hpow` 改为 `hrough.trans hpow` | `hrough` 是 `≤`，原方法名用于严格不等式链；两段非严格关系用 `le_trans` |
| 260 前 / `[11589,11637)` | 在原 hcap 行前加 `change 2 * Xmin ≤ (N : ℝ) ^ astar at hpow` | 实际第263行的线性算术输入仍带函数合成；只展开定义后交给原 `linarith` |

没有改变声明、imports、namespace、原假设、阈值量词顺序或其余证明字节。原七个声明（含两个 private helper）的全部 header 已逐字比较。没有添加任何声明、目标误差假设或算术估计。

## 稿件与原证明来源

固定手稿是 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的
`paper/release-20261106/en/coefficient-appendix.tex`，blob
`10f3e2efb2074a9b97148a5151956e1d450be13f`，SHA256
`267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。
本轮只重读对应的513–520段：原非负 dyadic partition 给出 `R_i=2^j_i`、`X⁺`，在 HB 前固定 `z=f(2^(6k_*+2)X⁺)`，并说明每个原素数最终超过 `z`。

当前 Cutoff 的证明正是已有的窗口尺度上、下界 → 同一 polynomial argument cap → subpower cutoff 小于源下界。其原主体来自：

- `docs/source-only/20261112-resume/t05/rank2-deep-cutoff/P5IndependentFourPrimeChartCutoff.lean` 的 `active_psi_scale_each`；原全文件 SHA256 `5b8132f4e6c639fd6ee95efed6bdcb9b8bc5a2bc8c700b1bd24ebade8cc954b3`。
- 冻结 repaired 选本 `docs/source-only/20261112-resume/t05/rank2-dependency-audit/repairs/P5IndependentTestPrimeChartUniformCutoff.lean`；原全文件 SHA256 `d849269829a19b3b733082a0fe54291b0f920cc752ec900469cd49b3c8cd17c1`。

四错误均发生在既有推导的表达层。本轮没有发现必须增加稿件假设的实质缺口，也没有重写其原有限乘积、亚幂增长或 eventual 预算。

## API 与验证边界

已只读核对匹配的 Mathlib commit `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`：

- `Mathlib/Data/List/Forall2.lean` 的 `List.forall₂_map_right_iff`；它已通过原 HB import 链中的 `P5ActualHBMediumRoleSupports` 导入，不需新增 import。
- `Mathlib/Algebra/Order/ZeroLEOne.lean` 的 `zero_le_one`。
- `Mathlib/Order/Defs/PartialOrder.lean` 的 `le_trans`。
- 同一 Lean 4.33.0-rc1 的 `Init/Core.lean` 中 `Function.comp_apply = rfl`。

实际完成：五 splices 的正反向字节重建、七 header/import 相同、受禁证明 token 不存在、HB 源与 F 的9142 B / `00af3647…` 相同，以及 `git diff --check` exit 0。

**未运行 Lean、kernel 或云任务，因此不宣称修复已 elaborate 或通过。** 四处证明表达已通过 remote_delta 独立只读窄审，未发现具体阻断；新增纯注释 delta 也已独立复核：逆换后精确恢复已审四处表达候选。原12610 B候选及其原manifest/diff/README完整保留在 `historical-four-proof-splices/`，不作为最终postimage。旧 F manifest、旧提取记录与旧 review 均未改写。
