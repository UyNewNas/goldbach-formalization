# P1.4：撤去额外 raw transfer 路线，复用原最终 compiled ρ

结论：本轮发现的是**所选证明路线增加了原稿未要求的强接口**，不是原稿原命题的反例。历史 `savingMiddle` 的 raw Δρ → boxed Δρ sharp-error 传递不能由现有密度界推出；但实际最终调用 `P1OriginalSingletonRectangleSchedule.original_single_prime` 已沿原稿路线工作，不消费这个历史 middle。应继续复用它的最终 compiled ρ / singletonAtlas 路线，不新造 raw-transfer 定理或等待它的包装。

本包没有新增 Lean，没有改旧 source/freeze/main。已发表 f06293 / 8ac0cc7c 的实际 owned before/after selected 支撑不重复。P1.4、原历史两个 middle、最终完整 PP、各原 HOLD 仍保持其真实状态；本包只撤去“raw transfer 是最终调用必需输入”的解释。

## 1. 原稿究竟主张什么

原稿 commit `9731290e8f53cffda44129906cde6a965eaa869b`：

- `eighth-unequal-parent-interface-20261009.tex:126–142` 的 U6/U7 是实际 parent 的 **raw ordinary density** 差及积分下界。130 行明确不主张有限 signed weights 的逐系数单调性。
- 同文 194–207 行先固定历史、共同细分、有限 cap、compiler 余量，随后对固定许可的 prime-product family 用 signed-atom 定理。它没有加入 raw Δρ 的 sharp coupled-domain transfer。
- `actual-k-compilation-joint-audit.tex:70–109` 给出 boxed c ≥ raw λ 与 reciprocal-totient density 成本；111–142 行用**先求 signed small-beta density 再取绝对值**支付小筛斜率。144–181 行要求最终同系数的整盒卷积与一次 factorial 恢复。
- `distribution-prime-product-completion-20261010.txt:34–49` 的 compiler 条件与 66–70 行的 PP 用的是同一个 compiled ρ。70 行明确不使用 sharp signed coupled-domain theorem。

所以，若先人为要求 raw history Δρ 本身的 signed sharp bound，再尝试靠 density compiler 转给它，就比上述原稿增加了一个实质输入。后文分析其失败点只否定这种推导，**不否定原稿、实际 saving 或 P1.4**。

## 2. 真实 caller 已有另一条正确接线

以下全是已有源码，不是本轮写的新 wrapper；本包按实际 local bytes 与 publication index SHA 完全匹配记录。

| 已有声明 | 实际消费与结论 |
| --- | --- |
| `P1OriginalFinite87PhysicalReserve.unchanged_upper_sector:50–56` | 最终 upper bank 的 sixthRoot − eighthRaw，精确等于原 orderedSixth − orderedEighth 的 normalized raw-density 差。它承担原 saving 的同源转移，不主张 raw/compiled 系数逐点相等。 |
| `original_archive_and_physical_reserves:61–106` | 从实际 87 frontier / R17 endpoint 与同一 finite compiler schedule 产出 density 上界、原遗漏费用、完整模数支撑和最终同一 c 的 sharp middle。 |
| 同文件 147–169 行 | `hGain` → `hjoined` → 原 `eighthSlots`；再与同一 `hCompiler` 的 `hden` 合并，得到最终 `physicalDensitySum S c < U`。没有调用历史 `savingMiddle` 或 `exists_original_reserves`。 |
| `P4AOriginalFiniteFallbackFinePPSchedule.joined:24–46,48–91` | 先选择一个 beta，再选一个 aligned k 同时满足 compiler / range / fineTolerance / rank-budget，最后 N0。最终 c 的 density、strict support、RealB count/distribution 均同源。 |
| `P1OriginalSingletonRectangleSchedule.original_single_prime:25–44,45–87` | 直接调用上述 final physical schedule。产出同一 `P.rho` 的 D < numericUpper，且 literal − primeMass·D 与 singletonTensor 相差已付 sharp reserve；tensor 精确等于 singletonAtlas。 |
| `P1OriginalSingletonMiddleTensor:109–146` | 对最终矩形 `P.rho` 支付原 singleton smoothing / squarefree collision，接到 `free P` 的三因子 tensor 与同一 original Atlas。这里没有历史 Δρ。 |

这一链明确说明：可以沿原稿 final compiled ρ 路线继续，**无需先证明历史 raw→boxed sharp transfer**。这不是抛弃原 87 saving：上表第一、二、三行正是原 saving 进入最终 density 上界的现有实质接线。

相反，`P1Original87SharpMiddleReserve.exists_original_reserves:82–99` 是另一项已有辅助结论：它只把两个历史 receiver 的已付部分剥离，显式留下 `comparisonMiddle/savingMiddle`。它们还未付款。审查最终 caller 的完整 proof body 即可确定“不消费”，无需从全仓库无命中推断。U01 的持久图只覆盖选定验证根，不能据它未列出某模块宣称全仓无 caller。

## 3. 新定位：为何简单 density + BT 转移不成立

精确 residual 和 β 选择在 `EXACT_FORMULAS.md`。已有 `P4AUpperTaggedContinuationAccounting.signAttachedValue_change:50–79` 已经证明点值编译差的真实 β 斜率，**不重写**。

关键区别：

```text
已付密度使用： | Σ_a β±(a) / φ(a) |
逐完整模数绝对估计需要： Σ_a |β±(a)| / φ(a)
```

后者不能用前者代替。实际 small Rosser 的两种 β 都有 β±(1)=1，因此后者至少是 1。该事实直接来自固定 MathlibNt provider 的 `lowerWeight_one:81–83` / `upperWeight_one:410–412` 与实际非零 small prime product；不是抽象兼容系数的反例，也不是 P1 saving 的反例。

即便另有原完整模数范围内的 Brun–Titchmarsh 上界，逐 a,d 取绝对值后会消耗**绝对 β 质量**。当前密度 theorem 所得的 C_N/log N signed slope 不再可用。一个 fixed pre-N fine width 不能被事后改成依 N 缩小来补这个损失。这只证明“这些现有界并不能支付所提 transfer”；不证明 transfer 本身为假。

## 4. 下一项应保留的真实未付输入

从已发表 roughPrimeReserve 消零继续，下一项可针对**最终矩形系数的实际 mediumAtlas 付款**，而不是 raw Δρ 转移。其精确对象和选参顺序见 `EXACT_FORMULAS.md §4`。现有 singletonTensor 已有独立三因子展开，原 OneLong 也已有后继源码；都不重复实现。

实际 medium 仍需同 original singleton W / chart / pre-HB cutoff、同 residue N 和 prime cap 2N、同 `products P/free P` 的合法局部参数与统一估计。Atlas 的代数恒等式允许任意 zeta，并不自动证明任意 zeta 都满足 (M)。必须选择原许可的正几何余量，再消费真实 restricted-medium 分析供应。仅 `RestrictedMediumObligation` 的定义、import、source graph 或 Weil 子步骤成功均不构成这项付款。

本包没有重审 J/native6 全图或宣称所有后继不存在；没有取得新的最终 medium 供应。故这里的准确分类是：**原稿 PP 的实际解析输入及族接线仍须验收；本轮未发现原命题反例。** 历史 middle 可留作独立辅助义务，不能虚记为已付，也不再当作这条 final caller 的强制前置项。

## 5. 证据与操作范围

`SOURCE_PINS.json` 绑定本轮实际读取的 bytes/SHA/computed blob、已有 publication exact match 和旧 provenance。computed blob 本身不是新远端身份；MathlibNt 使用固定 09b97 包，不当作标准 Mathlib。现有 source-only / HOLD / kernel 历史标签不升级也不降级。本轮没有运行 Lean、Lake、LSP、候选、helper、fixture 或 CI，没有额度调用、Git/GH 写入或 artifact 取件。

一次错误的非现成 blob 查询在禁 lazy-fetch 设置下仍触发 Git 尝试连接 promisor；连接 SSL 失败，命令已结束，没有取得请求对象的内容。该错误查询不作为任何证据，随后停用未知 Git 对象读取，仅用本地文件与冻结元数据。完整记录见 `SOURCE_PINS.json.operation_incident`。

