# 实际 selected U5 classical-complement consumer

**状态：源码候选，未编译，未内核核验，不增加 P3.6 整体完成信用。** 本目录没有进入现有 `SOURCE_SELECTION.json`；未改主 cap、编译 runner 或任何已有 Lean 源码，也没有为它排远程编译任务。

## 新增内容

`ImbalancedChen/P3OriginalU5SelectedClassicalComplement.lean` 含一条公开候选定理：

`ImbalancedChen.P3OriginalU5SelectedClassicalComplement.exists_selected_original_count_beyond_classical`。

它直接消费既有 `P5OriginalU5ClassicalComplement.exists_original_count_beyond_classical`，将其中任意 `P` 实例化为

```lean
selectedPolicy R bank (1 / 1000 : ℚ) false N
```

并保留原有计数不等式的全部项：`fullProjectedMainSum`、`projectionReserve`、相同 `integerRho` 的 `branches`、原 `beyond` 载体和 `currentChenUpsilon5`。因此新模数结论明确属于这条实际计数结论中的 surviving carrier，不是一个缺少消费者的 cap 重述。

旧定理以 `eMax = 1/272` 调用。其返回的 `e < eMax` 在新证明内部给出

\[
  (34/125)e\leq 1/1000,
\]

因为 `(34/125)*(1/272) = 1/1000`。没有要求调用者另外提供小因子 allocation 或最终模数 cap。该 e 仍为附着精度，没有与 `PairRange.epsilon` 识别。

输出的 B、C、e、M 均先于 N、R、mesh、bank 和 zeta。对出现在计数结论 `beyond` 中的同一个 q，输出：经典 cutoff 的严格下界、原整数 ρ 非零、q 正性、平方自由、与 N 互素、原 ρ 的绝对值不超过 1，以及 `q < N^(599/1000)`。原始未支付 `branches` 的实部和符号保留；没有得出其小误差估计。

## 复用及禁止重复核对

本次搜索了固定 Y05/Y06 档案、20261123-resume 档案、现有物化模块，以及已取回的 20261103/20261105 P3 Git trees。在这些核对范围内，既有通用 count 定理已写出，但未找到 `selectedPolicy + beyond + 1/272` 的同等具体消费者。没有据此作“全仓所有历史分支均无类似工作”的声明。

复用的精确来源：

| 供应者 | 固定来源 |
|---|---|
| 实际 classical complement 与原 count 定理 | `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b:docs/source-only/20261123-yellow-node-owners/y05_causal_q_mass/ImbalancedChen/P5OriginalU5ClassicalComplement.lean`，blob `af7f2905aedf6ff2a6ab367d5976e991ddcb04b0` |
| 现成 `full_modulus_data` | 同提交的 `docs/source-only/20261123-yellow-node-owners/y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkCosts.lean`，blob `a2af61aa4f37b0e180c438db49dbed4905706b96` |
| 本轮非零真实整数 ρ 的物理上界 | `aa0f93b87cfd976ca5185e1293c1930562577d8a:ImbalancedChen/P3OriginalU5PhysicalModulusCap.lean`，blob `2b4ecdbec201a63658216c87fb8248ec53afff02`；实际调用当前模块同名接口 |
| 模数正性、平方自由、互素 | 原 `full_modulus_data` 的素数积整除结论，经既有 `Nat.pos_of_mem_divisors`、`sieveProduct_squarefree`、`coprime_of_dvd_sieveProduct` 消费；不重写模数性质证明 |

## 验收边界

本候选须在真实依赖闭包中编译和核验后才可取得形式化信用；没有使用 stub、axiom 或模拟假设替代被调用定理。本轮没有重编旧 Y05/Y06 全链。`P5OriginalU5ClassicalComplement` 当前仍来自既有 source-only 档案，其可读源码不等于已通过编译。

该 consumer 不提供完整 (S)/(F) 准入、共同 Q 查询覆盖、正谐和质量或未支付分支的分布界。P3.5 已验收的独立 Cauchy 核心不在本次重写范围内。详细接口边界见 `docs/part3-distribution/continuation-20261125-p36/ADAPTER_REVIEW.md`。
