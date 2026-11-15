# 原文与实际 API 对应

本包新增源码只有 `P1OriginalOwnedEighthSelectedSupport.lean` 中的一条定理；以下行号按本包冻结版本。

| 原稿或旧源 | 真实内容 | 新候选中的用途 |
|---|---|---|
| `main.md:115–119` | 原 signed gain、actual prime mean 与 reserve 仍黄；4733 中段仍保留 | 保持黄色，不改主稿 |
| `current-eighth-distribution-interface-audit-20261009.tex:125–149` | 原 mask complement 的每个平方、所有后续 slot；后续偶位由前一奇位准入控制 | 候选 134–180：完整 ordinary 准入传递，再复用已实现的 full D-well/selected append |
| 同稿 151–174；`eighth-unequal-parent-interface-20261009.tex` U1–U6 | 共同原第三历史、真实 current-sixth parent、selected cap，不能由两项单侧估计相减 | 候选 70–103：同一个 states/owner/trim，从原 supplier 推导 P≤comparison<M；不比较 signed 质量 |
| 同稿 176–229 | endpoint 分组及独立三因子；不能按盒内实际 tuple 改分组 | **未由本候选证明**；仅给其前置 full/selected support 与固定 tent buffer |
| 同稿 231–253 | 实际 residue=N、local-scale 与 7/32 三/四单项式损失 | **未付款**；没有把物理 N 改成局部 x 或 cap |
| 同稿 255–321 | 真实 HB outer slots、uniform SW、同 compiled rho 的 PP 估计 | **未付款**；本候选不新建 W 或 outer family |
| 同稿 342–359 | 固定历史/余量→dispersion→beta/omega→细网格→N | 候选参数 47–50 先固定原 supplier 与 n/r；没有新 N-adaptive 选择 |
| `distribution-prime-product-completion-20261010.txt:23–70` | 原 PP 必须有同系数有限卷积、完整乘积、全家族统一性与 restricted M | 见 REMAINING_INTERFACE 的未付接口，不作为新假设搬进 Lean 候选 |

| 已有声明（完整身份见 SOURCE_PINS） | 精确适用处 |
|---|---|
| `OwnedPrimitiveLedger.beforeLeaves/afterLeaves` | 候选 54–55 直接接受原两种 leaf membership，未重建或去重列表 |
| `LicensedSixthRealization.states` | 候选 70–74 展开原 filter；没有额外 owner 字段 |
| `AllEighthFrontierTerminal.actual_rank_eight_state_canonical` | 候选 75–84，恢复原八素数前缀及相同目标 N 的坐标 |
| `LicensedSixthRealization.FilteredSourceSupply` | 候选 91；同参数的既有 forall-N/forall-source 输出 |
| `EighthKernelIntegration.actualParent_residual` | 候选 92–101；实际 level6Exponent，而非 comparison 代替父层 |
| `FiniteEighthCap.finiteCap_licensed` | 候选 90、170–184；原 selected c 所有 complement tests 与 width n buffer |
| `P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible` | 候选 104–119；完整真实入站 ordinary 准入 |
| `InheritedTerminalLevel.ordinary_terminal_admissible` | 候选 134–142；公开声明。未调用 private inherited_ordinary_leaf_admissible，也不要求旧导出补丁 |
| `FirstExitValidSelection.exists_validSelection_of_mem_firstExitRetainedLeaves` | 候选 143–160；原 carrier 中的 tail 与实际 selected list 的严格等式 |
| `Part3.ActualCompactAllRankSupport.upper_set_dwell_support` | 候选 164–168；参数只有实际 prime list、decreasing order、UpperAdmissibleSet |
| `P4AFinitePPSelectedPrefixSquares.complete` | 候选 179–180；任意 arity 支撑算术。它不接受也不输出 ALL16/upper 系数的 PP 结论 |

精确被复用的通用 append 合同是：

```lean
theorem complete {k N : ℕ} (hN : 1<N) (I : Finset (Fin k)) (p : Fin k→ℕ)
    (hp : ∀i,0<p i) (tail : List ℕ) (M : ℝ)
    (hfull : actualDwellSupport ((N:ℝ)^M) (List.ofFn p++tail))
    (hg : ∀ j∉I,selectedSquareExpr I (actualPrimeTupleLog N p) j≤M) :
    actualDwellSupport (((N:ℝ)^M)/((selected I p).prod:ℝ)) (selected Iᶜ p++tail)
```

这里只展示已有类型；候选给出其实际 `hfull` 与 `hg`，不将二者作为调用者的新数学责任。k=8、I=原 selected c、tail=原剩余子列、M=原 finiteCap，均没有自由替换。
