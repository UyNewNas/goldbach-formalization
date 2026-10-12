# Part 1 关键定理：完整源码声明头与 Lean 审计类型

## 证据与展示范围

- 共同证明基线：`1a80c1bcce67886f699d097fc37fd245cd3620bf`。
- 本文逐项匹配了实际成功审计中的 **14 条关键定理**；四个生产模块加 `LevelCheckProbe`，共五个定义模块的完整审计库存为 **150 条声明**。
- 实际编译方式：原版 `Lean.Elab.runFrontend`，`trustLevel = 0`，六个目标均以 strict 模式通过；实际审计由 `verification.parts.p1.Part1HistoryAudit` 的 Lean 环境库存及 `Lean.collectAxioms` 产生。
- 审计编译进程的独立记录退出码：`0`；原版 `leanchecker` 六次顺序单目标 replay 的汇总退出码：`0`（每次 `LEAN_NUM_THREADS=1`，六次均退出 `0` 并分别覆盖对应目标模块的定义声明）。
- 审计日志 SHA-256：`dde30b9419b719e946c067f9a5f6dc6e495395379040b13002f0e6ceaa0b94fa`。
- 实际最终回执 JSON SHA-256：`2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1`。

本文件只转录已经成功的声明库存、类型和传递公理报告，并核对定义模块、实际编译源码、编译日志及 replay 对象的哈希。提取脚本不自行运行编译或 replay，也不创建成功回执。上述原版 frontend API 编译不等同于已运行标准 `lake build`；原版检查器的六模块 replay 不声称重放了全部导入依赖；本记录不声称全仓 CI 已通过。最终交付 Git SHA 由主交付记录提供。

Lean 的 `Meta.ppExpr` 生成可读类型，可能隐藏隐式或实例实参，以及 proof-irrelevant 的证明实参；pretty-printed 文本不是内核表达式的完全展开序列化。本文件同时原样保留每条定理的完整源码声明头，包含源码中的全部绑定和假设，只去掉证明体。完整名称、定义模块和源码 SHA-256 将这两个视图绑定到同一项实际审计结果。

本里程碑的范围是普通父树的 lower fourth 积分与有限 upper third/fourth/fifth 历史 level 接口。raw odd-policy 等式不代表 boxed support、factorization license、完整历史第五层积分、K/c 数值界或主定理已经完成。

## 经验证据绑定的源码

| 源码路径 | SHA-256 |
| --- | --- |
| `ImbalancedChen/OrdinaryLowerFourFrontier.lean` | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` |
| `ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean` | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` |
| `ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean` | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` |
| `ImbalancedChen/HistoricalPrefixCertificate.lean` | `b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3` |
| `verification/parts/p1/LevelCheckProbe.lean` | `7987d49ff708dc9ecfc6e22e00a77fd9ce0fae5261eb2dcba6495d6cb5075b26` |
| `verification/parts/p1/Part1HistoryAudit.lean` | `f978429bb2c04f5ac39972cfbacd766843707e8a7470352316dcf8c4810bf60e` |

## 实际声明库存

| 定义模块 | 审计声明数 |
| --- | ---: |
| `ImbalancedChen.OrdinaryLowerFourFrontier` | 27 |
| `ImbalancedChen.ActualSelectedPrefixLowerCellSum` | 9 |
| `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` | 8 |
| `ImbalancedChen.HistoricalPrefixCertificate` | 96 |
| `verification.parts.p1.LevelCheckProbe` | 10 |

实际 Audit 编译的原始 argv：

```json
[
  "/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/lake",
  "-d",
  "/workspace/scratch/127408f63891/lean-runtime/frontend-driver",
  "-f",
  "lakefile.lean",
  "script",
  "run",
  "compileOne",
  "/workspace/scratch/127408f63891/goldbach-formalization/verification/parts/p1/Part1HistoryAudit.lean",
  "verification.parts.p1.Part1HistoryAudit",
  "/workspace/scratch/127408f63891/goldbach-formalization/.lake/build/lib/lean/verification/parts/p1/Part1HistoryAudit.olean",
  "strict"
]
```

## 关键声明目录

| 序号 | 完整名称 | 用途 |
| --- | --- | --- |
| 1 | `ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_log` | 实际下第四候选的父门控、排序、目标删素数与严格端点 |
| 2 | `ImbalancedChen.actualSelectedPrefixLowerOwnCubeSum_eq_cells` | 带 log N / singularSeries N 归一化的精确有限分解 |
| 3 | `ImbalancedChen.selectedPrefixLowerRestorationIntegral_eq_integrals` | 两个严格 own-cube 指示函数所在的同域真实积分 |
| 4 | `ImbalancedChen.tendsto_actualSelectedPrefixLowerOwnCubeSum` | 实际归一化素数修正和收敛到真实积分 |
| 5 | `ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_restoration` | b ≤ old 下连接同一个实际下筛树 |
| 6 | `ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized` | 规范 ceiling 枚举下的完整归一化极限 |
| 7 | `ImbalancedChen.historicalPrefixAncestorCell_unique` | 共用半开网格中祖先盒归属的唯一性 |
| 8 | `ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject` | 反向存储历史与处理顺序坐标投影对齐 |
| 9 | `ImbalancedChen.HistoricalPrefixCapData.level4_outside` | 第四层盒外精确继承第三祖先 level |
| 10 | `ImbalancedChen.HistoricalPrefixCapData.level5_outside` | 第五层盒外精确继承第四祖先 level |
| 11 | `ImbalancedChen.HistoricalPrefixCapData.levelCheck_of_selectedBoxCapChecks` | 实际 inherited old cap 的整盒检查供应有限 level 条件 |
| 12 | `ImbalancedChen.HistoricalPrefixCapData.upperThirdToFifthSaving_eq` | 实际 ordinary-base 历史树的第三至第五层 telescope |
| 13 | `ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub` | 共同第五层盒中的新旧任意 cap 函数精确分解 |
| 14 | `ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_eq_oddFirstExitPolicy` | raw odd-policy 接口；不声称 boxed support 或 factorization license |

## 1. ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_log

实际下第四候选的父门控、排序、目标删素数与严格端点。

- 定义模块：`ImbalancedChen.OrdinaryLowerFourFrontier`。
- 源码路径：`ImbalancedChen/OrdinaryLowerFourFrontier.lean`。
- 整个源码文件 SHA-256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`。
- 此声明头 SHA-256：`3ef84b6b76c2f369d0582481a7360d1faf2e11962590569318665ef2eb26d5ec`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem mem_ordinaryLowerFourFrontierTuples_iff_log
    (N cap : ℕ) (old w z : ℝ) (hN : 1 < N)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old
```

### 实际 Lean 审计输出的类型

```lean
∀ (N cap : ℕ) (old w z : ℝ),
  1 < N →
    z ≤ ↑cap →
      ∀ (p : Fin 4 → ℕ),
        p ∈
            ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
              (ImbalancedChen.roughPrimeUniverse N cap w z) ↔
          StrictAnti p ∧
            (∀ (i : Fin 4), Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ ↑(p i) ∧ ↑(p i) < z) ∧
              ImbalancedChen.actualPrimeTupleLog N p 0 + 3 * ImbalancedChen.actualPrimeTupleLog N p 1 < old
```

## 2. ImbalancedChen.actualSelectedPrefixLowerOwnCubeSum_eq_cells

带 log N / singularSeries N 归一化的精确有限分解。

- 定义模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`。
- 源码路径：`ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean`。
- 整个源码文件 SHA-256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`。
- 此声明头 SHA-256：`e034339701fcdc862ab0ec9d5f299fa586bc922009101825e0dd69991882d2f2`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem actualSelectedPrefixLowerOwnCubeSum_eq_cells
    (N cap : ℕ) (I : Finset (Fin 4)) (old nu a b : ℚ)
    (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (b : ℝ) ≤ (cap : ℝ))
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum true N cap ((N : ℝ) ^ (b : ℝ)) I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ J,
        (actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ)
          (selectedPrefixCellCap I old nu a b m j : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) -
        actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ) (old : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)))
```

### 实际 Lean 审计输出的类型

```lean
∀ (N cap : ℕ) (I : Finset (Fin 4)) (old nu a b : ℚ),
  a < b →
    1 < N →
      ↑N ^ ↑b ≤ ↑cap →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          ImbalancedChen.actualSelectedPrefixOwnCubeSum true N cap (↑N ^ ↑b) I old nu a b m J * Real.log ↑N /
              ImbalancedChen.singularSeries N =
            ∑ j ∈ J,
              (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap (↑a) (↑b)
                  (↑(ImbalancedChen.selectedPrefixCellCap I old nu a b m j))
                  (ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                    ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                      (ImbalancedChen.ordinaryLowerFourGateBounds ↑old)) -
                ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap (↑a) (↑b) (↑old)
                  (ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                    ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                      (ImbalancedChen.ordinaryLowerFourGateBounds ↑old)))
```

## 3. ImbalancedChen.selectedPrefixLowerRestorationIntegral_eq_integrals

两个严格 own-cube 指示函数所在的同域真实积分。

- 定义模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`。
- 源码路径：`ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean`。
- 整个源码文件 SHA-256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`。
- 此声明头 SHA-256：`d15982a6be4f94c783d004f6620d92615a093d7beef6fdcaffa3d49c905eae31`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem selectedPrefixLowerRestorationIntegral_eq_integrals
    (I : Finset (Fin 4)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    selectedPrefixLowerRestorationIntegral I old nu a b m J =
      ∑ j ∈ J, ∫ t in logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old),
        (primeOwnCubeGatedProfile (selectedPrefixCellCap I old nu a b m j : ℝ) t -
          primeOwnCubeGatedProfile (old : ℝ) t) * ∏ i, 1 / t i
```

### 实际 Lean 审计输出的类型

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
        ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J =
          ∑ j ∈ J,
            ∫ (t : Fin 4 → ℝ) in
              ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                  (ImbalancedChen.ordinaryLowerFourGateBounds ↑old),
              (ImbalancedChen.primeOwnCubeGatedProfile (↑(ImbalancedChen.selectedPrefixCellCap I old nu a b m j)) t -
                  ImbalancedChen.primeOwnCubeGatedProfile (↑old) t) *
                ∏ i, 1 / t i
```

## 4. ImbalancedChen.tendsto_actualSelectedPrefixLowerOwnCubeSum

实际归一化素数修正和收敛到真实积分。

- 定义模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`。
- 源码路径：`ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean`。
- 整个源码文件 SHA-256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`。
- 此声明头 SHA-256：`f02cc1ada5de189bbfcbea9d8f377b22ba98fbf03a4237ae40d8d8f14a9ad64c`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem tendsto_actualSelectedPrefixLowerOwnCubeSum
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixOwnCubeSum true N (cap N) ((N : ℝ) ^ (b : ℝ))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

### 实际 Lean 审计输出的类型

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) (cap : ℕ → ℕ),
        (∀ᶠ (N : ℕ) in Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N}, ↑N ^ ↑b ≤ ↑(cap N)) →
          Filter.Tendsto
            (fun N =>
              ImbalancedChen.actualSelectedPrefixOwnCubeSum true N (cap N) (↑N ^ ↑b) I old nu a b m J * Real.log ↑N /
                ImbalancedChen.singularSeries N)
            (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
            (nhds (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## 5. ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_restoration

b ≤ old 下连接同一个实际下筛树。

- 定义模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`。
- 源码路径：`ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean`。
- 整个源码文件 SHA-256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`。
- 此声明头 SHA-256：`61b0f9d681c6170bd7b324a8e6064da4dbeca3ef61b34a35b3d3a153a6d54626`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_restoration
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J -
        actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ (b : ℝ))
          ((N : ℝ) ^ (old : ℝ))) * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

### 实际 Lean 审计输出的类型

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      b ≤ old →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          (∀ j ∈ J,
              ImbalancedChen.selectedBoxCapCheck I old nu (ImbalancedChen.qLogPrimeMeshLo a b m j)
                  (ImbalancedChen.qLogPrimeMeshHi a b m j) =
                true) →
            ∀ (cap : ℕ → ℕ),
              (∀ᶠ (N : ℕ) in Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N}, ↑N ^ ↑b ≤ ↑(cap N)) →
                Filter.Tendsto
                  (fun N =>
                    (ImbalancedChen.actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J -
                          ImbalancedChen.actualSmallRosserMinusDensity N (cap N) (↑N ^ ↑b) (↑N ^ ↑old)) *
                        Real.log ↑N /
                      ImbalancedChen.singularSeries N)
                  (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
                  (nhds (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## 6. ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized

规范 ceiling 枚举下的完整归一化极限。

- 定义模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`。
- 源码路径：`ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean`。
- 整个源码文件 SHA-256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`。
- 此声明头 SHA-256：`a23bbd655c09331fb3f0561c86f18559b1f1c693044cd9f302c807dfc2a1ad72`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_ceil_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixLowerDensity N (Nat.ceil ((N : ℝ) ^ (b : ℝ)))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

### 实际 Lean 审计输出的类型

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      2 * b ≤ old →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          (∀ j ∈ J,
              ImbalancedChen.selectedBoxCapCheck I old nu (ImbalancedChen.qLogPrimeMeshLo a b m j)
                  (ImbalancedChen.qLogPrimeMeshHi a b m j) =
                true) →
            Filter.Tendsto
              (fun N =>
                ImbalancedChen.actualSelectedPrefixLowerDensity N ⌈↑N ^ ↑b⌉₊ I old nu a b m J * Real.log ↑N /
                  ImbalancedChen.singularSeries N)
              (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
              (nhds
                (2 * Real.exp (-Real.eulerMascheroniConstant) / ↑b *
                    MathlibNt.SieveTheory.suzukiContinuousLowerFactor (↑old / ↑b) +
                  ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## 7. ImbalancedChen.historicalPrefixAncestorCell_unique

共用半开网格中祖先盒归属的唯一性。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`2eabd37ea4ef264f1c438eddeaae319e4791540c2f8d1f59d792f5474a230d04`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem historicalPrefixAncestorCell_unique {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j)
    (hq : historicalPrefixProject hrd t ∈ logPrimeMeshCell a b m q) :
    q = historicalPrefixProject hrd j
```

### 实际 Lean 审计输出的类型

```lean
∀ {r d m : ℕ} (hrd : r ≤ d) {a b : ℝ},
  a ≤ b →
    ∀ {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)} {t : Fin d → ℝ},
      t ∈ ImbalancedChen.logPrimeMeshCell a b m j →
        ImbalancedChen.historicalPrefixProject hrd t ∈ ImbalancedChen.logPrimeMeshCell a b m q →
          q = ImbalancedChen.historicalPrefixProject hrd j
```

## 8. ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject

反向存储历史与处理顺序坐标投影对齐。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`e1e3861270479061758414ddcbd214cccf8da375ccd0b8b0c1d29ad9b6b648e0`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
    {r d : ℕ} (hrd : r ≤ d) {history : List ℕ} (hlen : history.length = d) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) =
      historicalPrefixProject hrd (primeHistoryLogCoordinates N d history)
```

### 实际 Lean 审计输出的类型

```lean
∀ (N : ℝ) {r d : ℕ} (hrd : r ≤ d) {history : List ℕ},
  history.length = d →
    ImbalancedChen.primeHistoryLogCoordinates N r (ImbalancedChen.rosserAncestor r history) =
      ImbalancedChen.historicalPrefixProject hrd (ImbalancedChen.primeHistoryLogCoordinates N d history)
```

## 9. ImbalancedChen.HistoricalPrefixCapData.level4_outside

第四层盒外精确继承第三祖先 level。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`e8901b4db08836ff654bf18ae3679f15ffe194eee994b39fd93e39fa85222f09`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem level4_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 4)
    (hout : ∀ j ∈ D.cells4, primeHistoryLogCoordinates N 4 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N history = D.level3 N (rosserAncestor 3 history)
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (history : List ℕ),
  history.length = 4 →
    (∀ j ∈ D.cells4,
        ImbalancedChen.primeHistoryLogCoordinates N 4 history ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
      D.level4 N history = D.level3 N (ImbalancedChen.rosserAncestor 3 history)
```

## 10. ImbalancedChen.HistoricalPrefixCapData.level5_outside

第五层盒外精确继承第四祖先 level。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`82cf0c6bbbf93b2191f1d8f3a02e1b1656056843ef68da2df327c9134a39c916`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem level5_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = D.level4 N (rosserAncestor 4 history)
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (history : List ℕ),
  history.length = 5 →
    (∀ j ∈ D.cells5,
        ImbalancedChen.primeHistoryLogCoordinates N 5 history ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
      D.level5 N history = D.level4 N (ImbalancedChen.rosserAncestor 4 history)
```

## 11. ImbalancedChen.HistoricalPrefixCapData.levelCheck_of_selectedBoxCapChecks

实际 inherited old cap 的整盒检查供应有限 level 条件。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`63e92db400d9999c8aaa7ecd2719a62a7026be387945efed75172a72dc845eee`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem levelCheck_of_selectedBoxCapChecks (D : HistoricalPrefixCapData)
    (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
    (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4))
    (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
    (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ)
    (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ)
    (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ)
    (h3 : ∀ j ∈ D.cells3,
      D.cap3 j = selectedBoxCap (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h4 : ∀ j ∈ D.cells4,
      D.cap4 j = selectedBoxCap (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h5 : ∀ j ∈ D.cells5,
      D.cap5 j = selectedBoxCap (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true) :
    D.levelCheck = true
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
  (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4)) (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
  (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ) (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ) (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ),
  (∀ j ∈ D.cells3,
      D.cap3 j =
          ImbalancedChen.selectedBoxCap (I3 j) D.old (nu3 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
            (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
        ImbalancedChen.selectedBoxCapCheck (I3 j) D.old (nu3 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
            (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
          true) →
    (∀ j ∈ D.cells4,
        D.cap4 j =
            ImbalancedChen.selectedBoxCap (I4 j) (D.old4 j) (nu4 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
              (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
          ImbalancedChen.selectedBoxCapCheck (I4 j) (D.old4 j) (nu4 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
              (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
            true) →
      (∀ j ∈ D.cells5,
          D.cap5 j =
              ImbalancedChen.selectedBoxCap (I5 j) (D.old5 j) (nu5 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
                (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
            ImbalancedChen.selectedBoxCapCheck (I5 j) (D.old5 j) (nu5 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
                (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
              true) →
        D.levelCheck = true
```

## 12. ImbalancedChen.HistoricalPrefixCapData.upperThirdToFifthSaving_eq

实际 ordinary-base 历史树的第三至第五层 telescope。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`d921a61df67aa38fafe9acd681e5fb1ed3db64fcc00444048a0327fea7524e55`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem upperThirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true →
      ∀ (N cap : ℕ),
        1 < ↑N →
          ∀ (z : ℝ),
            ImbalancedChen.firstExitRetainedPolynomial (D.upperThirdPolicy ↑N) (fun p => 1 / (↑p - 1)) [] true 1
                  (ImbalancedChen.roughPrimeUniverse N cap 0 z) -
                ImbalancedChen.firstExitRetainedPolynomial (D.upperFifthPolicy ↑N) (fun p => 1 / (↑p - 1)) [] true 1
                  (ImbalancedChen.roughPrimeUniverse N cap 0 z) =
              ImbalancedChen.actualHistoricalFourthSaving
                  (ImbalancedChen.ordinaryParityRosserPolicy false (↑N ^ ↑D.old)) (D.level3 ↑N) (D.level4 ↑N) N cap z +
                ImbalancedChen.actualHistoricalFifthSaving
                  (ImbalancedChen.ordinaryParityRosserPolicy false (↑N ^ ↑D.old)) (D.level3 ↑N) (D.level4 ↑N)
                  (D.level5 ↑N) N cap z
```

## 13. ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub

共同第五层盒中的新旧任意 cap 函数精确分解。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`cb2e623842e22e31f88fc893185cc0a9b1b6371b964a602145bc18390ce23826`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem exponent5_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 5 → ℝ) (f : ℚ → ℝ),
      f (D.exponent5 t) - f (D.exponent4 (ImbalancedChen.historicalPrefixProject ⋯ t)) =
        ∑ j ∈ D.cells5,
          if t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j then f (D.cap5 j) - f (D.old5 j) else 0
```

## 14. ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_eq_oddFirstExitPolicy

raw odd-policy 接口；不声称 boxed support 或 factorization license。

- 定义模块：`ImbalancedChen.HistoricalPrefixCertificate`。
- 源码路径：`ImbalancedChen/HistoricalPrefixCertificate.lean`。
- 整个源码文件 SHA-256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。
- 此声明头 SHA-256：`107eedaa42c69f409e84e69d22bc3d67aa13c1feea32702480488fb73a57557c`。
- 实际传递公理：`propext`, `Classical.choice`, `Quot.sound`。

### 完整源码声明头

```lean
theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre)
```

### 实际 Lean 审计输出的类型

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ),
  D.upperFifthPolicy N = ImbalancedChen.oddFirstExitPolicy fun pre => D.upperFifthPolicy N false pre
```
