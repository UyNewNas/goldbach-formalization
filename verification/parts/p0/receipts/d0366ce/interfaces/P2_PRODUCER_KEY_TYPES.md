# P2 前 64 行：最终交接所需的完整类型

## 版本与验证身份

- 固定生产证明：`f0c00f9ccce98e04af439321a92eb9fd0dd26203`。
- 已实际成功的 P2 专项 CI 源：`e6d6d57323cc358cef060fb243ec386c13cb662d`；run `38252572597`，job `114822365913`。
- 固定后续交接：`101bb2291cd51f9717544ce477122fdd44eda44d`，生产源码与上述版本相同。
- 已发布新 P0 集成：`d0366ce64272e81faf6166a8a90050f56b328d38`，tree `e2ab22b96f76c8969386296558c626c62a581700`。
- **编制本摘录时，新 P0 core run `38289734671` 尚待 root 完成核验。本文件不声称已由 d036 的新 CI 确认类型。** Root 后续应将该 SHA 的实际类型产物与本摘录复核。

下面五项的 `type` 字段是固定生产者的**实际完整 pp.all 编译器原文**，不是从源码提取后重写的声明头。它们已在生产者原始 audit log、成功 CI 的 `axioms.log`、`declarations.json` 与完整 job log 中逐条比对相同。此处不另行启动或轮询 CI，也没有运行 Lean。

## 准确常数与实际求和对象

以下定义体摘自固定源码，和后面的编译器类型原文分开标识。网格与系数属于 `ImbalancedChen.Certificates.PairedV2`：

```lean
def a : ℚ := 417 / 5000
def h : ℚ := 19 / 125
def d : ℚ := 59 / 250
def mu : ℚ := 25 / 128
def K : ℚ := 8452171 / 1250000
def tLower (i : ℕ) : ℚ := mu + (d - mu) * i / 512
def tUpper (i : ℕ) : ℚ := mu + (d - mu) * (i + 1) / 512
def uLower (j : ℕ) : ℚ := a + (h - a) * j / 512
def uUpper (j : ℕ) : ℚ := a + (h - a) * (j + 1) / 512
```

累计模块 `ImbalancedChen.Certificates.PairedV2.Prefix64` 的定义：

```lean
def prefixIndex (i : Fin 4) : Fin 64 := Fin.castAdd 60 i
def batchIndex (i : Fin 60) : Fin 64 := Fin.natAdd 4 i
def rowIndices : Fin 64 → ℕ × ℕ :=
  Fin.append Prefix4.rowIndices Batch4To64.rowIndices
def rowZ : Fin 64 → ℚ :=
  Fin.append Prefix4.rowZ Batch4To64.rowZ
def rowOrdinal : Fin 64 → ℕ :=
  Fin.append Prefix4.rowOrdinal Batch4To64.rowOrdinal
noncomputable def rowIntegral (i : Fin 64) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)
noncomputable def integral : ℝ := ∑ i : Fin 64, rowIntegral i
def lowerBound : ℚ := 203256527543633 / 100000000000000000000
def upperBound : ℚ := 50814161308597 / 25000000000000000000
```

所有区间端点在下表统一写为未约分的 `/10^20`，仅为显示；它们与源码中的约分有理数完全相等：

| 实际积分和 | 原始零基范围 | 下界 | 上界 |
|---|---|---|---|
| Prefix4 | `[0,4)`，原四行 | `12676565261567/10^20` | `12676572571081/10^20` |
| Batch4To64 | `[4,64)`，新增六十行 | `190579962282066/10^20` | `190580072663307/10^20` |
| Prefix64 | `[0,64)`，累计六十四行 | `203256527543633/10^20` | `203256645234388/10^20` |

`Batch4To64.lowerBound` 在源码中为 `95289981141033 / 50000000000000000000`；累计上界在源码中为 `50814161308597 / 25000000000000000000`。

## 新六十行与原四行没有重复计入的准确含义

旧四行的 `rowOrdinal i = i.val`，新批的 `rowOrdinal i = 4 + i.val`。`Fin.append` 逐项保留真实坐标，`Fin.sum_univ_add` 给出下面的真实积分追加恒等式；累计界只使用两份已经证明的区间相加，首格没有再加入一次。

此外，`source_ordinal_coverage` 精确覆盖原始 `n < 64`；独立的 `rowIndices_injective` 排除实际网格坐标重复。原始行号分段的不交和实际格子不重计不是靠同一行号假定混为一件事。

每项仍为 `(K/80)` 乘以 `(t,u,z,w)` 四重积分，核是 `1/(t*u*z^2*w)`。`K/80 = (K/4) × (1/20)` 已含陈氏归一化与 Buchstab 收益，两个因子均只使用一次。

**这些结论覆盖有限采用行、真实坐标和有限积分和。完整几何并域/历史 parent 许可/真实计数至积分身份仍需 P1/P5；数值常数 K 出现在此处不代表同一实际 rho 的完整解析 K 密度界已经证明。完整 c、hLower、hUpper 也未由本批推出。**

## 五个完整编译器类型

### integral_semantics

声明全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_semantics`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) Real
      Real.instAddCommMonoid
      (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) =>
      @intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (t : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (u : Real) =>
              @intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (z : Real) =>
                  @intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (w : Real) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          w))
                    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a)
                (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix64.rowZ i))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uUpper
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tUpper
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

实际传递公理依赖：`propext`, `Classical.choice`, `Quot.sound`。

### integral_bounds

声明全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_bounds`。

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix64.integral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.Prefix64.integral
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound))
```

实际传递公理依赖：`propext`, `Classical.choice`, `Quot.sound`。

### integral_eq_parts

声明全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    ImbalancedChen.Certificates.PairedV2.Prefix4.integral ImbalancedChen.Certificates.PairedV2.Batch4To64.integral)
```

实际传递公理依赖：`propext`, `Classical.choice`, `Quot.sound`。

### source_ordinal_coverage

声明全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.source_ordinal_coverage`。

```lean
∀ (n : Nat),
  Iff
    (Or
      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @Eq.{1} Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal i) n)
      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))) =>
        @Eq.{1} Nat (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal i) n))
    (@LT.lt.{0} Nat instLTNat n (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
```

实际传递公理依赖：`propext`, `Quot.sound`。

### rowIndices_injective

声明全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices_injective`。

```lean
@Function.Injective.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) (Prod.{0, 0} Nat Nat)
  ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices
```

实际传递公理依赖：`propext`, `Classical.choice`, `Quot.sound`。

## 复核依据文件

- `KEY_INTERFACES_COMPILER.json`：上述五项和其他十四项原始完整记录。
- `NEW_400_COMPLETE_TYPES.json`：本批三模块新增四百项记录；SHA256 `5f36ebd40258e9ff1c2da6e9f85b79fba9e89104e3ffc77170d6bde79f17e57c`。
- `P2_INTAKE_RECEIPT.json`：固定源码、原始对象导入绑定及已实际完成的 P2 CI 接收回执。
- `ci-artifact.zip`：P2 原始 CI artifact `11749278994`；SHA256 `4f0b9cc1232226392515eda5ccf880a40241cc5afc8d6defcbac45206089d663`。

新 P0 SHA 的正式最终结论以 root 后续收取的实际 CI 产物为准。本摘录引用生产者已经执行的验证，不迁移或预报尚未核验的新 CI 结果。
