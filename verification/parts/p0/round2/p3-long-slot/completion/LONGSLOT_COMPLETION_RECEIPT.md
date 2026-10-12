# P0 LongSlot 固定修复候选：三门完成回执

**固定候选已通过生产严格编译、专属审计严格编译和 stock 内核重放，完成本次请求的最小三门。** 源码未再修改；后续正式接收入 integration 由根 P0 负责。

编制时间：2026-10-12T05:15:18.498328+00:00。

## 固定身份

- 共同证明基线：1a80c1bcce67886f699d097fc37fd245cd3620bf。
- 手稿：ba6ec11d800eccc54406490631895e174de85766。
- 原 P3 源提交：64598da177adf861df3763d7c465ff941388b6d6。
- 已发布 P0 验证提交：6d1e5c4710a66f68fd101d0b40b5514bbbba4919，父提交 c9f407efe66240c08c2e8a678330ba7b98b74db5；分支 chatgpt/chen-p0-validation-r2。
- 固定 Lean：leanprover/lean4:v4.33.0-rc1；原依赖、定义、量词和常数保持不变。
- 生产源码 SHA-256：67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e。
- 生产源码 Git blob：13288c1122f26135644bbd2c04f731f993ffa058。
- 已验证生产 olean SHA-256：fd8cdcf5ac894e5b904f8bdc0e80506b16c23bb17bc1a568ea4a3a5b50b61816。

远端固定 commit/tree/blob 的核验由根 P0 提供；本执行者逐字核对了对应本地生产源码 SHA，并将编译、审计导入和重放绑定到同一对象。没有声称构建了该提交整棵项目树。

## 实际执行与等待

| 顺序 | 单一目标 | 开始观察时间 UTC | 等待加启动秒 | 门内运行秒 | 结果 |
| --- | --- | --- | ---: | ---: | --- |
| production | ImbalancedChen.Part3LongSlotDistribution | 2026-10-12T05:07:44.688894+00:00 | 86.083 | 56.725 | exit 0 / verification_passed=true |
| audit | verification.parts.p0.LongSlotAudit | 2026-10-12T05:09:47.424898+00:00 | 57.349 | 83.336 | exit 0 / verification_passed=true |
| replay | ImbalancedChen.Part3LongSlotDistribution | 2026-10-12T05:12:24.339946+00:00 | 69.438 | 26.924 | exit 0 / verification_passed=true |

每一门独立持有相同排他锁，上一门完成后才提交下一门：

```sh
flock -x /workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/frontend.lock python3 /workspace/scratch/535d89efd063/p0-round2/runtime/verify_batch.py compile ImbalancedChen.Part3LongSlotDistribution
```

```sh
flock -x /workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/frontend.lock python3 /workspace/scratch/535d89efd063/p0-round2/runtime/verify_batch.py compile verification.parts.p0.LongSlotAudit
```

```sh
flock -x /workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/frontend.lock python3 /workspace/scratch/535d89efd063/p0-round2/runtime/verify_batch.py replay ImbalancedChen.Part3LongSlotDistribution
```

等待数值包括取得锁前等待与 Python 运行器启动/索引时间，不能冒称精确的锁独占等待。完整外层时间戳、返回码、命令和原始输出见同名 JSON 的 outer_locked_runs 及 longslot-completion/ 外层日志。未调用 P1 内锁 driver，没有双重锁嵌套，也未操作 P1 构建。

## 验证强度与声明盘点

生产和审计均由现有 P0 driver 通过原 pinned Lake 调用官方 Lean.Elab.runFrontend，明确 trustLevel=0、warningAsError=true。实际 kernel gate 使用工具链自带的 leanchecker --verbose，重放该生产模块在 imports 上的声明；未声称 --fresh 全导入闭包重放或根 lake build。

专属审计枚举 **35 个定义模块所属声明：6 个 definition、29 个 theorem**，包括私有及自动生成声明。所有声明名唯一、数量一致；未发现 unsafe 或 axiom 声明，传递公理只有 propext、Classical.choice、Quot.sound。全部 raw/readable 编译器类型无省略符。

生产源码前后哈希不变；审计实际导入的生产对象、生产严格编译对象以及重放前后对象均为同一 SHA。每个运行记录的直接导入对象前后保持一致。

完整 35 项编译器类型存于 longslot-completion/compiler-types.json、compiler-types.txt、compiler-readable-types.txt。下列关键类型直接来自实际审计输出，不是源码类型提取：

### ImbalancedChen.part3IntervalAPCount_coprimeMean_error

```lean
∀ (L U q a : ℕ),
  LT.lt.{0} 0 q →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0} (↑(ImbalancedChen.part3IntervalAPCount L U q a))
          (HDiv.hDiv.{0, 0, 0} ↑(ImbalancedChen.part3IntervalCoprimeCount L U q) ↑q.totient)))
      2
```

### ImbalancedChen.part3LongSlotRemainder_eq_zero_of_not_coprime

```lean
∀ (L U q a m : ℕ), a.Coprime q → ¬m.Coprime q → Eq.{1} (ImbalancedChen.part3LongSlotRemainder L U q a m) 0
```

### ImbalancedChen.part3LongSlotRemainder_abs_le_two

```lean
∀ (L U q a m : ℕ), LT.lt.{0} 0 q → a.Coprime q → LE.le.{0} (abs.{0} (ImbalancedChen.part3LongSlotRemainder L U q a m)) 2
```

### ImbalancedChen.part3LongSlotSignedError_norm_le

```lean
∀ (S Q : Finset.{0} ℕ) (α ρ : ℕ → ℂ) (L U a : ℕ),
  (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LT.lt.{0} 0 q) →
    (∀ (q : ℕ), Membership.mem.{0, 0} Q q → a.Coprime q) →
      LE.le.{0} (Norm.norm.{0} (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (∑ m ∈ S, Norm.norm.{0} (α m))) (∑ q ∈ Q, Norm.norm.{0} (ρ q)))
```

### ImbalancedChen.part3LongSlotSignedError_norm_le_of_mass

```lean
∀ (S Q : Finset.{0} ℕ) (α ρ : ℕ → ℂ) (L U a : ℕ) (M D : ℝ),
  (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LT.lt.{0} 0 q) →
    (∀ (q : ℕ), Membership.mem.{0, 0} Q q → a.Coprime q) →
      LE.le.{0} (∑ m ∈ S, Norm.norm.{0} (α m)) M →
        LE.le.{0} (∑ q ∈ Q, Norm.norm.{0} (ρ q)) D →
          LE.le.{0} (Norm.norm.{0} (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) D)
```

### ImbalancedChen.part3LongSlotSignedError_norm_le_box

```lean
∀ (M D L U a : ℕ) (α ρ : ℕ → ℂ),
  (∀ (m : ℕ), Membership.mem.{0, 0} (Finset.Icc.{0} 1 M) m → LE.le.{0} (Norm.norm.{0} (α m)) 1) →
    (∀ (q : ℕ), Membership.mem.{0, 0} ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) q → LE.le.{0} (Norm.norm.{0} (ρ q)) 1) →
      LE.le.{0}
        (Norm.norm.{0}
          (ImbalancedChen.part3LongSlotSignedError (Finset.Icc.{0} 1 M) ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) α ρ L U
            a))
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 ↑M) ↑D)
```

## 首失败与最终修复补丁

保留原 P3 源 SHA f8054e4b422c5a62bfc39021aa5e6ce978d6aca83bfbc81990d35a53bdd557b5 的第一次真实 Lean exit-1 失败，运行 192.03 秒。首诊断原文为：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Part3LongSlotDistribution.lean:177:4: error: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

```

随后还有 189:61 的 coprimality 目标未解及相关 strict simp 提示。这是 Lean 失败，不是成功信号中止。原日志：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T032009180679Z-compile-ImbalancedChen.Part3LongSlotDistribution.log。

此前两处 proof-only 修复是 letI 改 let，以及显式证明互素等价的两个方向。本次三门运行无需进一步修复；相对原 P3 源的 **12 个源码 theorem 头（含两个 private）和 6 个定义正文全部不变**。

最终长期补丁为 p3-longslot-proof-fix.patch；历史 p3-longslot-proof-fix-candidate.patch 保留为相同字节的别名。补丁内容已从原 P3 源和本次已验证源重新生成，SHA-256：0066d75a1d089ebeb02fc2c0bd3aa3de6a793c8991f7642f8597026688aac762。

## 接收范围与未闭合输入

本组件提供未另加粗糙/素数过滤或长槽相位的整数长槽有限误差界；短槽 alpha 和模数权 rho 仍是定理所写的任意复系数。接收方为 P3、P4-B、P5 和 P0。它不供应实际构造的 same-rho realPhysicalDistributionError，不闭合 medium/two-long 分布或真实 K、c、hLower、hUpper。

没有编译 Part3LongSlotNormalization 或任何其他 P3 闭包；完成三门后已停止 Lean。未推送 integration、未触发 Actions、未改其他 Part 源分支。完整根构建与最终集成 SHA 验证不在本回执范围。

## 原始执行日志

- production：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050744682383Z-compile-ImbalancedChen.Part3LongSlotDistribution.log；SHA-256：e94df9629020db32c374379317fb9e99dd0ebbfd8dea9c50a94da57f75666afe。
- audit：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050947421966Z-compile-verification.parts.p0.LongSlotAudit.log；SHA-256：a9a002481db6960fb4bb050e65e9732db1bceed836010116f929114fffdd262e。
- replay：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T051224325996Z-replay-ImbalancedChen.Part3LongSlotDistribution.log；SHA-256：13c2168a3a7d6729d9e0d53be93bca9ad8c65bb6357def7db62554b431acb6c2。
