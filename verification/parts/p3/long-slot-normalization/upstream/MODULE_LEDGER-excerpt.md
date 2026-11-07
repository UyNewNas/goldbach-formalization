### P3 — `ImbalancedChen.Part3LongSlotDistribution`

文件：`ImbalancedChen/Part3LongSlotDistribution.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `a41dc28e862f2f74bfa8719bc8b41141812f0f1d` |
| 原始 SHA256 | `f8054e4b422c5a62bfc39021aa5e6ce978d6aca83bfbc81990d35a53bdd557b5` |
| 当前 blob | `13288c1122f26135644bbd2c04f731f993ffa058` |
| 当前 SHA256 | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` |
| 当前固定源码提交 | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` |

未筛选、无相位整数长变量 AP 误差 ≤ 2*||alpha||_1*||rho||_1 的有限恒等/界。

类型：源码 theorem/lemma 12 个；编译器全部声明 35 个，其中匹配源码 theorem/lemma 12 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `f8054e4b422c5a62bfc39021aa5e6ce978d6aca83bfbc81990d35a53bdd557b5` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T032009180679Z-compile-ImbalancedChen.Part3LongSlotDistribution.log` |
| compile strict | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050744682383Z-compile-ImbalancedChen.Part3LongSlotDistribution.log` |
| replay  | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T051224325996Z-replay-ImbalancedChen.Part3LongSlotDistribution.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Part3LongSlotDistribution.lean:177:4: error: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050947421966Z-compile-verification.parts.p0.LongSlotAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:15:39.013346+00:00`；其中早期验证待办以本节当前门状态为准）：

- Actual rough/prime coefficients, phases and medium/two-long-variable distribution are not supplied.
- Same-rho realPhysicalDistributionError and normalization adapters remain separate.

