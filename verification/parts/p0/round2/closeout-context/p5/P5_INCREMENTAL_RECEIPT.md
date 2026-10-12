# P5 新固定交付增量回执（只读）

固定供货提交：`bd83a110ee52626daf9e68535c007eb73a93daca`；远端 `refs/heads/chatgpt/chen-p5-lower` 已读取得到同一 SHA。共同证明基线不变。

**结论：存在新的真实供货。MeanLedger 是新源码；LowerScale 是同源别名。生产编译/重放已可与这批固定源码匹配，旧生产者审计确实成功，但缺 P0 规范要求的审计导入对象前后哈希。**

## 版本与三门状态

| 模块 | 固定源码 SHA256 | 严格编译 | 原装重放 | 公理审计 |
|---|---|---|---|---|
| ImbalancedChen.CurrentChenMeanLedger | `30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8` | PASS | PASS | producer 完整清单 PASS；P0 同对象绑定待补 |
| ImbalancedChen.CurrentChenLowerScale | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` | PASS | PASS | producer 完整清单 PASS；P0 同对象绑定待补 |

MeanLedger 原 db97 源为 `ab659310c2dca5400a6ffedc3790e1435187dc98b29e861cf273d95395005183`，其 34 个定理 header 和 16 个定义未改变；修复集中在六处证明/API 与验证说明。旧源码不能套用新源码的成功记录。

## 已执行的真实记录

| 模块 / 动作 | 开始 UTC | 退出码 | 秒 | 对象 SHA256 |
|---|---|---:|---:|---|
| ImbalancedChen.CurrentChenMeanLedger / compile | 20261012T042402897056Z | 0 | 171.955 | `1ddb7c1f850ad945ea093de5f98930e606654d286b7de19359df7c77c784cb9d` |
| ImbalancedChen.CurrentChenMeanLedger / replay | 20261012T043511053990Z | 0 | 74.535 | `1ddb7c1f850ad945ea093de5f98930e606654d286b7de19359df7c77c784cb9d` |
| ImbalancedChen.CurrentChenLowerScale / compile | 20261012T043109605634Z | 0 | 205.151 | `7d1f14794fe5c19328247b3f713f530e106076fd9fba3ea860884c6915a3ed9a` |
| ImbalancedChen.CurrentChenLowerScale / replay | 20261012T043625594734Z | 0 | 80.788 | `7d1f14794fe5c19328247b3f713f530e106076fd9fba3ea860884c6915a3ed9a` |
| ChenP5Audit | 20261012T043808908000Z | 0 | 214.417 | `98cbe776477bbeac5071b2bcaa254436b26f5802d634f8b6175c56ad981a805b` |

审计遍历 103 个所属声明：MeanLedger 93、LowerScale 5、此前 Buchstab 5；包含私有/生成声明。全部传递公理只含 `propext`、`Classical.choice`、`Quot.sound`，没有打印截断。固定提交内的 audit log 与 live 原日志逐字相同，compiler-types.json 与日志逐条相同。

旧 recorder、固定 finite receipt 都没有 `import_olean_sha256_before/after`。固定 dependencies.json 记录的是生产模块的直接依赖，不是审计本身导入的生产对象双端快照。现在测得对象哈希相同有助于复用，不能补写成当时已记录的双端事实。

## 只读 readiness

05:26:45 UTC 的对象盘点已找到两份生产对象和三个唯一直接依赖，全部匹配生产者既有清单；缺失的已记录对象：**无**。P5 生成对象当前为单个 main `.olean`；核心 CollectAxioms 的 main/server/private 三片齐备。盘点时没有运行中的 P5 Lean 或相同 ChenP5Audit。

最小新审计仅需导入：

```lean
import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.CurrentChenLowerScale
import Lean.Util.CollectAxioms
```

按旧审计清单应覆盖 98 个所属声明。生产对象及三项直接依赖都在：

`/workspace/scratch/cd30ec11ea1d/goldbach-formalization/.lake/build/lib/lean/ImbalancedChen/`

对应文件：CurrentChenMeanLedger.olean、CurrentChenLowerScale.olean、CurrentChenSummedBridge.olean、ChenQuotientPrimeSource.olean、CurrentNumericalTransfer.olean。各 SHA256、源码身份、所有已存在分片、核心读取路径见 object-readiness.json。此盘点没有新加载或编译 Lean。

## 关键编译器打印类型

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

以上为成功生产者审计实际打印的类型；JSON 保留其 98 个新批声明完整清单。P0 对象双端绑定仍单独待补。

## 其他新源码与边界

bd83 的 CurrentChenInitialSource 源 2573e544… 有真实编译失败。live 修复源 4b11a63c… 已有严格编译、原装重放及随后 InitialSourceAudit 的成功记录，但尚未进入固定提交。不能用这些成功覆盖 bd83 的失败源。InitialMean 的固定源与 live 源也不同，仍没有该目标的完成记录。

完整 adopted-mask Chen 均值、实际 c 解析支持与 hLower 仍未闭合；P4-A 的同一实际 rho / K 供应者仍需接入。这里只是完整有限十一项恒等式与有限因子四预算，不产生渐近均值供应者。

所有旧诊断、API 取回结果、固定 Git blob 校验、live 候选快照均已保留在本增量目录。未修改 ledger-final、主文档或任何生产源码；未启动 Lean、CI 或新环境。

## 有限十一项接口复核补充

上下界方向逐项固定：第 1、2、5、6 项需要下界，第 3、4、7、8、9、10、11 项需要上界；符号系数为 `(3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1)`。最后两项也可提交实际和的单个联合上界，不能从联合证书推断分别的数值端点。

采用同一个 `singularNormalization N` 时，每项 `delta` 的误差总损失精确为 `14 * delta`；联合最后两项分配 `2 * delta`。第 6 项和第 11 项是同一个 `E` 的补集，第 11 项将它应用于最后一对 `t.2`。有限源重排保留 `chenAdditivePrimeCarrier N`、自然数接收量 `N - P`、全部有标签因子及其重数。第 1、2 项的实际 sifted-source 等式有 `Even N` 前提；其余源字典仍保留实际筛余商计数。四个指数 `417/5000`、`19/125`、`59/250`、`1/3` 没有改动。

这些有限桥仍把逐行界和 `hweight` 明确列为输入。它们没有提供最终采用的 `E`、十一项渐近均值、真实 `c`/`K` 解析证明或 `hLower`。P5 的真实均值供应仍需 Part 4-A 的同一实际 `rho`/`K`，不必等待 Part 4-B。

## Root 补审计状态（仅消息更新）

Root 报告约 05:30 UTC 已在共享锁下启动唯一新目标 `ChenFiniteAudit`，枚举 MeanLedger 与 LowerScale 的 98 个所属声明，并复用已匹配的生产编译和重放对象。**本增量回执只记录其正在执行，尚未记录新的 P0 PASS。** 当前审核员没有启动、加载或重编任何 Lean 目标；本节不改变上述生产者旧审计与 P0 对象绑定缺口的区分。
