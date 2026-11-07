# P0 Round 5：接收 P3 quotient-sieve 直接供应模块

本批以证据接收方式闭合 `ImbalancedChen.ChenQuotientSieveRemainders`
的独立验收缺口。P3 发布提交
`0ac5ec5f43216215ff37488908a6d4e8d2c96636` 保留的生产者证据显示：

- `trustLevel=0`、`warningAsError=true` 的严格编译退出 0；
- 同一生产对象的原装 `leanchecker` 重放退出 0；
- 审计模块严格编译与原装重放均退出 0；
- 完整枚举 34 个所属声明（30 theorem、4 definition，含 private/generated）；
- 4,237 个实际导入对象逐个绑定；
- 没有 unsafe 或新 axiom，传递公理仅为 `propext`、
  `Classical.choice`、`Quot.sound`。

生产源码的 SHA256 是
`caaca61f7e87eab1fe60b82b09d1f3438ebcace6b16f9ed7eac2d2411646664e`，
Git blob 是 `ac3abc1ad7f2170fcca2308db1ae8534f1319315`。它在 P3 的实际
生产源码提交、P3 证据发布提交、P0 已验根 `d0366ce…` 和本次 P0
接收父提交 `4d03e98…` 上完全相同。

P0 公共根早已显式导入该模块。封存的 core run `38289734671` 对
`d0366ce64272e81faf6166a8a90050f56b328d38` 完成 9,802-job 全构建、
根原装重放、5,872 项根公理审计和类型导出；原始 build 与 replay
日志均明确记录此模块。因本批没有改变 Lean 源码、import、workflow、
依赖 pin 或证明目标，不触发一个内容完全相同的新根构建。生产者三门与
既有整根三门是两组分别保存的证据，接收器将它们绑定到同一源码身份。

执行：

```bash
python3 verification/parts/p0/round5/p3-chen-quotient/verify_intake.py
```

## 数学边界

本批只将两个直接供应者中的 `ChenQuotientSieveRemainders` 标为已验收。
另一个 `Bombieri1965Richert418Unconditional` 及其冻结 BV 闭包仍需恢复并
验收；`Part3PrimeAPDistribution` 本身仍未编译，因此没有新增 P3 分布定理，
也没有得到高物理模数、rough 槽或非零素数相位结论。实际 same-rho K、
`hLower`、`hUpper` 和无条件主定理均未闭合。
