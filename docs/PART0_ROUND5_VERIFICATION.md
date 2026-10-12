# Part 0 第五轮：P3 quotient-sieve 供应证据接收

本轮接收 P3 已发布的
`ImbalancedChen.ChenQuotientSieveRemainders` 独立验证证据。生产者发布提交为
`0ac5ec5f43216215ff37488908a6d4e8d2c96636`，生产源码来自未改动的
`f3ad8cbe43c61c903857c7411626ee8c56f4f2f9`；P0 接收父提交为
`4d03e98e9adae3f4290005ab50afe40e41cbdb7b`。

| 项目 | 结果 |
|---|---|
| 生产源码 SHA256 | `caaca61f7e87eab1fe60b82b09d1f3438ebcace6b16f9ed7eac2d2411646664e` |
| Git blob | `ac3abc1ad7f2170fcca2308db1ae8534f1319315` |
| 严格 frontend | PASS，`trustLevel=0`、`warningAsError=true` |
| 生产对象原装重放 | PASS |
| 审计严格编译 / 原装重放 | PASS / PASS |
| 所属声明 | 34：30 theorem、4 definition，含 private/generated |
| 实际导入对象 | 4,237，逐对象路径、大小及 SHA256 绑定 |
| 传递公理 | 仅 `propext`、`Classical.choice`、`Quot.sound` |

该生产源码在 P3 两个固定提交、P0 已验根
`d0366ce64272e81faf6166a8a90050f56b328d38` 和本轮接收父提交上均为同一
blob。P0 公共根原先已经显式 import 此模块。封存的 core run
[`38289734671`](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734671)
在精确根提交上完成 9,802-job 全构建、根 stock `leanchecker`、5,872 项
根公理审计和类型导出；其原始 build/replay 日志分别含此模块的构建和重放行。

本轮只新增证据、接收器和状态文档，没有修改 Lean 生产源码、公共 import、
workflow、依赖 pin 或证明目标。因此没有把文档提交当作新的根验证，也没有
重复执行内容完全相同的整根重任务。离线接收器同时重验 P3 生产者证据包与 P0
封存根证据，并核对两侧固定 Git blob：

```bash
python3 verification/parts/p0/round5/p3-chen-quotient/verify_intake.py
```

完整回执、生产者回执、固定审计源码、原始证据归档和验证器位于
[`verification/parts/p0/round5/p3-chen-quotient/`](../verification/parts/p0/round5/p3-chen-quotient/README.md)。

## 剩余义务

该模块现在可作为 P3 的一个已验直接供应节点，但不等于实际分布结论。另一个
直接供应者 `Bombieri1965Richert418Unconditional` 及冻结 BV 闭包尚未恢复成
身份匹配的可加载对象；`Part3PrimeAPDistribution` 未严格编译、未重放、未审计。
普通 BV 的适用范围也不能改称 599/1000 高物理模数、rough/prime-product 槽或
非零素数相位结果。

P1 完整历史、P2 全证书、P3 实际误差、P4-A 的同一 rho 实际 K、P4-B 的
`hUpper`、P5 的完整 Chen 均值与 `hLower` 均继续开放。
`current_theorem_1_1_of_manuscript_bounds` 仍显式依赖 `hLower` 和 `hUpper`；
本轮没有新增或隐藏等强前提，也没有得到无条件主定理。
