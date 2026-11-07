# Part 2 第三轮：运行入口重定位与冻结记录

本目录保存第三轮实际使用的运行输入副本和来源链。运行工作区为：

```text
/workspace/scratch/1334dbd5a747/lean-runtime-p2/round3-runtime
```

`verify_project.py` 和官方 frontend driver 与第二轮代码逐字节相同。环境和
producer 路径已重新定位，原有期望源码/对象哈希继续检查。旧 `recovery/`
工作区和 `verification/part2/round2/runtime/` 归档均未改写。

本次 runtime agent 没有启动 Lean 编译、kernel replay 或 cache 恢复操作。
下面的 Data 实际执行由 root 串行完成；本目录链接其 canonical receipts，
不重复保存运行日志。

## 本轮实际运行入口

使用原装 `leanprover/lean4:v4.33.0-rc1`，Lean githash 为：

```text
62eed1db4d67327ec8120be05f1a1b0847d74561
```

原装 Lake 执行固定 driver，调用未经修改的 `Lean.Elab.runFrontend`：
`trustLevel := 0`、`warningAsError := true`。初始化 API 与第二轮相同，
位于独立 driver 中；没有向生产声明加入公理，没有改工具链二进制或内核。
随后调用原装 `leanchecker --verbose MODULE`。实际 receipts 明确记录
`metadata_adapter: false`。

可从任何目录显式运行一个模块：

```bash
python /workspace/scratch/1334dbd5a747/lean-runtime-p2/round3-runtime/verify_project.py compile MODULE
python /workspace/scratch/1334dbd5a747/lean-runtime-p2/round3-runtime/verify_project.py replay MODULE
```

`compile` 默认从 P2 仓库的对应模块路径读取源码，也接受第四参数指定绝对源码
路径。输出写入 P2 自己的 `.lake/build/lib/lean`；runner 不自动重建依赖。
保持 `LEAN_NUM_THREADS=1`，每次仅运行一个 frontend 或 checker。

这套入口提供**官方 frontend 编译与原装 kernel replay**。它不构成普通
`lake build` 或全项目根模块已经成功运行的声明，也不扩大各模块积分定理的范围。

## 为什么需要重定位

第二轮环境中的 P0 临时目录
`/workspace/scratch/535d89efd063/p0-round2/validation` 已不存在。旧 runner
会在启动 Lean 前读取该处的 expected producer 源码和对象；直接复用旧路径会
无法完成输入核对。

此前独立复制到本仓库的六个 P0 producer 对象仍然存在，六份本地源码和对象
均重新核对为原期望哈希。本轮只在新的运行副本中把路径指向这些同字节文件，
没有降低或替换期望哈希。原路径保存在 `original_round2_observed_paths` 中，
完整旧链仍由以下原字节副本提供：

- [round2-provenance-original.json](round2-provenance-original.json)
- [round2-project-cache-transfer-original.json](round2-project-cache-transfer-original.json)

固定 P0 证明提交为 `278f949444748a30b5165ff47bfa283ab0bad0d8`，回执提交为
`cce2334906f068fda2f58c400646366f2aa2d417`。

新的固定 producer 集还纳入第二轮已验收的 `PairedV2Geometry`、
`PairedV2Prefix4Data`、`PairedV2Prefix4`，共九个先前已验收模块。这三模块
分别绑定第二轮 prefix4 receipt 和证明提交
`6acf61cc28f227a9154363f2347c386ec01dffb0`。为保持 runner 代码原字节，
JSON 沿用 `p0_source` / `p0_object` 查找字段名；三条记录明确标注其实际
`validation_origin` 为 **Part 2 第二轮**，不能据字段名误认为 P0 生产者。

`LEAN_PATH` 首项仍是 P2 自己的输出根。新环境移除了已经消失的 P0 根，以及
从第二轮起就不存在的 Cli 对象根。Cli 源码和 exact dependency pin 保留，
本次观察的生产源码导入闭包没有 Cli 模块。其余配置的源码根与对象根实际存在，
11 个依赖 Git HEAD 与锁定清单一致且 tracked clean。

## 一次被 guard 拒绝的交叠尝试

初次 Data 编译启动时，最后一次 provenance 名单扩充仍在进行：旧六模块的
12 个源/对象摘要加三个工具入口，共 15 个 key；扩充为九模块后成为 21 个 key。
这次前后名单变化触发了 runner 的输入稳定性检查。

该次 frontend 返回 0，且产生对象，但 receipt 明确记录：

```text
verification_passed = false
failures = ["shared_cache_changed"]
shared key count: 15 -> 21
```

共同 key 的哈希值没有变化，源码与本地 producer 快照也没有变化；失败原因是
**被检查的名单本身在运行期间改变**。这仍是未验收尝试，不能用 frontend 的
exit 0 覆盖 guard 的拒绝结果。

原始记录保留在：

- [未验收尝试 receipt](../batch4-to64/attempts/20261012T123059143737Z-compile-ImbalancedChen.Certificates.PairedV2Batch4To64Data.json)
- [未验收尝试 raw log](../batch4-to64/attempts/20261012T123059143737Z-compile-ImbalancedChen.Certificates.PairedV2Batch4To64Data.log)

随后所有 runtime 输入完成冻结，root 以固定九模块名单重新编译并重放 Data。
下面的稳定运行才是本次 Data 验收的依据。后续如需改变名单、路径或环境，应先
结束当前运行并形成新的输入快照，再执行新的验证；历史 receipt 保留原样。

## 冻结后的稳定 Data 编译与重放

| 实际执行 | 结果 | 耗时 | 前后输入 |
| --- | --- | --- | --- |
| `PairedV2Batch4To64Data` strict frontend 编译 | PASS；exit 0；无失败项 | 7.281 秒 | shared 21 → 21 完全相等；local producer 完全相等；源码相等 |
| 同一对象的原装 kernel replay | PASS；exit 0；无失败项 | 4.014 秒 | shared 与 local producer 完全相等；重放前后对象相等 |

稳定运行的源文件 SHA-256：

```text
4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c
```

稳定编译输出与重放对象 SHA-256：

```text
61b3d3eeef416c6293ebdba0b5b1ac89a1d0d44e99be316f6139c2d51d60b259
```

Canonical 记录：

- [稳定 Data compile receipt](../batch4-to64/gates/20261012T123208523478Z-compile-ImbalancedChen.Certificates.PairedV2Batch4To64Data.json)
- [稳定 Data compile raw log](../batch4-to64/gates/20261012T123208523478Z-compile-ImbalancedChen.Certificates.PairedV2Batch4To64Data.log)
- [稳定 Data replay receipt](../batch4-to64/gates/20261012T123237308937Z-replay-ImbalancedChen.Certificates.PairedV2Batch4To64Data.json)
- [稳定 Data replay raw log](../batch4-to64/gates/20261012T123237308937Z-replay-ImbalancedChen.Certificates.PairedV2Batch4To64Data.log)

纯文本源码导入扫描曾报告若干对象路径缺项。该扫描是诊断，不能代替 Lean
loader 的实际执行，也不能据此断言运行被阻塞。之后观察的代表性对象及其
`.olean.private` / `.olean.server` 伴随部分实际存在，root 上述 Data 编译与
重放成功。本轮没有据静态扫描启动 cache 恢复。实际导入是否可用，以对应
模块真实运行结果判断。

这些 Data 记录不单独证明新 60 行或累计 64 行的积分界；后续证明模块、累计
语义等式与全模块 audit 的结果由相邻 `batch4-to64` 总回执分别绑定。

## 冻结输入与存档校验

| 文件 | SHA-256 |
| --- | --- |
| `verify_project.py` | `0830c9d46b524f791e4fc39fd5e84076d1561904026905ebc0dd4402aa1d6f5e` |
| `frontend-driver.lean.txt` | `ede18bb7c68c9950c2096ed79211c4c26948c21c28ba1985bf9f38d909024f50` |
| `project-environment.json` | `5352879b09979779eb70b7437af0493da3e566287d4d7dff665dcaf2bfb097f5` |
| `recovery-provenance.json` | `06c7101f95590d79d9aff8f3451b5e76859b478b34d97600ef6452a054c83ee8` |

这四个实际运行输入和两份旧来源链都按原字节复制。归档没有替换历史绝对路径、
重排 JSON 或规范换行。完整清单见 [ARCHIVE_MANIFEST.json](ARCHIVE_MANIFEST.json)，
重定位及 canonical 运行记录的绑定见 [RELOCATION.json](RELOCATION.json)。

在本目录运行普通文件校验即可核对存档：

```bash
sha256sum -c SHA256SUMS
```

此命令只核对文件字节，不运行 Lean。工具链和 package cache 二进制未内嵌在
本 Git 证据包中；另一环境复现需先准备准确锁定版本和所需 producer，并在
独立运行副本调整路径、保持期望哈希与检查门槛，随后形成新的实际执行回执。

由于共享内存限额为 8 GiB，继续使用单线程、单进程调度。归档工作只操作本
`verification/part2/round3/runtime/` 目录，不修改正在执行的 runner、配置、
provenance、源码或 import objects。
