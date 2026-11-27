# P1.5 整原子分组与原始 δ 余量：本批验收通过

两个有限目标及其 78 模块依赖链已通过原 Member guard 下的正常编译、精确单模块内核重放、全部 owned 声明完整类型与公理审计和最终独立只读复核。

- `P5SelectedRealWholeAtomGroups`：同一实数端点盒内的所有元组共享已计算的位置分组，保留完整乘积；C<1 时对完整列表重新分组。该目标有 16 个 owned 声明。
- `P5OriginalOrdinaryWholeAtomDelta`：在完整的 `1 ≤ A ≤ N^(1/3)` 和 `0 ≤ κ ≤ δ/64` 上推导三项物理余量，指数为 `1−3δ`、`2−4δ`、`2−39δ/8`，包括 κ=0。该目标有 2 个 owned 声明，含 1 个私有声明。

| 来源 | 本环境已验收模块 | owned / 私有 | 计数口径 |
| --- | ---: | ---: | --- |
| 既有 P1 待编译源码 | 40 | 499 / 32 | 原源码的 Member 环境编译验收 |
| 复用已提交 P3.6 源码及 API 修复 | 38 | 892 / 44 | 仅做必要的 Member 环境接入验证；新增 donor 数学功劳为 0 |
| 合计 | 78 | 1391 / 76 | 不代表新增 1391 项数学证明 |

30 个原 Member 边界输入保持原对象，旧 Member 模块正常编译和内核重放均为 0。恢复执行时逐项校验源、依赖和输出指纹，复用已通过的模块。失败尝试和一次已记录的中断均完整保留。全部传递公理仅有 `Classical.choice`、`Quot.sound`、`propext`。

这是隔离输出下的 direct Lean 验收；未声称新的 Lake named-target 或全导入闭包重放。原工具链、依赖锁、guard/core 和 `-t0 -j2 -M12288` 不变。[方法与限制](METHOD.md) · [验收回执](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [修复分类](REPAIR_CLASSIFICATION.md)

**完整 P1.5 仍未闭合。** 本批没有把原 `trueDDeltaRho` 的历史 owner fibre 认定为矩形原子，也没有供应全域统一的有符号中段估计。原小 β 选择规则、完整模数过滤、计数与互素均值使用同一系数，以及物理/自由碰撞支付仍须精确连接；最终常数和阈值必须先于所有实际 chart/row/mode/owner 索引。原 ProperPower 登记仍为 18/21，三个 HOLD 未关闭。

证据归档包含选定源码、所有保留尝试、正常/内核/审计日志、完整声明类型及公理、新对象和逐文件哈希索引，不含复用导入符号链接的原对象载荷。原 donor 来源及早期诊断的适用范围在 [provenance/README.md](provenance/README.md) 中明确区分。

归档：[下载](p15-whole-atom-integration-evidence.zip)，16,884,431 bytes，1866 个成员；CRC 与每个索引成员均已重新校验。SHA-256：`c051a061980a1e7099818a1d7d6b76e33f33876f5458ade007cd1ba5e1265a55`。
