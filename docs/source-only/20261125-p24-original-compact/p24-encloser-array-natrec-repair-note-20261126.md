# Q80 Encloser 与 ArrayTable：显式递归候选及隔离验证

## 结果与边界

固定生产源码为 `6e616f4e0372555f7a78bcdba3e198d0e277eec8`。两份候选在独立顶层模块中完成编译、原递推零/后继方程检查、`leanchecker --verbose` 独立重放，以及未修改判据的原完整 owned 审计。原完整 324 项源码/对象/工具快照、编译 registry 和既有 native 环境前后相同。

这些结果是隔离候选证据。未修改 canonical 源码、对象或 registry；没有授予生产编译、A/B/W 或完整 P2 验收 credit。ArrayTable 隔离测试仍使用冻结 6e 的 canonical Encloser 依赖。两个候选及其余修复组一起晋升后，须由原 canonical 门控验证组合后的源码。

## 唯一计算定义变化

| 文件 | 定义 | 保留的原递推 |
| --- | --- | --- |
| `P2OriginalCompactQ80Encloser.lean` | `logLoop` | 零次初态仍为 `⟨⟨ul,uh⟩, I80.raw 0⟩`；第 `n+1` 次仍将第 `n` 次状态交给 `logStep square n`。 |
| 同上 | `firstSeries` | 初值仍为 `(1/2,0)`；保留 `k=n+1`、系数分支、原乘除与幂次、奇偶符号及 `prev.2 + term` 顺序。 |
| `P2OriginalCompactQ80ArrayTable.lean` | `buildFrom` | 零次仍返回原数组；后继仍先执行 `appendNode g nodes`，再把该数组交给剩余迭代。 |

三处都改为显式 `Nat.rec`，避免原结构递归编译产生的 partial 辅助声明。原定义名称、参数、返回类型、所有数值和其他计算定义不变。独立方程文件对这三项原零/后继方程逐项用 `rfl` 验证。

仅两处证明体随真实编译错误正规化：`logLoop_eq_historical` 的 `simp` 列表删除实际未使用的 `ih`；`buildFrom_represents` 的零分支先明确目标为 `Represents g (n + 0) nodes`，再使用原假设。没有修改这两个定理的 statement，也没有新增数学前提或选项。

`source-transformations-02.json` 保存完整原块、候选块和两处 proof 变换。将这些变换逐项反向应用，精确恢复两个 6e 原文件 SHA；变换块外的源码字节完全一致。独立只读复核也确认了三个递推的初值、后继、符号及运算顺序。

## 实际运行

| 阶段 | Encloser | ArrayTable |
| --- | ---: | ---: |
| 编译 | 8.805052 s，exit 0 | 3.582064 s，exit 0 |
| 原零/后继方程 | 3.493339 s，exit 0 | 3.494401 s，exit 0 |
| 独立 replay | 29.297010 s，exit 0 | 7.411929 s，exit 0 |
| 原完整 owned 审计 | 4.732945 s，exit 0 | 4.833429 s，exit 0 |
| 全量 owned 声明 | 193 | 19 |
| 完整类型 UTF-8 字节 | 58,657 | 8,421 |

任务 `8d56c275c9174285b46c320201d11d33` 正常结束：exit 0，外层 142.860534 s，采样峰值 4,226,121,728 B。固定参数仍为 `-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000`；原 audit 模板 SHA `2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`，每份只替换两处目标模块名。

本地再次从完整 raw audit log 核对：serialized/env/逐声明输出三套 inventory 完全一致；全部 owned 声明 safe、非 partial、非 axiom；没有遗漏或截断类型；传递 axioms 均为 `propext`、`Classical.choice`、`Quot.sound` 的子集；原 loaded-project closure 精确相符。三个原 `_unsafe_rec` 名称未在对应候选 owned inventory 中出现。

## 失败记录与精确证据

- `p2-encloser-array-natrec-01.*`：任务 `8f5b44dde32b4d34813b4992d89e153f` 在 Python 导入时失败，Lean 未启动。原 runner 导出名为 `PIN`，wrapper 最初误写为 `MATHLIB_PIN`；后续仅修成 `PIN as MATHLIB_PIN`。
- `p2-encloser-array-natrec-02.*`：任务 `7c0234b566694aeeaf71340d07c8a268` 真实报告上述两处 proof 正规化问题。原输入检查全部通过，未运行后续 replay/audit。
- `p2-encloser-array-natrec-03.*`：最终完整隔离通过；exact MCP stdout 23,388 B，SHA `99b3549a611cc77a906b73ec77bf982bd25929ea114bfa21aa9c7183eea9bdaf`。
- `p2-encloser-array-natrec-evidence-20261126.tar.gz`：完整 attempt 002/003 的 30 个原始文件，共 2,381,355 B；含源码、原实例化 audit、方程、全部 stage log、完整 parsed owned 输出、前后快照和 receipt。gzip 392,153 B，SHA `7e5a5463577e5904aa88ebecb81d31a1b301c104a88897e8490acfc556d45f3f`。
- `p2-encloser-array-natrec-evidence-verification-20261126.json`：归档逐文件字节数/SHA 和本地独立的完整规则复核。
- `submitted-command-bindings.json`：三次实际提交 Command 与归档 wrapper 逐字一致，包括最后 LF。

最终候选 SHA：

- Encloser：`139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058`。
- ArrayTable：`b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d`。

已有完整 321 风险扫描的 27 项清单保持冻结；这份新证据清单独立于该清单。原 25 个 partial 风险与其他修复模块的 canonical 结果须分别跟踪。
