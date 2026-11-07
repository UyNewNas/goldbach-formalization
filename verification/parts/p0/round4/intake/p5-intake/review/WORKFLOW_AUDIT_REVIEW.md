# Part 0 Round 4 workflow 与审计独立静态审查

**结论：15 项静态检查全部通过；没有遗留的发布前静态阻塞。此结论不是新审计的 Lean 编译、内核或 CI 回执，实际验证仍由 Root 在明确的新集成 SHA 上执行。**

四模块及真实生产者声明计数如下：

| 模块 | 固定生产者提交 | 实际声明数 |
| --- | --- | ---: |
| `StoredHistoricalBoxPermit` | `744316efd1887f21c91dd4b63c218fa27704c931` | 14 |
| `PairedV2Batch4To64Data` | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` | 72 |
| `PairedV2Batch4To64` | 同上 | 207 |
| `PairedV2Prefix64` | 同上 | 121 |

当前四个生产文件均与固定来源逐字匹配，总计 414。已由 Root 显式导入根，workflow 又明确执行四个 `lake build` 目标。导出采用实际 defining-module 清单，含 private/generated，Lean 内部与 Python 消费端都强制四个分模块计数和总数。原主桥独立打印，不计入 414。

## 审查通过的门槛

- 原完整 build 90 分钟、根 stock leanchecker 25 分钟、根公理审计 10 分钟、Round 3 类型导出 10 分钟均保留。
- 新四目标缓存构建 10 分钟、Round 4 完整类型导出 25 分钟，实际子进程上限 1,440 秒。
- build、根重放、根公理、Round 3 类型、Round 4 目标、Round 4 类型六个阶段全部进入 required outcomes；skipped/failed 无法被当成成功。
- Lean 审计开启 `pp.all / pp.proofs / pp.deepTerms` 和高打印步数上限；完整与 readable 字段出现 Lean 省略字符即失败，Python 再核对字段、数量、唯一性和模块归属。
- 在输出每项类型之前，Lean 按实际环境拒绝 unsafe 声明、own axiom 和标准三公理以外的任何传递公理。
- 类型导出固定源码提交、冻结配置、输入源文件与 `.olean` 及 `.olean.*` 附件前后身份；源、对象集合或 HEAD 改变均失败。实际运行仅编译辅助审计，不宣称重编生产模块或重新重放它们。
- 对正常 `lake env lean` 清除继承的 LEAN_PATH/LEAN_SRC_PATH，调用既有 pin 检查。
- artifact 继续 always 上传阶段日志/时间，明确包含 `.lake/part0-round3-types/` 和 `.lake/part0-round4-types/`，并保留 `include-hidden-files: true`。
- 当前主桥源 SHA256 仍为 `68a2a3aad8ccdc73ed8e5076e31b9984bc659c307d71150920a71b5fc98f067d`，`hLower/hUpper` 未隐藏或被宣称解除。

## 找到并已修复的具体问题

初版新 Python 脚本的首处诊断正则只接受 `error:`，会漏掉 `error(lean.synthInstanceFailed):`。对 P5 原始失败审计日志的纯 Python 消费测试显示：初版误报日志第 8 行，而实际第一条在第 4 行（Lean 源位置 47:23）。Root 只修复新 Round 4 脚本使其接受 `error(code):`；原 Round 3 源码未动。

复查同一原始日志后，修复版准确返回 `47:23` 的 `MonadWithOptions CommandElabM` 错误。修复前诊断、修复前/后源快照和结果都在此 review 目录保存。本审查没有启动 Lean/Lake/CI，没有修改 Root 文件。

## 报告时必须保留的范围

输入快照沿用既有机制，覆盖明列模块、根直接项目导入、配置和辅助脚本；不能描述成整个递归依赖闭包的逐文件快照。`object_parts` 绑定 `.olean` 和 `.olean.*` 附件，不能描述成所有生成物（例如 `.ir`）的哈希。

S1LowerRosser 是另外接收的既有 goldbach 依赖证据节点，不在四模块/414 项清单，也不在现有根依赖闭包。当前新增根导入及四目标检查不使它自动获得这轮 root CI 覆盖；它的 8 项证据应单列 P5 固定单模块三门及 P0 原件接收检查。任何新集成 CI 成功仍不闭合解析 K、c、hLower、hUpper。

## 复查文件哈希

- `.github/workflows/lean.yml`：`82a51ff3fdc1a1240c8f6faf037220c0c54b932ee3077881379f50492f24e698`
- `verification/parts/p0/Round4Audit.lean`：`c8696d7098e458317054caa46066fca5f4b2aa92093bdf722246409244444beb`
- `verification/parts/p0/check_round4_types.py`：`7d10845d22d790004caad2dda34d103df7e8228832aa206ed848a0d7d77f4429`
- `ImbalancedChen.lean`：`d6a0af92c0827bc2f1ae30a12f895f46f8048049fdca694e89fc3678e202f449`
- `ImbalancedChen/CurrentMainTheorem.lean`：`68a2a3aad8ccdc73ed8e5076e31b9984bc659c307d71150920a71b5fc98f067d`
- `verification/parts/p0/check_pins.py`：`276072bb14bc52fcd9544bb3557870b1edf6d3ab2ff8aaf8360ad541f0fd3633`
