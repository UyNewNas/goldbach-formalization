# P2.6：运行时恢复与 Cell05 Shape 检查点

2026-11-27，P2 原环境恢复后，本检查点完成了 Cell05 最后一个 `P2OriginalSaving19Geometry05ScalableShape` owner 的 normal、stock kernel 和完整 owned 检查。三个命令均退出 0，随后通过只读 retained verification 和独立离线回读。**这完成了 Cell05 原字符串解析、解码和有限形状这一段；P2.6 全局仍然开放。**

机器记录见 [CHECKPOINT.json](CHECKPOINT.json)。全部旧上下文、旧失败和旧计数按原样保留，新成功属于单独的单 owner 阶段。

## 实际源码变更

九个 remaining9 候选源码在原工作分支均已存在。前八份源与原阶段、远端固定 head 的字节完全一致。唯一需要更新的规范源码是：

`ImbalancedChen/P2OriginalSaving19Geometry05ScalableShape.lean`

修改包含五处显式 `Fin` 界限传递，以及一处 `simpa` 的 lint 修正。声明、定理类型、导入、选项和 18 个公理打印保持不变。修复前后分别为：

| 源码 | 字节数 | SHA-256 |
|---|---:|---|
| 原失败版本 | 7,353 | `d530f5979a380f28ff750c47114b44a38f7d8af4c882f68ac1ffa0ae470cc905` |
| 本次通过版本 | 7,508 | `fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb` |

差异和独立源审查分别保存在 [Shape-repair.diff](cell05-shape-completion/Shape-repair.diff) 与 [SOURCE_REVIEW.json](cell05-shape-completion/SOURCE_REVIEW.json)。

## 三项新检查

实际作业 `64419527e8294cd2880cc7575368f6d5` 退出 0；包含前后证据检查和导出的总时长为 72.796 秒。

| 模式 | 结果 | 证明进程用时 | 关键验证 |
|---|---|---:|---|
| normal | PASS，exit 0 | 3.865 秒 | 显式 `--trust=0 -DwarningAsError=true`；18 个 `#print axioms` 逐项对应源码。 |
| kernel | PASS，exit 0 | 3.642 秒 | 固定的原版 `leanchecker --verbose` 检查目标模块。 |
| owned | PASS，exit 0 | 4.368 秒 | 显式相同信任与诊断选项；按声明所属模块检查全部 40 个声明。 |

完整 owned 清单包含生成的辅助声明；环境清单与序列化清单完全一致。每项均保留完整类型、声明模块及传递公理，没有 `unsafe`、`partial` 或新增 `axiom` 声明。公理并集仅为 `Classical.choice`、`Quot.sound`、`propext`。实际项目导入闭包为 126 个模块。

三项检查均绑定同一个 99,952 字节对象，SHA-256 为 `9907452a9498108f2212a5c5e881396ec6e1b84e4d2457e1e9f4dc0e540d40da`。固定 stock leanchecker 为 50,608 字节，SHA-256 为 `ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a`。

后续只读作业 `f6f812506f494df7b3e601044ff38501` 返回 `RETAINED_EVIDENCE_VERIFIED`，没有重新运行 Lean。独立回读再次检查了 40 个归档成员、命令、启动记录、结果、接受回执、同一对象、完整声明和所有恢复绑定。

- [单 owner SUCCESS](cell05-shape-completion/SUCCESS.json)
- [原 24 项与新 3 项的组合索引](cell05-shape-completion/COMBINED_INDEX.json)
- [完整 owned 声明](cell05-shape-completion/owned-declarations.json)
- [独立回读报告与精确 argv](cell05-shape-completion/INDEPENDENT_READBACK.json)
- [实际作业原始输出](cell05-shape-completion/RUN_TASK.stdout)

## 历史计数与失败边界

下表是不同原上下文的并列汇总；没有构造一个替代旧记录的总 SUCCESS。

| 阶段 | owner 数 | 接受检查数 | owned 声明数 | 本轮是否重跑 |
|---|---:|---:|---:|---|
| 原 connections13 前缀 | 13 | 39 | 112 | 否 |
| 原 ShapeArrays 独立修复 | 1 | 3 | 28 | 否 |
| 原 remaining9 前八项 | 8 | 24 | 116 | 否 |
| 本次独立 Shape | 1 | 3 | 40 | 本次新增三项 |
| 不同 owner 的汇总 | 23 | 69 | 296 | 旧证明命令重跑数为 0 |

原 remaining9 的 complete 尝试记录仍为 `newly_executed_steps=22`：21 项新成功、1 项失败，另复用 pilot 的 3 项成功。原失败 Shape normal 和早先失败的 ShapeArrays normal 均保留。原九目标上下文仍按真实停止状态保存；新 Shape 成功不改写它。

旧 normal 命令没有显式设置 `--trust=0`。保留它们的实际 argv、原 stock-kernel 和 owned 证据，不追溯改变旧命令的信任选项。

## 运行时恢复

恢复前的完整检查确认：34,656 个现存条目与原快照的内容相同；Mathlib 缺少 24,923 个文件，共 7,156,488 字节。本轮从 P1 原始文件恢复这些精确字节，并逐项回读。原 guard 文件没有改写。

由于恢复造成物理文件身份变化，旧 lstat guard 继续拒绝当前文件系统。独立的 v2 恢复协议对十个运行时根、59,579 个选中条目、8,042,816,961 字节进行了完整核对，生成新的当前 guard 和兼容性证书，同时保持 `original_live_guard_validator_passed=false`。随后检查原包、原 39／3／24 项记录和两个旧失败链，并对接 125 个 Shape 依赖。

首次 v1 capture 因未捕获原验证器的 `RuntimeError` 而失败；源码、打包内容和原 stderr 保存在 [attempts/v1](cell05-runtime-recovery/attempts/v1)。经限定修复、真实原 helper 的定向测试和独立复审，新的 v2 capture 作业 `d1c729427f824000b03e75cf043325a5` 退出 0。两个阶段没有运行旧证明。

- [恢复证书](cell05-runtime-recovery/CERTIFICATE.json)
- [恢复独立回读报告](cell05-runtime-recovery/INDEPENDENT_READBACK.json)
- [实际文件恢复记录](runtime-recovery/live-restore/RESTORE_OBSERVATION.json)
- [原 remaining9 完整恢复包](cell05-remaining8-recovery/evidence.tar.xz)

## 完整归档

| 归档 | 字节数 | SHA-256 |
|---|---:|---|
| [原 remaining9 状态](cell05-remaining8-recovery/evidence.tar.xz) | 403,524 | `e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4` |
| [运行时恢复证据](cell05-runtime-recovery/evidence.tar.xz) | 4,245,880 | `8a0b3afab2c32114fc124a69071160f05a1c3dc8ef84d4a19b3ae4866a66b8c6` |
| [新 Shape 完整证据](cell05-shape-completion/shape-evidence.tar.xz) | 1,057,200 | `3a7f08f9f47c68a25bbc300ea2124cbfecd5332a74e425e3dba494d0540630d4` |

三个归档均已按外部保留的长度和摘要完整回读。恢复归档超过工具单次日志上限，采用原前缀与两个精确后缀拼接；最终整包摘要一致。Shape 归档无截断。离线检查器、原执行命令、历史归档及布局说明保存在 [readback](readback/README.md)。

## P2.6 仍开放的部分

新端点 `geometryPacked05_parse_decode_shape` 证明：原 Cell05 打包字符串经过 `SourceJson.parse` 和 `decodeGeometry` 得到指定 `concreteGeometry05`，且该数据满足有限 `GeometryShape`。它没有完成所有 28,918 行、原 floor 绑定、所有权、积分或共同历史 saved-gain 的实际端点。

`Archive`、`Original28918`、`Original28918FloorBinding`、`OwnedSource`、`PullingOwnership`、`OwnedIntegral` 和 `ActualEndpoint` 的全局闭合状态保持开放。

后续最小已备源码候选为 `RowNumericsPureBridge`，需要先对接九个旧供应商的原证据；ArchiveSchema 与 SourceJson 的两个不同对象上下文不能混用。本轮沿已知 Git 指针补回了 HigherMoments224 的原回执，但其中 89 个 owned 声明全部属于 HigherMoments，不能把该审计升级为三个 analytic 供应商各自的完整 owned 验收。详情见 [下一关口](POST_CELL05_NEXT_GATE.md) 与 [analytic3 原证据补回](row-numerics-history/analytic3/REPORT.json)。Cell01 原 floor family 保持独立的 P3 关口。

本检查点保存到既有工作分支，不合并主分支，不把项目看板标为完成。
