# 本轮编译尝试与并发记录

本文记录实际发生的诊断和源码接收，不构成独立编译回执。最终验收只使用 `VERIFICATION.json` 明确绑定的成功命令、相同源码快照、对象及原 checker 日志。失败记录、旧辅助 Audit 和未被最终回执绑定的尝试不计入六目标验收。

## 证明修复

- Geometry 的第一次严格编译在 singleton admissibility 化简处失败。修复只增加 `Finset.filter_singleton`，没有改变定义或定理类型。当前源码 SHA-256 为 `a131b783d59540ea98cc11574f31489e2f75d519927445b49a2e4c688ab74cbe`；`attempt-20261012T185327333014Z` 留下实际严格成功记录。
- CellIntegral 在同一尝试严格成功，源码未改，SHA-256 为 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。
- 旧历史 probe 的初次错误涉及有限坐标投影和 `norm_num` 化简。修复增加两个私有 singleton helper，并显式使用已有 gate-region 与严格排序字典；采用的有理数数据和原公开定理类型没有改变。所有失败尝试的真实日志均保留。

## 共享运行时的并发观察

在已知本会话启动的 `attempt-20261012T190807188827Z`（run-05）运行期间，另一个工作会话也从同一 checkout 调用原 `compile_round3.py`。只读父进程核对区分了这两个入口；这里没有终止外部进程、改变原前端参数或绕过原调度锁。

probe 的两个私有 singleton helper 在实际前端读取源码之前被改成直接的 `funext i; exact Fin.eq_zero (j i)` 形式。该变化经逐项源码 diff 审阅后接收；它没有修改数据或任何公开定理类型。最终接收源码 SHA-256 为：

`60d27f341b74f61f0fc3e6b03c67ea7a35d999245f186b6d478bffbd533b901e`

已知 run-05 的实际源码快照、命令头、编译前后 SHA 均为上述相同值，原前端实际返回 0，耗时 244.389 秒。其主对象 SHA-256 为 `bea11498c61d1bc80c32a290c9d233d619cb60af1b5b0e66320c25ff652a6deb`。这份已知成功证据独立保存在 incident 下的 `accepted-known-run05/KNOWN_STRICT_SUCCESS.json`，该文件 SHA-256 为 `8c78cd2e3f674cef963c44cd84f8ff2aa48d2c4668489ac7ddb0f7cd1088b46c`。

run-05 后续的旧辅助 Audit 亦严格成功，原四目标队列最终返回 0。另一个工作会话的后续尝试在旧辅助 Audit 处失败，报告官方 `Aesop.Frontend.Basic.olean` 不存在，并覆盖了全局队列状态文件。已知 run-05 的 immutable attempt result 和原始成功日志仍保留。最终新增阶段只需要 Geometry、CellIntegral 和 probe 的已核对严格记录；旧辅助 Audit 不属于本轮最终六目标。

只读核对随后发现本地原队列的 683 个主对象全部存在，原官方缓存有六个主对象缺失：`Aesop.Frontend.Basic`、`Qq.ForLean.ReduceEval`、`Qq.ForLean.ToExpr`、`Qq.Typ`、`Batteries.Lean.Except`、`Batteries.Data.Nat.Basic`。这只是观测到的文件状态，未据此断言删除原因。恢复和后续验证须保留原缓存来源、真实命令和当前对象身份；不把恢复对象计为本轮重新编译或完整导入声明 replay。

随后逐 parts 清点将缺失集合准确细化为同六个模块各自的 `.olean`、`.olean.private`、`.olean.server`，共 18 个 payload；18 个现存 `.hash` 文件与原 permit 绑定一致。第一次恢复检查在解包、复制之前停止，写入数为零。最小恢复范围据此只包含这六个模块的 18 个缺失 payload：须从同六份原官方 `.ltar` 解到独立 staging，逐项匹配旧回执 SHA 后补回，不覆盖现存文件。实际清单与执行记录保存在 `p1-round3-runtime/cache-repair-six/`。

有关并发入口、源码 diff、缺失对象清单以及已知成功记录的原始 JSON 和文本保存在 `p1-round3-runtime/incidents/`，由本轮证据归档逐文件保留。全局状态被另一队列写入不改变已完成命令的结果；最终收集仍须逐一检查实际源码、对象、直接导入及原始日志。

## 后续缺项、快照与来源细化

18 个缺失 payload 已于 `attempt-20261012T193450106905Z` 实际补回，均匹配原绑定；随后闭包检查发现另有 83 个第三方主对象和本地 `Architect.Command` 缺失，因此该次恢复脚本的总体状态仍为失败，未改写成完整依赖成功。

独立硬链接快照在 `object-snapshot/attempt-20261012T193850752660Z` 完成，保存原 SHA 匹配的 700 个本地 parts 与 20,007 个原 permit 绑定的第三方 parts。硬链接保护后续 unlink，不保护原地覆盖；这项文件保存没有运行编译或 checker。

83 个第三方模块中，82 个的 246 个 payload 与原官方档及已有绑定相符，已在 `cache-repair-compatible-82/attempt-20261012T194329707518Z` 原样补回。其余 `Batteries.Tactic.OpenPrivate` 的旧 bytes 与官方档不同。进一步核对原 `round2/bootstrap-run.log` 及实际 raw log，发现它曾由原前端在 bootstrap 环境中实际生成；该次 bootstrap 命令使用了 `metadata_adapter = true`。旧 permit 对这个供应对象使用的泛化“官方缓存”标签不够准确。旧记录原样保存，不将该来源误写成直接来自官方档，也没有将不同 SHA 的档内对象替换进当前绑定。

本轮在 `supplier-recovery-two/attempt-20261012T194528243284Z` 对 `OpenPrivate` 和 `Architect.Command` 分别运行原 `Lean.Elab.runFrontend`，均使用 `trustLevel = 0`、`metadata_adapter = false` 和正常供应模块诊断模式。两次实际返回 0，分别耗时 2.116 秒和 2.333 秒；全部旧绑定 parts 与新生成文件逐项相同。当前回执将 `OpenPrivate` 明确分类为本轮实际重编译的第三方供应模块，`Architect.Command` 分类为本轮实际重编译的本地供应模块。它们不计入六个严格目标的次数，也不计为完整导入声明 replay。

上述真实重建记录包括命令、源码前后 SHA、源码快照、直接导入对象、原始日志及所有旧 parts 的一致性结果。最终收集专门检查 `OpenPrivate` 的这一实际来源例外；六目标严格前端、原 checker 与声明审计的验收条件保持不变。

## 第五层 saving 桥的导入诊断与 IR 恢复

`expanded/attempt-20261012T194706704126Z` 的 saving 桥严格前端在导入初始化处实际失败，原始错误为 `Could not find native implementation of external declaration 'Lean.registerNameMapAttribute._redArg'`。该次失败没有进入证明行，不计为该模块编译成功，也没有据诊断改变原前端的解释器支持或验收设置。

逐文件核对发现，同六个及后续 82 个已恢复官方缓存模块还缺少 `.ir` 和 `.ir.sig`，合计 88 个模块、176 个 payload；相应现存 hash 文件与各自原官方档内 hash 一致。`cache-ir-recovery/attempt-20261012T195344565396Z` 于 19:53:44 UTC 实际从保留的原官方 staging/归档恢复了这 176 个缺失 payload，采用原 SHA 检查及不覆盖现存文件的写入方式，耗时 0.126 秒。所有实际恢复文件又存入硬链接快照。`PLAN.json` 和原 result 保留逐项来源、官方归档 SHA、源码 SHA、payload SHA 及现存 hash 一致性；没有声称旧 permit 曾绑定这些 IR 的 SHA。

最终证据在 Lean 对象之外单独记录当前存在的 IR、签名及 hash 文件；这是验证后的文件身份清单，不宣称是每条命令的运行时加载轨迹。恢复操作本身没有运行编译或内核 replay。随后 `expanded/attempt-20261012T195404283745Z` 使用相同六目标、相同原前端命令和原调度锁重试；其结果由实际前端记录决定。

两轮原 bootstrap 的完整来源映射另存为 `supplier-recovery-two/BOOTSTRAP_SOURCE_MAP.json`。与本次 83 个恢复模块及最终缓存闭包的交集均只有 `OpenPrivate`，与没有旧 permit parts 绑定的 16 个模块交集为空；没有仅因这 16 个模块缺少旧绑定而额外重编译它们。

## Saving 字典的实际证明修复

第二轮 append 于 19:59:19 UTC 实际返回 1，耗时 314.811 秒。其完整 raw 只有 saving 源码第 38 行的类型匹配错误：`level5_ownCube_normalized_history` 的 `simpa ... using` 未通过；Cutoff 和新 Audit 尚未开始。诊断的 pretty output 仅显示 `primeHistoryTuple (4 + 1) history` 与 `primeHistoryTuple 5 history` 的区别，这不足以判定内部 elaboration 原因，不能说 `4 + 1` 和 `5` 不定义相等。

修复复用了已验证的 `ActualSelectedPrefixCellDecomposition.actualSelectedOwnCube_normalized_history` 写法：显式指定 `(k := 4)`，先重写 `actualPrimeTupleOwnCubeMinus_primeHistoryTuple`，再展开实际 density 与坐标并用 `rfl` 对齐。第四祖先版本同步采用该写法，保留原来的 `hcoords`。独立只读复核确认这项改动不改变定理陈述、历史投影、严格 own-cube、自然数 product 或 quotient level；修复后的成功状态仍须由后续实际编译决定。

`expanded/attempt-20261012T200116931794Z` 于 20:04:40 UTC 返回 1，耗时 203.813 秒；其唯一诊断为旧祖先字典末行 `No goals to be solved`。该次源码 SHA 为 `187b18b527757da8e5525f6d315726950d83e9ba501fbf92cf790ca839a360d1`。两处末行据此改成 `simp only [...] <;> rfl`，只在仍有目标时运行 `rfl`；新源码 SHA 为 `9f7632b3f1b429cdefaf2a19224e81f8d4445123df652ae66466def0a7304923`。第三轮失败记录原样保存，第四轮仍使用相同原前端、严格诊断、源码冻结和调度锁。

第四轮 `expanded/attempt-20261012T200534175385Z` 的严格诊断只报告两条 lint：第一字典不需要 `<;>` 的全目标战术组合，第二字典的 `rfl` 没有目标可处理。源码据此改为第一字典顺序执行 `simp only` 和必要的 `rfl`，第二字典只执行已经闭合目标的 `simp only`。没有禁用 lint 或改变 warning-as-error；修复后源码 SHA 为 `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e`，交由相同严格前端重验。

该源码在 `expanded/attempt-20261012T200952712536Z` 的 saving 严格前端实际通过：返回 0，耗时 159.484 秒，`trustLevel = 0`、`metadata_adapter = false`，原 raw 含准确 `FRONTEND_OK`。主对象 SHA 为 `ecc1959cc503dff7d13b721bef07bb66aa22ffd95c62d9cb744e32ffe53e023c`，源码前后 SHA 与实际快照均为上述完整源码身份。当前实际产物只有主 `.olean`；新目标快照明确记录 `.ir`、`.ir.sig` 不存在，没有把未生成的文件记为已备份。其后原队列继续 Cutoff 与 Audit；本条只记录 saving 的前端成功，最终 checker 状态以回执为准。

同一 winning attempt 的 Cutoff 模块在首次实际严格前端通过，返回 0，耗时 172.423 秒；源码前后及快照 SHA 均为 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`，没有修改候选源码。主对象 SHA 为 `831e9f794f078e93e5a03ab949c3d5d313b66c03e8be3fe2ce1a767c88fba8c2`。新目标保存记录分别位于 `object-snapshot/new-targets/attempt-20261012T201320623089Z`（Saving）和 `attempt-20261012T201619436917Z`（Cutoff）。这些文件保存不增加验证次数。

新版 Audit 在同一 attempt 实际严格通过，返回 0，耗时 552.546 秒；源码 SHA 为 `e3539741b7db8340b15c39d7334fff2ff84d44b0aa8dcd4f811449b1b08777af`，主对象 SHA 为 `91b86ba10014ed84ffa40e1893b872cc42717cbdf32fdfa835800c8e0311de4f`。按 defining-module metadata 得到的真实声明数分别为 Geometry 23、CellIntegral 23、SavingIntegral 15、Cutoff 9、Probe 30，总计 100（生产 70，probe 30）。实际传递公理并集为 `propext`、`Classical.choice`、`Quot.sound`；包含 private/generated 声明，没有按公开定理个数代替完整清单。

该 attempt 的 expanded 队列最终返回 0，六目标前端状态为 `FRONTENDS_SUCCEEDED`，源码闭包的本地模块数为 685。审计计算期间只观察 CPU 和日志，没有重启或更改源码、工具链、原 collector、允许公理集合或检查范围。原 checker 的最终结果另由本轮回执绑定。
