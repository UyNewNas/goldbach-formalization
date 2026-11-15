# 真实R24严格审计器：原件复用，静态HOLD

本包只把现成严格审计工具适配到真实R24的精确库存。它不是新数学证明，不改任何102份数学源、statement、前提或终点；不是R25数学重编，也不制作新R24 driver。没有本地Lean/Lake/LSP/nativekernel、项目helper、stage/setup/guard/fixtures执行。所有source/runtime/object/CI资格仍待当前范围独审与真实原件绑定，`ready=false`、`formal_credit=0`。

候选 [CandidateAudit.lean](CandidateAudit.lean) 为26345B，SHA256 `99eab937d22dc3e20f8ba93fbd6bf581879bc491f046a14724aa1924bbc012db`，Gitblob `cab376b2b6702a3d21d4fd6cff2a49792fe8a236`。它复用原 `u02-p2-exporter-only/CandidateAudit.lean` 的26345B/`80f718e9…` 原件；原件没有修改。旧published记录为`9bd166df`下的 `docs/source-only/20261115-resume/source-expression-and-r22-auditor/r22-exporter-only/CandidateAudit.lean`。旧T07 AL `a3203a48…`只覆盖原R22 source applicability，不能自动批准这个R24后像。

## 只有两行差分

第226行保留原exact assert，只把 `102/3628/3787` 改为本轮真实 `102/3590/3779`；第227行把对应错误标签 `Exact R22` 改成 `Exact R24`及同一组数字。`EXACT_DIFF.patch`与`SOURCE_REUSE_PROVENANCE.json`记录完整两行。反向替换后字节、长度、SHA和Gitblob恢复原80f；其余代码没有重写。

102条数学imports与原module数组都逐序等于真实R24 manifest `52c614d4…`。额外标准import仍为原严格审计器的`Lean.Util.FoldConsts`。从`requiredTerminal`到EOF的全部字节相同：精确owner/multiplicity、loaded modes、codegen names、逐root fresh checked type/body worklist、body presence、实际kind/flags、primitive边、AX、安全闭包、metadata-only companions及原终点门均保留。原`graphEmitted`只去重输出，每root的pending/seen仍重新建立；safe logical闭包拒unsafe/partial，actual defnInfo/opaqueInfo executable companions仍须完整AX审计且proof/termination credit为0。没有放宽条件、删exact assert、改数学证明或借新前提。

## 真实库存与缺口

本包直接只读ROOT已取得的真实ZIP：`8825963B/8124f443…`，run43670444098、attempt1、head`b125727f…`、source`1d586700…`。所用原始member均与T07本地原件逐字节对应并经ZIP CRC读取。`batch-types.log`为9579893B/`4f2ba144…`。

原log含102个SERIALIZED、102个MODULE、3590个唯一DECL及最终COUNT3590。每模块serialized names、environment names、DECL names完整重数相等；extra_codegen_name_count合计3779。`R24_EXPECTED_INVENTORY.json`保存逐模块canonical root名字及摘要、声明和codegen计数、两个新增`firstMax_nil/firstMax_cons`真实theorem记录。全部3590根的所报unsafe/partial/axiom flags为false；这些根字段与所报AX不替代当前dependency闭包审图。

3779来自本轮原数据，不是旧R22数量加减推算。但原成功路径只输出extra-codegen数量，没有其实际名字数组；不能把3779描述成完整codegen名字库存。严格原件本来就要求打印其真实数组，因此后续新stdout解析必须核完整名字、模式、owner、primitive图和逐root AX。`_private.`名字前缀统计只是名字辅助信息，不作为逻辑或visibility分类规则。

R24实际使用的CandidateAudit仍为19752B/`43d3b26c…`，生成器未采用严格80f机制。根因需要准确表述：`collectAxioms`每次公共调用已有局部seen；导入声明命中`exportedAxiomsExt`时会用编译缓存AX列表，且原R24没有当前dependency body/type安全性、owner、kind与直接边审图。没有证据支持“实际R24跨root globalvisited造成漏报”，也不宣称原AX记录已经被证明错误。这里是严格合同与证据缺口，不是已发现数学命题错误。

## 先查现成，复用现成

本地有界exact-inventory检索只找到原80f严格source，未在所查范围找到R24-specific严格后像。已读known b125完整九文件commit差分与原auditor绑定，确认本轮实际仍旧生成器。remote只做三次成功metadata查询：R24 auditor commit top8、当日auditor commit top10均空，r24 branch page30只返回已知分支；另一次exact branch fetch被connector URL校验拒绝，没有取得branch-head结论。`inputs/REMOTE_DEDUP*.json`保留原响应；这些不是全历史不存在的断言。本包继续复用现成80f算法，不另造算法。

## 复用原R24 kernel证据，不为审计重复数学工作

真实R24的27份数学源各有一次调用，保护75没有源调用。FinitePi在step17编译一次；step18再次列入target但没有第二次源调用。历史85/17提案没有实施，不能为匹配它再编成功模块。

原`batch-checker.log`为6235B/`0289f1a2…`，恰有102个唯一replaying行，顺序为manifest逆序。原`BATCH_ACCEPTANCE.json`为6229B/`21158720…`，绑定8975981B/`20998c91…`的`BATCH_OBJECTS_BEFORE.json`，后者包含53,254个path→hash元数据。T07说明原workflow的pipefail、后继BATCH verify及ROOT原GHA成功状态支持原checker成功证据；light没有独立checker exit receipt，本包保留`checker_exit_code=null`，不造exit0。

该原R24 checker证据可在ROOT/T07将实际被加载的同一102对象及其source、private/server/IR、setup、allactualinputs、runtime/toolchain/ABI与原快照、collector/retention逐件资格绑定后复用。严格审计器的`kernel_replay_required`逻辑角色字段保留，指向该可靠同对象kernel证据；不因此安排重新运行同一可靠kernel，也不重编任何102数学源。当前尚未取得或资格这些对象正文。缺原件就HOLD并补真实绑定，不能以重编或额外kernel支出作默认补救。

## 未来仅审计工具的条件计划

本包没有runtime、workflow、driver、fixtures或stdout parser实现。后续若ROOT决定做GHA audit-only，应先取得T07对本26345B/`99eab937…`后像的当前R24 source AL，再把已qualified原R24对象以全102数学源compile-denial加载。只有新审计工具自身可有源执行；数学源、C/native/link和bootstrap cold fallback都必须为0。source/对象当前身份应与原R24同一组绑定，不能把原hash列表当作已取得的正文。

同一组**精确已审**auditor bytes须分别绑定stage、qualification、preexec、proof、final、retention；final与retention为独立门，不能用当前文件selfhash代替独立approved hash。原guard的串行slot、trust-zero、-t0/-j2/-M12288和deny-before-exec边界保留。原失败stdout/source/output与collector证据须保全。

新审计stdout应完整解析全部3590 DECL及canonical owner/private/generated范围、两份完整types、全部loaded-module modes、实际3779 codegen名字数组、primitive dependency nodes和每root重新计算的type/body安全/AX闭包。global去重只对输出，不能跳过逐root检查。原15条终点记录及原ordinary integral endpoint的完整类型继续逐值比较；不改变其conditional component范围。未知kind/owner或缺body/edge、非允许AX、safe closure到unsafe/partial、缺图或缺原件均HOLD/拒绝。implementation metadata持续零proof/termination credit。

`ROOT_AUDIT_ONLY_BINDING_SLOTS.json`将当前source AL、audit-only实际head/tree/parent、物理资格、同对象kernel绑定、当前loader closure、guard policy、原process argv/cwd/exit/stdout/stderr、fresh parser/graph重算、final与retention分别留作硬槽位。本轮仅冻结source与静态差分。Lean语法/API/资源、实际执行、当前物理对象及完整证明合同均未验收。
