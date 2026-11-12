# Fine 与八个 Winner 目标的 Stored 选源独审

本轮裁定为选源与 071 证明结构的源码审查。逐字复核使用 Git 固定对象、既有远端证据中已保存的 Lean 源、JSON 与文本片段。没有运行作者的选源脚本、生成器、安装器、Lean、Lake、guard、checker、数值判定或 CI。

## 源码、依赖与已验范围

从原 Fine 清单的 1,808 个项目模块出发，新增加八个 Winner 源，八个文件的原件和 import 向量均由公开提交 fecfaff4fe34657cbb1e70a24c6fbb53b0d27d54 逐项比对。Fine 范围内只变更 Stored000–071 的证明源。其余 1,736 个记录与原 Fine 清单逐字段相同，原始 43 个 native 记录也完全相同。联合源集合有 1,816 个不同的安装路径，数学模块共 1,859 个。按模块名、源码 SHA256 与原始 Git blob 三元组升序取紧凑 JSON，1,816 项目的摘要为 41ae7de0255d269011dc70ddb23fd1ba6092f394b17bd98b9cda4d2306d3663d。

逐项从 124d09f9fc74e7b78261e2471a573f1657b5633e 的 commit:path 读取 72 个原文件。对记录中的唯一旧文本、实际新文本、左右字节、全文件 SHA256、原始 Git blob、直接 import、rows_size 和公开 source_index_at 类型独立复核。71 个整块的证明文本在替换各自 sourceIndex 的基址后，与实际通过的 Stored000 对应片段逐字一致。000–019 的新文件共 4,778,214 字节，逐项等于原三次通过的 artifact 内实物。已验范围沿用 run 43033551155、43080955096、43122130246 和 artifact 13874148553、13890440332、13910907180 的原独审结论。它们的狭义数学结论是实际行数与 sourceIndex 对齐。Q80 数值、原数据的几何解释、全部 Stored 或 Fine 的结论各有独立门控。

在本冻结快照中，020–030 为固定期望字节，031–070 的整块与 071 的尾块均未取得这份清单所需的远端验收。须用实际同源 artifact 更新 020–030 的状态。归并这样一份以后到达的收据也须先核对完整类型、传递公理、源及复核对象。原文件变换不会转移先前的内核验收。

## 尾块与反向依赖

071 的原始行数组、rows_size=1817 和公共类型原字节保留。它有 28 个 Fin 64 的私有子声明，最后一个完整块从 1728 开始，最后一个 Fin 25 从 1792 开始。最后的公开分支由前一边界和 j.isLt 得到 1792≤j.val<1817。在这个区间 j.val=1792+j.val%64，因而该余数严格小于 25。它恰能送入最后一个私有声明。所有内部偏移和数组读取保留其界证明，未额外强加取值许可或更改常量。前 28 个分支与既有通过的模板逐字对照，仅替换总长度，最后一支显式证明余数更小。选源 SHA256 为 41c5a10b4812e3193c0cc105ad64de4f607ef6c732728e3935b6e1632aef70b9，Git blob 为 9a65b279121837d087c05e7a890671a3a9807780。这里核对的是分段证明的逻辑与源码，所有 decide +kernel 和私有声明的实际验收仍待远端。

按这 1,816 个模块的原实际 imports 逐边计算，72 个修改点含自身的反向闭包恰为 266；其余 1,550 个源位于闭包外。Fine 和八个 Winner 的实际项目闭包合并恰覆盖全部 1,816。Fine 含全部 72 个改写块；Winner 中 RawWinner 和 SixthWinnerBankRead 各不含任何 Stored 块，其余六个各含全部 72 块。当前需单独取得新证明源证据的有 52 个 Stored 与八个 Winner，另外 1,736 项的相同源码须有真正可用的依赖输出。

## 运行证据边界

保留的 20 份 source/olean/hash 及历史重放仍有价值。原三次 Stored artifact 没有 ParentTypes 的实际对象与原依赖包的完备输出，也没有足以恢复 Lake leanArts 的全部 ilean、C、setup 和真实 trace。后续新批若保留 parent 的原对象，可在绑定实际依赖环境后用于具体重放；单一 parent 对象依然不足以证明完整 Lake 缓存命中。沿用 T02 复核 d2ffa97c6e6a7337d7fb7149ae32ceb7474caaaf1a2303a4fdcd809931d2c350 的边界，实际可恢复的完整模块集合仍为空。43 个 native 的 source/hash/canonical/guarded-object/实际 import 环境与所有数学模块的 fresh kernel 和完整序列化声明、公理及 byte-level 运行门控仍然独立。新增私有块改变了声明集合，不能沿用旧清单的声明数。实际审计 wrapper 的选本和重放名单需由后续 driver 显式固定。此计划的 driver_ready 为 false，未触发新的 CI 或任何主树改色。

## 已落实的两项元数据校勘

原登记 2c3a27728db5cd7bc13ba077b1c7c8f50b0459106708f7d6da5da619b086db4e 保存取证原貌。原始提案遗漏 72 个 pre_input.origin，而原 Fine 的 materialize_record 会先读该键；同时误把旧 Fine 的 efca98… 两元组摘要留在新目标中，后八个目标只有名字。单独校勘登记 7bd7bbe2771640db5e177ee459fb68ecde74657c626a802cd14edd840d09ca80 解决这两个输入歧义。逐字段比对证实，所有 1,816 条源记录中仅 72 个 pre_input 新增了对应原 Fine 的真实 Git 出处，所有证明字节、变换及安装路径均没有变化。

已对九个新目标的 actual import closure、外部 import、两个源摘要及全集的无环性独立计算。每个 closure_modules 是集合清单；实际构建使用 import 拓扑。Fine 1,808 的兼容两元摘要为 cbfab9b665a35824f1215eb96a19d0dcf4490471d8a462c0147c309191a27b71，三元为 643ec0de6be762f54d44c92ca78ef02b374bfcbb0980fd487673119c8de2f91b。全集 1,816 的两元摘要为 51e527a1da586b0d1e3ca2d3954f7da807f4adf47f9f4a9412b70c7d853ed385。未来 driver 须把全集和每个目标分别写入与实际物件绑定的证据。旧 stage 仅将 targets[0] 写入摘要，其余原资源、数据路径及实际依赖恢复责任均须继续绑定。

选用的具体提案为 PROPOSED_FINE_WINNER_SOURCE_SELECTION.stage-corrected.json，SHA256 为 8bae4da647ca49642bebf5076495a836ed4230dd1d5a8d59e6fa2788d5f36b93。两份作者包内的 22 个文件共 8,553,547 字节。逐文件原始 SHA256、Git blob、源和发表目标在 FINE_WINNER_STORED_SELECTION_ALLOWLIST.json，其 SHA256 为 8ee456e1cab875f74e25497a2ca90a77e80aca7dbe85207dd45c7190317fd868。本次可发表的是带勘误的选源证据，远端 driver 的授权、安装及实际执行均不在此表内。
