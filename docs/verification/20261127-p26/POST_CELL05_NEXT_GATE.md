# Cell05 Shape 后的 P2.6 下一关口

**结论。** 以 Cell05 Shape 日后通过三项检查为条件，目前有精确源码、且新增 owner 最少的已列语义候选是 `ImbalancedChen.P2OriginalSaving19RowNumericsPureBridge`。它的十个项目模块闭包只含一个新 owner。**先做九个旧供应商的只读证据对接，并确认目标没有既有成功记录。现有本地证据不足以直接首编。** 此桥与 Cell05 是独立支线，Cell05 的 Shape 成功不会解决它的供应商冲突。

以下依据本地固定源基线 `46d7a9b20373700d7e862116344abfb28243289f` 及本轮恢复检查。路径均相对于共享工作区。本报告没有查询云队列或看板、运行 Lean、回放内核、修改源、发布或新增验收。

## 1. 已有验收，保留原上下文，不重跑

- Cell05 已有 prefix13 的 39 项、单独 ShapeArrays 的 3 项、remaining9 前八 owner 的 24 项原记录。117/125 是嵌套供应闭包，不是可另加的独立验收计数。若本次最终 Shape 新获 normal/kernel/full-owned 三项，直接结论为 cell05 原字符串解析、解码与有限形状；56 个几何行的结构边界不提供十条数值条件的证明。
- P1 原 task `job_830622aeef50453fb1dc2e58a6211831` 已成功。原单 owner `P2OriginalSaving19RowNumerics` 具有 normal、内核调用和 20 个完整 owned 声明证据，源 SHA-256 为 `4be5f94041cc77997b8ad720966bc87938824493287480dd13d8abc7d95ef98e`，对象 234,920 B、SHA-256 `5c58c0b5f8d96c2c379459d6acb15859decebf59aa6518e16c70dba6e3597fb0`。附审 `job_18f63882b3c441a89451cdf3add0fd1f` 已核对原 guard/state 和 stock leanchecker 文件身份。保留 blue-member-build 原上下文。该 owner 定义数值判据，并未证明某一个实际行满足判据。
- Cell00 已有 56 原行检查，Cell01 已有 144 个有限行结果、通用原 floor 传递和 row000 原 floor bridge；这些供应商的既有检查不进入下一批新增命令。

## 2. 最小新 owner 前须补的原证据 join

目标真实源码为 `p26_remote_audit/scope-audit/reference/ImbalancedChen/P2OriginalSaving19RowNumericsPureBridge.lean`，807 B、SHA-256 `57e18693e4eb8b80487c4ebebbd9f5a3edf73668e10711799d2a4240e0b9ed06`。三个直接导入为 `P2OriginalSaving19RowNumerics`、`P2OriginalSaving19RowNumericsPure`、`P2OriginalLogMomentQ96ArithmeticBridge`。第 10 行的 `rowDataChecksFor_iff_original` 对任意 `v : Fin 9 → Fin 8 → ℚ` 及原 `GeometryRow` 证明两份十条谓词等价，源码给出的证明是 `Iff.rfl`。

| 九个旧供应商中的位置 | 现有证据 | 本地识别的下一动作 |
|---|---|---|
| RowNumerics 原 owner | 原上下文三项和对象已恢复 | 对新命名空间给出原输入关联；保留原三项。 |
| Q96ArithmeticBridge | canonical checkpoint 有三项直接证据 | 对接相同源、对象、原受理记录。 |
| ArchiveSchema、SourceJson、RowNumericsPure、Q96ArithmeticPure | canonical checkpoint 显式提供四者各自 normal、kernel | 寻找其他原包中的完整 owned 记录。当前 checkpoint 的资料不能证明其他地方从未做过 owned。 |
| DegreeSixLogGapSoundness、PositiveAffineSimplexLogJensen、Q96Checker | 已有 accepted analytic 源/对象 pins，HigherMoments 224 模块闭包中有来源指针 | 三个原 facade-retry 文件在已探查 P1 路径未找到。先从备存/原存储按既有 pins 对接具体声称的旧证据；有界扫描不能证明全局缺失。 |

最直接的冲突在两个共用依赖。原 RowNumerics 的 ArchiveSchema 对象为 `30ffc4c239486de337c5ca19931caa5c751e53d067381f773f7c588fbd8e9781`，canonical 对象为 `8c3b41bd6b27e92b7a3c724b5d5ee9b191b4a4079fb40bd3ff5daad34129f9cc`。SourceJson 相应为 `865aaca31da595e69687b69f7dc0aa69edc01800d55e286cd5ba767239ac4d3f` 与 `ec7361a2e508c323bf2dfa5f384d31a4bd71ffd47e032bfbf428c13bc1c2e467`。两对源码相同、对象长度和 SHA 均不同。须建立单一实际导入上下文的证据，不可用 Cell05 的运行时证书替代这两项项目对象对接。

## 3. 新工作与仅 owned 项的边界

- **首编候选。** 若原证据 join 通过，并在目标宿主上只读核对队列、已有目标对象和各态收据，确认尚无相应成功步骤，则只为 PureBridge 补未完成的 normal、stock kernel 和完整 owned。此前 P1 在列明目录内查无该桥，不是全局去重结果。即使通过，仅能给出一个数据无关的等价定理，不给具体行、积分或 endpoint 新信用。
- **仅 owned 的候选项。** 上表四个 canonical owner 在所查 checkpoint 的 full-owned 覆盖尚未证实。只有恢复搜索和宿主去重确证需要补项时，才在原始、已接受的对象上单独做完整 owned；当前可确认的“从未执行过的旧 owned 命令”数未知。不把它们预排为四条必跑，也不重做 normal/kernel。
- **Cell05 本身。** 固定 HEAD 的 119 个 cell05 相关源条目中可定位原始 GeometryData05 与 MomentData05；所查清单没有已就绪的 Cell05 原 Archive 索引→moment/floor/所有权一体化后继 owner。新增 Shape 只能作为将来这类连接的供应商。全 28,918 行、所有权、积分、共同历史 saved-gain 端点继续开放。

## 4. 需要 P3 的独立关口

Cell01 有已经打包的 **11 个**原 floor owner，共 **33** 个计划检查。先读 P3 队列及 `/workspace/p26-cell01-family-p3-inputs-557a12f3bcd7/PREFLIGHT.json`、`/workspace/p26-cell01-family-p3-stage-557a12f3bcd7` 和 v3 接收/部署目录，保留既有部分成功。要求先通过 791 个旧供应商和 11,517 个外部运行时模块的无证明 preflight。本轮最近的 P3 工具观测为 Session terminated，未读到队列或文件；不能据此判定远端无更晚成功。

第一 owner 的真实源码在 `materials/upstream/cell01-family-p3-preparation-v3.tar.xz`（664,856 B，SHA-256 `05db077182e91606f800569f621ec0f13f79e0642500a8f6f930391a522e1bb4`）内的 `source-package/sources/ImbalancedChen/P2OriginalSaving19Cell01OriginalFloorInterface.lean`（4,251 B，SHA-256 `dcfebb22ceae165a75e78fbc612a4b0d46ef3381e81cf637f71d6d45c8d5d504`）。直接导入 OriginalFloorTransport、Geometry01BoundedAccess、Moment01Shape。其后是九个 16 行块及一个 144 行聚合。P3 原 row001 完整证据依既有约定原位复核。已有 v3 首次执行资格不等于验收。

另有三份 cell01 Archive 候选源。第一份 AllRowArithmetic 直接聚合 144 个已验有限行供应者，独立于新的 floor family；第二份 ArchiveBridge 依赖该 family 的 AllOriginalFloorBridge 及 ArchiveCore/geometry/moment；第三份 ArchiveRowArithmetic 需要前两份。三者的项目源码闭包各为 551、830、832。不能把三份源码或 P1 的额外对象位置记作九条已验命令。

## 证据路径

- `P2_6_recovery_status_20261127.json`；`materials/p26-work/docs/plans/20261127-cell05-shape-completion.md`；`materials/p26-work/docs/verification/20261126-p26/continuation-557a12f3bcd7/README.md`。
- `p26_remote_audit/scope-audit/MINIMAL_SEMANTIC_ENTRY.json`（早期 job 未知状态已被后续原 task 回读更新）；`p26_remote_audit/scope-audit/EXACT_HEAD_TREE_SCOPE.json`。
- `p26_remote_audit/row-numerics-recovery/REVIEW.json`；`p26_remote_audit/row-numerics-recovery/BRIDGE_DEPENDENCY_OBSERVATION.json`；`p26_remote_audit/row-numerics-recovery/identity-addendum/REVIEW.json`。上文按时间采用补审的新证据，不把旧资料中的等待态延续到本轮。
- `p26_remote_audit/cell01-r2/STATUS.json`；`materials/p26-work/tools/p26/cell01-family-p3-join-20261126/P3_DEPLOYMENT_CANDIDATE_v3.json`；`p26_remote_audit/scope-audit/CELL01_ARCHIVE_CANDIDATE_SUMMARY.json`。
