# P3 Wall Consumer Continuation Implementation Plan

> **For agentic workers:** Use the already assigned owners below and execute only unfinished gates. Follow `superpowers:subagent-driven-development` or `superpowers:executing-plans` at execution time; this document does not submit a compiler task.

**Goal:** 接续已验收的 Gate 与 Unit，按原有源码完成下一共同消费者 OmittedPrimeWall，再接 NonemptyTailWallCount。

**Architecture:** 复用已成功的对象及审计；先补齐原供应的精确接收闭包，再在新的 P3 独占目录只编一个新目标。SelectedNativeWallPayment 保留为另一条较长的后续分支。

**Tech Stack:** 原 Lean 4.33.0-rc1 / commit `62eed1db4d67327ec8120be05f1a1b0847d74561`，mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`，原 P3 guard、runner、owned validator。

**Spec:** root 本轮任务；已有 `OMITTED_WALL_EXISTING_SUPPLIER_FRONTIER.json`（`6c3a31bdf136a8ebd3a77807acf7d12069eec7e9`）；atlas 新增两记录分析 `0520f4650089981185999b8572b72ec3668709f2`。精确输入清单见同目录 `P3_WALL_CONTINUATION_INPUTS.json`。

## 当前决定

下一新编译目标仍是 **OmittedPrimeWall**，但现在不能提交：Affine/Poly 的完整接收资格未齐，Nonunit 的唯一 target-only 续跑尚未完成。Gate 在 root 报告的 `bbd5dac6` 已接受；缓存 selector 中较旧的 pending 标记不再用于判断 Gate 状态。

| 顺序 | 既有源码，保持原文 | 直接项目依赖 | 当前边界 |
|---|---|---|---|
| 1 | OmittedPrimeWall `ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e` | AffinePrimeWallReserve、NonunitQuotient、FibreCore | FibreCore 已在 P3；另两支尚未接收完成。Gate 不是它的直接依赖。 |
| 2 | NonemptyTailWallCount `eaaa2b2d78c26668c3c4d54dca00876cd5bc1c8a` | GateAffine、NonradialSupport、OmittedPrimeWall | Gate 已有；Nonradial 是已有成功对象，只需其原证据和对象接收。 |
| 后续分支 | SelectedNativeWallPayment `a91a2ff88efabf868bb9922731368eeffdfa66cc` | SelectedAtlasStrips、GateAffine、OmittedPrimeWall、CoordinateCore | SelectedAtlas 分支还有多个源码层；Coordinate 已在别处验收，不得重编。 |

这里没有新增定理、定义展开或 proof 改写。Nonempty 使用的是已选定的显式 Nonradial import 后像，不能退回旧的隐式导入版本。

## Global Constraints

- P3 的 18 个旧供应 / 394 owned、Unit 26 owned 和 Gate 81 owned，均保留原成功证据；不重跑其 normal、kernel 或 owned。
- 已知 Affine 与 Poly 的 strict normal 都是 exit 0；不得为接收重新生成这两个对象。
- 两个目标审计文件在本次精确读取中没有取得，不等于整个项目不存在历史审计。优先恢复已具名的原证据；只补真正未完成的门。
- 不把相同 Lean/mathlib pin 当作实际对象一致；每个模块、facet、source owner 和实际解析路径须有精确绑定。
- 不将 515 native 的既有 external snapshot 算为 Affine/Poly 的 target-owned 信用，不重编或整批重放 515 模块。
- 不用此前 P36/P24 的同名 Geometry 变体替换当前源闭包；相同的坐标定义不足以证明整个输入闭包兼容。
- root 独占 Git tree/commit/ref 和最终验收。该计划不更新看板计数，不宣称 signed-PP 或完整 P2.9。

## Review Focus

- **同名对象不同字节：** 合并前按 module/facet 与 source owner 检查冲突；冲突时保留证据并停止，不能通过改搜索路径绕过。
- **原闭包只给 count/digest：** 52/53 个 project 项的成员与 P3 重叠目前未知；必须恢复原清单并重算 digest，不能猜测缺项数。
- **旧对象的成功阶段：** normal 已过不重跑，kernel/owned 已过也不重跑；原失败日志同时保留。
- **导入与目标偷跑：** P3 normal 的允许源码集合仅为一个新目标；实际图出现未经绑定的新研究输入则停止。
- **下游陈述边界：** Omitted 要求剩余维数正、每个壁线性部分非零；Nonempty 要求 tail rank 正。Unit 不能替代这两个假设或 Nonunit 的逆乘积估计。

## Task 1: 取得可接收的旧供应闭包

**Owner:** P2 原闭包仅由 atlas 负责；P1 Nonunit 仅由 delta 负责。profile 不再查询同一远端闭包。

**Consumes:** atlas 已取得的两个 schema-3 原记录、原 source imports，以及具名 external snapshot `ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27`。

**Produces:** 逐文件 source/object/原 normal/已有审计映射与安全归档；缺失审计必须明示，不能用生成的新记录代替。

- [ ] atlas 按实际 source imports 递归恢复原 52/53 project 项及记录，重算 Poly `d74c3438bc6173f6f5cbef2caff5ff2ab4306e45236acb1a2d738aacb8dd131c`、Affine `6c1afc8e6ebb6763c450877d9ddcf52ffd5ff06770364f11d923cf00ab994422` 的原 dependency-file digest。
- [ ] 取得/复用两目标已有 kernel/full-owned 证据；若确实未做，只将缺失阶段交给 root 决定执行位置，成功 normal 原件保持不动。
- [ ] 仅封装新接收方实际需要且尚未持有的对象/facet；已有五成员记录包没有这两个 `.olean`，不能当作对象转移已经完成。
- [ ] delta 完成 Nonunit 唯一续跑和证据交付。当前选择为 FQN proof 修复 `eeaf7a2c714da44928cc43e79780846e1e72d23b`；首 normal 失败及已过输入检查必须保留，不另建 P1 编译任务。

## Task 2: 仅接收并绑定 P3 合并输入

**Owner:** profile，等 Task 1 的精确材料到位后执行。

**Files:** 新建独占 `/workspace/p29-omitted-prime-wall-20261126-ef40c77/` 及其接收证据；原 Unit、Gate 目录只读。控制器尚未创建或提交。

**Consumes:** 原 P3 资格、FibreCore 对象 `7b54021ff39a596a2ab8085ee89c827c77f181e04acc7bb616d193b62b5e2cfa`，及 Task 1 的实际闭包。

**Produces:** 精确实际 import 图、源/对象/原工具绑定及通过或第一失败阶段的收据。

- [ ] 独占目录已存在则停止，先接续原任务；不得产生重复目标。
- [ ] 对接收到的成员验证安全路径、唯一性、大小和 SHA；旧 P3 对象只核对原绑定和当前字节稳定性。
- [ ] 对两边模块/facet 做一致性合并，显式记录未知或冲突。Nonunit 的 RadialRoughMass/native 闭包也必须纳入，不能只转移其目标 `.olean`。
- [ ] 用原 guard 正常 setup 绑定新配置并保留 action 校验；原 P3 policy 为 `Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2`。
- [ ] 使用原 actual-import probe 读取三个 direct roots 的联合环境。每个实际 facet 都须命中已接受的精确 authority；不能把一个可导入的新对象自动计为已合格。只做输入检查，不重放旧 18 / Unit / Gate。

原 52/53 项中有多少已在 P3、还需转移哪些 native facet，必须由 Task 1 的成员清单和本任务实际解析确定；当前没有可靠数量可填写。

## Task 3: 唯一新目标 OmittedPrimeWall

**Consumes:** Task 2 的合格输入，以及固定源码 `ef40c77...`（7,887 B；SHA256 `4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c`）。

**Produces:** `exists_wallTuples_payment`：固定 `d>0`、省略坐标、非零线性壁与正误差后，先选 `δ>0`，再对充分大的 `N` 控制原有序标记素数 carrier 的正规化计数。

- [ ] 复用已审 Gate P3 helper/工具，绑定唯一源码；独立审查新顶层输入合并与写入范围。
- [ ] 只运行该目标的原 strict direct-Lean normal：`lake env lean -DwarningAsError=true -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 -o TARGET.olean -i TARGET.ilean TARGET.lean`，通过原 runner/guard；不为其他源码生成输出。
- [ ] normal 成功后仅运行该新目标的 named kernel 和原 full-owned 审计；保留 `pp.maxSteps=1000000`，不改 parser。direct Lean 不生成 Lake trace/setup，报告必须如实注明。
- [ ] 复核目标以外实际输入未改变、源调用集合只有该目标；封存完整原始日志/声明类型/公理/输出后交 root 验收。若目标失败，先保存第一失败和固定稿对应段落，不预先改写源码。

## Task 4: 短支 Nonempty，长支 Selected 保持分开

- [ ] Omitted 接受后，复用已准备并已独立审查的 Nonradial 导出器 `5ad1322132859326ac4a1279b4cd2bc3c9317304`；当前未提交。原 Nonradial 对象 SHA 为 `0285b3ed20b8b8d3b5a540dab4f2c6e60a8120a0c6eead3f081036ae8dbe5883`，其直接 PhysicalExtension 对象与当前 P3 精确一致：`c80ed8b590734eb936bafd1a50889d1f431a8617bf21d059d7f4f30c4d68138c`。
- [ ] 原 Nonradial 证据与实际输入一致后，只编 Nonempty 的已选 `eaaa2b2...` 后像。它使用 Gate 的 `gate_strip_adapter` 和 Omitted 的计数结论；输出对固定 `k、r、ν` 且 `r>0`、全部允许的 `Q,width` 共用一个大 N 门槛。
- [ ] SelectedNativeWallPayment 不与该目标捆绑。其 selected 分支至少经过 `SelectedAtlasStrips → SelectedRootStrips → SelectedNativeStrips → SelectedWallCatalogue → SelectedBranchRows → SelectedFirstChange → SelectedQueryRows`，还接原 history/readout 供应；缓存中的源码闭包不等于 P3 runtime 资格。
- [ ] `ActualProperPayment` 的既有源码 `2735523e5245e96614b43d3b047b14158460bdf3` 虽使用 Nonempty 与 Unit，还需要 ActualHistoryScale 和 InnerComparison；不能将这两个已接受/待接受分量当成完整支付结论。

## 本轮自查与交付边界

已有计划先读后补增量；55 个缓存有效 source entries 中有 51 个带 imports 元数据，当前直接依赖可满足的仅 Unit、Coordinate、Chart、Gate，均为已验收组件，没有发现新的立即可投未编目标。这是有界缓存检查，不是全项目不存在其他对象的断言。

本轮 0 远程查询、0 compiler task、0 Lean、0 原证明重跑、0 新数学源码、0 Git ref 修改。P2 closure、P1 continuation、P3 reception 的责任人已互相确认；无需另起重复任务。
