# Winner9 原始 Full87 四模块的缓存恢复与资格边界

这条路线只恢复本次 5 个目标所需的既有固定源码和对象。缓存运输、输入资格、严格源编译、独立内核重放、owned-declaration 审计是分别记录的阶段；前两个阶段不增加定理验收数，也不完成 P2。

## 固定范围与原始证据

实际 source census 是 `docs/verification/20261124-p2-private/owner-native-source-census.json`，SHA-256 为 `ba08551ba6a326527d938439b96c06efa829e028bda88fc1497898645e282cc1`。它包含 247 个项目模块、506 个 goldbach 模块和 9 个 LeanArchitect 模块，无缺失源码。已独审的最终 request 是 `winner9_native_cache_request.json`，SHA-256 为 `9b33d3b252c02b3ab1e5ca75532efddd0f95136ef9daecf185b1aba40457a965`。

原始对象 artifact 为 `13749339878`，原 run 为 `42753193835`。整个原 ZIP 的 SHA-256 为 `c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b`；原 `CHECKPOINT.json` 的 SHA-256 为 `aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a`。重打包 run `45362510169` 只传输原字节，没有调用 Lean。

实际候选共 711 个：506 goldbach、9 LeanArchitect、196 project。514 个原生记录仍标为 `PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND`；196 个项目记录仍标为 `COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE`。`Architect.Command` 的 `PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED` 标签完整保留。51 个未导出条目均为 project，不能从旧包补造为当前已编译记录。

实际叶子字段见 `docs/verification/20261124-p2-private/architect-command-actual-checkpoint-fields.json`：`actual_import_count = 0`，无缺失 import artifact，`lake_completed_trace` 和 `output_bound_command` 均为 true，7 项 descriptor 均 matched。其实际 setup 是 `isModule = true`、`importArts = {}`、空 options/plugins/dynlibs。106ae2 适配器的 fresh 路径仍要求原 source/setup/trace 的完整性；这些前置条件在本次唯一隔离叶子上成立。它不是处理任意损坏或缺 trace 历史包的通用恢复器。

## 本轮已经观察到的结果与待验证阶段

106ae2 的首次真实 qualification（job `21e5f6cdbbac4ea195aa056cba2a2bd2`）先通过 13 个原生 provider 的原输入重绑，随后在 `freeze_core_imports("Lean")` 读取 `Init.Meta.Defs` 时，被整文件字符串/注释扫描器拒绝。错误是 `Unterminated comment/string in selected Lean source`。当时尚未启动 `Architect.Command` 的源编译，没有完整 native snapshot；13 个已复制 provider 的原字节保留。

5874aca 版本只修这个实际阻塞：增加局部 core header 读取，在首个非 header 命令前停止，保留 `module`、`prelude`、`public/meta import all` 和注释处理，再把所收集的头交给原导入解析函数。固定 census parser `9460e319…`、request `9b33d3b2…`、消费者和原资格门均未修改。固定 Lean 源 `Init/Meta/Defs.lean` 的原文 SHA-256 为 `01154a5f32560e2e971728ccb90a0cba6faa2f5c4764c9bab4bbcf7cb60b20b6`（65,877 bytes；Git blob `201680de486432949cac7a2da67f00faabd021da`）；旧扫描错误可在该原文复现，新 helper 返回正确的 6 个去重 imports 和 `prelude = true`。新增 2 项针对性回归独立通过，不能替代实际私有环境资格。

5874aca 的真实重试 job `77e605315ba246b4a2c30811d34fe812` 已完成：实际 2,322 个 core headers 预检通过；`Architect.Command` 严格源编译成功，其后的 Architect 原对象仍与原输入精确匹配。整批结果为 141 个原生 provider qualified、374 个 blocked，没有完整 native snapshot。4 个首发缺失来自 `Batteries.Tactic.Lemma` 与 `Batteries.Util.Pickle` 的 baseline 对象路径，其余是依赖级联；这不是扩大原生重编译预算的理由。已经成功的 `Architect.Command` 收据必须复用。

只读探针 `86794a54377c460aadc5d1936eef5d80` 的原结果保存在 `docs/verification/20261124-p2-private/batteries-complete-location-probe.json`。baseline 与 `/workspace/compile-deps/mathlib/.lake/packages/batteries` 都位于固定 pin `41bd267b3f6b7252f6676af46d4ffc6783b64de9`，tracked 源干净，原 CP 中的 192 个 Batteries 源 SHA 全部匹配。该探针扫描命名空间目录内的 955 个 loadable facets：baseline 匹配 390 个、缺 565 个；Mathlib 包缓存匹配 955 个、零缺失、零差异。这个目录扫描不包括可能实际需要的顶层 `Batteries.olean` 等文件，因此 955 不是恢复完整性计数。

后续适配器增加明确的 Batteries 字节恢复入口：从本次 711 个候选的实际原 setup 重新计算完整 Batteries import union，包括顶层 `Batteries`；逐源码、对象、原 import-map SHA 核对后，将所需 loadable facets 物化到既有 `stage/active/lib`。全部完成才发布 `standard-input-overlays/batteries.json`。来源仍为 baseline 固定源码，`LEAN_PATH`、sysroot 和 `Architect.Command` 的原 fresh 复用门保持不变；baseline 与 donor 都不写入。已有完整收据在再次 qualification 或项目采用器初始化时自动按同一原 union 严格重验；未完成的命名空间残留不能自动采用，必须显式恢复并完成检查。

这项恢复只运输原输入字节，不给 Batteries 或 515 个原生 provider 增加编译、重放或定理信用。其针对性 fixture 覆盖完整所需 union、顶层模块、缺失 facet、错误字节、额外目录遮挡、无收据残留和无编译的重复恢复；独立审查与真实私有环境重试结果分别记录。本文记录时完整 515-provider 资格仍待实际通过。

项目采用器的 d1be687a 版本修复了独审发现的实际事务漏洞：晚期 trace 复制失败时，原实现可能遗留无资格收据的成功 record。现在 trace 和其他可能失败的证据准备完成后才发布内存候选，整批后检前不写成功 registry；没有采用项时不改原 registry 字节。针对 late-copy `OSError` 的新增 1 项负例独立通过。实际项目采纳仍等待完整 native snapshot，没有发生任何 196 项目对象的自动升级或新的 proof credit。

## 私有环境命令

在 `/workspace/p2-private-20261124` 中运行。所有源编译和内核工作都在用户指定的私有编译环境中进行。

### 1. 原样接收并隔离存放

```bash
python3 verification/part2/qualify_winner9_native_cache.py stage \
  --packets .lake/p2-private/native-cache/repack-45362510169 \
  --request verification/part2/winner9_native_cache_request.json \
  --census docs/verification/20261124-p2-private/owner-native-source-census.json \
  --out .lake/p2-private/native-cache/staged-45362510169
```

`stage` 要求新的输出目录，不覆盖既有证据。它从固定原 CP 重新计算本次选择，校验每个分包和 content-addressed payload、原 source SHA/Git blob/imports，并按模块存入 `candidates`。旧 `.setup.json`、`.trace`、facet 和分类保留原字节。`STAGED.json` 的状态只能是 `BYTES_ONLY_NOT_QUALIFIED`。

已经实际执行的 stage 驱动原样保留为 `docs/verification/20261124-p2-private/native-stage-driver-v1.py`，SHA-256 为 `106ae2d4acd0ddc1f35f5c3bb26f2f47d9949a64b7bd9238ecf836a9bf5d2e91`。重复使用已完成的 stage 时直接进入下一阶段，不再执行 `stage`。

### 2. 恢复原生输入资格

```bash
python3 verification/part2/qualify_winner9_native_cache.py qualify \
  --stage .lake/p2-private/native-cache/staged-45362510169 \
  --project-root /workspace/p2-private-20261124 \
  --restore-batteries-from /workspace/compile-deps/mathlib/.lake/packages/batteries \
  --compile-missing --max-fresh-modules 1
```

先逐模块尝试原对象资格，只有确切原 cache 不能采用时才允许新编已选择的固定源码。默认最多一次源编译，覆盖本次隔离叶子的必要工作；后续旧模块必须再次根据实际新产出的对象 SHA 判断能否采用。不会直接把 515 个模块全部重新编译。若仍有缺口，输出具体 blocked 列表，状态为 `NATIVE_QUALIFICATION_INCOMPLETE`，不产生可消费的完整 native snapshot。

本次叶子已有成功收据，正常重试应出现 `REUSED_FRESH_NATIVE_RECEIPT Architect.Command`，不再次调用 Lean 编译该叶。Batteries 完整恢复后可以省略 `--restore-batteries-from`；初始化会根据已存在的收据重算原 setup union，并再次核对 donor、baseline 源和隔离对象。该自动路径也供没有新增参数的既有项目采用器使用。实际恢复模块数与 facet 数以 `batteries.json` 为准，不能照抄探针的目录计数。更新前的 5874aca 原驱动完整保留为 `docs/verification/20261124-p2-private/native-qualifier-before-batteries.py`。

适配器复用原 `checkpoint_original_protocol.py` 的 descriptor 校验函数，其 SHA-256 为 `cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff`。现有 `P2_NATIVE_398` / `STORED_PARENT` 的冻结 caller 规则没有被修改或绕开；本次新的 request 使用单独私有适配器，借用原纯校验函数，不伪称既有 caller 的验收结果。

每个候选必须满足原 source 身份、真实 guarded command、setup 选项、完整原 trace/facet、原 actual-import map SHA，以及映射后当前 imported source/object 字节。Lean runtime 与 pinned Lean shared-library ABI 必须匹配原记录。主机 C runtime 的不同逐项保留，不记为匹配；不安装 `.so`、`.a`、`.o` 或插件，也不装载原系统可执行 facet。该路线供现有 direct-Lean 私有 runner 使用，不声称 stock Lake 的 cache freshness 或 `--no-build` 已通过。

新编译使用真实 `-t0` 进程和显式实际 setup，保存全部实际输入的前后哈希、完整命令、日志和可加载输出。`Architect.Command` 新编译前额外冻结其实际 Lean 核心源码/对象依赖；原隔离对象不会因此被改标签。以后重新进入资格步骤时，已有 fresh receipt 必须按其原始实际 inputs 复核后复用，不重复源编译。

完整 515 个原生 provider 都通过时，输出实际 `EXTERNAL_SNAPSHOT.json` 路径与 SHA。它包含全部原生 source/object、实际 import root、runtime、provider receipts、直接 imports、传递依赖签名和总 context signature。后续命令必须使用该次实际输出的 snapshot 路径，不根据旧尝试编号猜测。

### 3. 复用当前已有项目记录

先将上一步实际输出路径设为任务专用变量，例如：

```bash
P2_NATIVE_SNAPSHOT=/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-001/EXTERNAL_SNAPSHOT.json
```

只有该实际 attempt 已成功生成完整 snapshot 时，才使用上例编号。

```bash
python3 verification/part2/run_winner9_private_checks.py \
  ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows \
  ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows \
  ImbalancedChen.P2OriginalDescendingEighthLogSemantics \
  ImbalancedChen.P2OriginalThirdMinorantLogDictionary \
  ImbalancedChen.P2Winner9OriginalFull87Bridge \
  --external-snapshot "$P2_NATIVE_SNAPSHOT" --time-budget-seconds 0
```

这一步只采用已经有效的当前记录或原可靠 baseline 缓存，并列出 pending。时间预算耗尽但无证明失败时，runner 返回 2 表示部分完成；这不应被改写为完整通过。

### 4. 显式采用原 CP 中的项目对象

```bash
python3 verification/part2/adopt_winner9_project_cache.py \
  --stage .lake/p2-private/native-cache/staged-45362510169 \
  --external-snapshot "$P2_NATIVE_SNAPSHOT" \
  --project-root /workspace/p2-private-20261124
```

只有该模块自己的原 guarded project row、当前 source、实际 imported source/object、当前依赖 records 和 runtime 全部匹配，才生成一个新的历史 cache 采用记录。已经有效的记录不改，现有不同对象不覆盖，依赖记录缺失或未绑定 native 时不采纳。候选记录只暂存在内存，整批 native 前后、实际项目 source/object、原 records 文件均复核后，才原子发布。

这些记录的 `new_strict_compile` 为 false，原分类保留，原 CP 和此次资格 receipt 都在记录中。原生祖先使用 schema 3，并显式绑定完整 snapshot；其余有限模块继续使用 schema 2。旧无 native 绑定的记录不会被自动升级。

### 5. 仅编译剩余模块，随后重放和审计

```bash
python3 verification/part2/run_winner9_private_checks.py \
  ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows \
  ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows \
  ImbalancedChen.P2OriginalDescendingEighthLogSemantics \
  ImbalancedChen.P2OriginalThirdMinorantLogDictionary \
  ImbalancedChen.P2Winner9OriginalFull87Bridge \
  --external-snapshot "$P2_NATIVE_SNAPSHOT" --workers 1 --threads 1 --memory-mb 6144
```

新批次中的 native 祖先记录在整批后检完成前，磁盘中保持 pending/exit 125，不能被别的过程误认为已通过。native snapshot 前后不符会撤销受影响的新成功状态。普通有限缓存签名不变。

只对尚未完成该上下文验收的原四个 owner 调用 v3 audit：

```bash
python3 verification/part2/run_winner9_private_audit.py \
  ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows \
  ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows \
  ImbalancedChen.P2OriginalDescendingEighthLogSemantics \
  ImbalancedChen.P2OriginalThirdMinorantLogDictionary \
  --external-snapshot "$P2_NATIVE_SNAPSHOT" --summary-name original-owner-v3.json
```

已接受的桥与有限证书 v1/v2 收据不因工具版本更新而重跑。真实 owner+bridge 组合导入仍须按同一 native snapshot 进行实际兼容性检查；source-only 同名定义不能与旧 owner 的原定义同时导入。

## 审查记录与现状

- `native_cache_repack_review.json`：重打包与真实 762 request 的独立审查。
- `native_snapshot_consumer_review.json`：schema 2/3 消费者及 default finite 兼容的独立审查。
- `native_cache_qualifier_review.json`：106ae2 私有资格适配器的固定范围审查与 5874aca core-header 最小修复审查。原 5 项接收器测试与新增 2 项 header 测试分别记录，均不提供 Lean 信用。
- `native_project_cache_adoption_review.json`：项目采用器的 4 项原 fixture、实际晚期异常复现，以及 d1be687a 修复后的新增 1 项负例；只核对历史记录的显式来源、不同对象不覆盖和失败时不发布成功状态。

保留的旧 compile budget v2 为 `compile-driver-budget-v2.py`（`df994927…`）；旧 audit v2 为 `audit-driver-v2.py`（`b214fe82…`）。新的 driver 同时需要 `winner9_external_snapshot.py` 与固定 `inspect_winner9_owner_native.py`，不能只更新一个 runner 文件。

真正的 native 资格结果、源编译、独立重放与 owned-declaration 结果以私有环境生成的具体 receipt 为准。本文中的命令和本地 fixture 不替代这些结果。
