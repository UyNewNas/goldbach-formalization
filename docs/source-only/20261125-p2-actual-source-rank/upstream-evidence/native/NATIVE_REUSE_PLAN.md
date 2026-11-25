# H430 native 边界复用审计与最小资格扩展计划

## 结论

本次 49 个 direct native 入口全部有既存、可定位的源文件；没有发现需要新造数学定义或重证明的“缺失来源”。

| 入口类别 | 数量 | 已有来源 | 当前可主张的状态 |
|---|---:|---|---|
| 原 515 native census 内 | 21 | 09b97 固定包 active 目录 | 已有 attempt-003 的 qualified environment 记录；后续消费仍按原 ExternalSnapshot 实物重验 |
| 固定 active 目录中、原 515 外 | 5 | 同一 09b97 的正常模块路径 | 云端原 source 全部存在且 SHA 精确一致；尚未纳入该 snapshot |
| Wu 研究供应 | 23 | 同一 09b97 的 research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ | 原 source 全部找到；不能伪记为包 active 路径；当前检查的 active 路径没有这些源码 |

固定 native 来源：`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`。
MathlibNt active 子树 `878b9ff8a818b478313bc8d4a3d4483bd4210bce`（2471 项，未截断），research 子树 `558e790fd1728a2b6252e36c9a41d34c9a66c072`（5187 项，未截断）。

新增 28 个入口的原文已按 immutable commit/path 下载到本审计目录的 `pinned-source/`，逐字节长度和 Git blob 验证通过，合计 184299 bytes。没有安装到任何原项目或 native checkout。

## 原 snapshot 与真实当前库存

原来源 census：

- `/workspace/scratch/33c167465f9e/goldbach-p2/docs/verification/20261124-p2-private/owner-native-source-census.json`
- SHA256：`ba08551ba6a326527d938439b96c06efa829e028bda88fc1497898645e282cc1`
- 506 goldbach + 9 LeanArchitect = 515 native；本次 49 根中的交集是 21。

已有资格记录：

- `NATIVE_OWNER_CONTEXT.json` 记录 job `ee728a8b25a749409d7a1fca96466306`。
- snapshot：`/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json`
- SHA256：`ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27`
- 514 原 checkpoint provider 重绑；Architect.Command 复用已有 fresh receipt；该轮新 native 编译为 0。
- 这是输入环境资格，不能增加 P2 theorem/kernel 完成数。

root 的真实云端 job `f57a1a3c943649aa84b79eb6ab7e5209` 已核对 26 个 active 入口原 source SHA 完全一致；其余 23 个 Wu 入口在本次检查的 active/cache 源位置没有文件。这个检查没有检测 research 目录、研究 build/lib 或其它编译环境 donor。

## 5 个 active 差集

1. `MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional`
2. `MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanActualErrorEnvelope`
3. `MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation`
4. `MathlibNt.SieveTheory.LiLiuPanBoundedAggregate`
5. `MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds`

它们的完整 commit/path/blob/SHA/imports 见 `EXACT_SOURCE_RECORDS.json`。这 5 个入口不能只凭“同一个 pin”补入既有 snapshot；应先对照原完整 checkpoint 的 guarded package rows 和实际 donor bytes。

其中 TailPropagation 已有更强的既存缓存线索：

- 已保留 `docs/verification/20261123-blue-compilation/member-cache-window/compact/P6_NATIVE_INSTALL_COMPACT.json`。
- 原 source SHA `16fbf5f74a67a969fea728e69b7ddef3659acc566cd4ec15de60797120936146`，与本次 immutable source 完全相同。
- 原 P6 → Member 复用保存 8 个文件，16622 次实际 import facet 重核；stock 检查为 up-to-date、该源新增编译为 0。
- 原 donor：`/workspace/blue-p6-build/.lake/packages/goldbach`；原接收方 `/workspace/blue-member-build/.lake/packages/goldbach`。这些是历史收据中的路径，不声称在当前 8e1da5a7 环境存在。

## 23 个 Wu 根的后续真实生产验核来源

早期 09b97 的 `research/wu2008/source-manifest.json` 记录 source/object/import 指纹，但其 `source_binding` 明确是 `matching_object_imports_rebuild_required`；仅凭这份搬迁清单不能资格化对象。

进一步只读查到后续 immutable commit：

`subfish-zhou/goldbach-lean@9d4c3a4010d42aedd9e7231bf94386019cfffccc`

其中：

- `research/wu-structural-compression-audit/production-verification.json`
- Git blob `d9f562ea3aeb996aee2cda92e8b3b8f64959d03a`
- SHA256 `d13f60c24222fb0882fadd6ca289ca45eff8e62b2635ff53bd259fd02125494a`
- 状态 `PRODUCTION_4151_RECEIPTS_LITERAL_AXIOMS_FINAL_KERNEL_PASS`
- 4151 个 production receipt 被复核；3500 promoted source proof receipts、651 unchanged receipts，最终 production verification 新编译为 0。

本次 **全部 23 个 Wu 根** 的 09b97 source SHA 与这份后续 production 绑定的 source SHA 逐项相同；另外 Bombieri1965Richert418Unconditional 和 BuchstabBounds 也相同。共 25 根均有原 source、原 .olean、原 receipt SHA 的三联绑定，完整表在 `V9_PRODUCTION_COMPARISON.json`。

这提供了可靠的“已有完成工作应该先复用”的出处，但 Git 树没有发布其 binary/receipt payload：

- 后续 research tree `dbc85018c75a0269bb7cca834210da55a95e10bc`，7138 entries，未截断。
- `wu2008/build/` entries = 0；.olean 文件 = 0；build/receipts payload = 0。
- 原 production path：`/home/azureuser/goldbach-lean/research/wu2008/build/lib/<Module>.olean` 与 `build/receipts/<Module>.json`。

因此，最省工作的方法是从仍保存这个 production 目录的既有环境取得**原 receipt payload 和完整 portable facets**，再核对当前 imports/runtime；只下载这 25 个哈希指纹不能形成可消费 cache。

另外两个更广的历史 donor：

- Member：`/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json`，曾有 1548 native 选源。
- P6：`/workspace/blue-p6-selection.json`，810 native 选源，SHA `5655b541f17120d3d535308478fe70f5d2b49739462a399675d4d88aeb277a62`。
- Member → P6 的 223 native / 1561 portable facets 收据：`/workspace/artifacts/member-to-p6-fresh-native-20261123/SUMMARY.json`，SHA `540f51c6e77be34ca3b1a5aa3dffb3bace8bb1fa56c3f20cda793c701bc23bb4`。
- 历史 receipt 路径必须与当前实际环境分开；不能从“曾有 810/1548 个”推断本次所有模块都有对象。

## 不能直接扩大旧资格工具的原因

现成工具的代码确有明确、固定的 caller scope：

- `inspect_winner9_owner_native.py` 固定 5 个原 owner/Full87 roots，且只按 package active 的模块相对路径查 source。
- `repack_winner9_native_cache.py:validate_request` 固定这 5 根、247 project sources、21 direct native roots 和原 parser SHA。
- `qualify_winner9_native_cache.py` 读取那个原 REQUEST/CP，新增 source compilation 也要求该模块已在原 selected 记录中。
- `winner9_external_snapshot.py` 仅消费已经资格化的环境；不会把新 entrypoint 自动升级成 provider。

因此，没有一条现成的 `qualify_winner9_native_cache.py` flag 能完成这次 49 根的扩展。不要改旧 REQUEST、猴补 ROOTS/validate_request 或单纯提高 `--max-fresh-modules`。应把新增范围作为独立、显式的 extension receipt，复用原 source/import/runtime 校验实现与旧 515 个 receipt。

## 已准备的最小只读调用

已准备独立工具 `inspect_h430_native_reuse.py`，SHA256：

`d3ff54fb3ca3b8b37873ff420d435a27d393e1b823c9e9c05bcc6691239ca9a2`

它只写指定的新报告，复用原 SHA 固定的 imports parser；验证 native checkout 的固定 HEAD、tracked 清洁、每个 active/research source 的真实 Git blob，然后读实际 imports 递归；同时对照旧 census/snapshot、原 CP 的同 source guarded rows、可选 object-root 的文件存在性。**不调用 Lean/Lake/对象加载器，不安装 source/cache，不授予资格。**

只需先把它和 `DIRECT_NATIVE_ROOT_INPUT.json` 转存到私有隔离目录 `/workspace/p2-h430-native-audit/`。小输入为 4768 bytes，SHA `eb3a9c5de567b9a0e5c418af2129a11abd4c234ca6ba8fa07f658a478f4fc8db`，绑定原 MINIMAL_SOURCE_MANIFEST 的 SHA `69dec94abd07c11aa1185470fde90be7696bac606dceca541aa18f80686a9b01`。

```bash
python3 -B /workspace/p2-h430-native-audit/inspect_h430_native_reuse.py \
  --roots-manifest /workspace/p2-h430-native-audit/DIRECT_NATIVE_ROOT_INPUT.json \
  --helper-dir /workspace/p2-private-20261124/verification/part2 \
  --goldbach-root /workspace/goldbach-p2/.lake/packages/goldbach \
  --architect-root /workspace/goldbach-p2/.lake/packages/LeanArchitect \
  --old-census /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/SOURCE_CENSUS.json \
  --old-snapshot /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json \
  --checkpoint /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/CHECKPOINT.json \
  --object-root /workspace/goldbach-p2/.lake/packages/goldbach/.lake/build/lib/lean \
  --object-root /workspace/goldbach-p2/.lake/packages/goldbach/research/wu2008/build/lib \
  --out /workspace/p2-h430-native-audit/source-cache-census-001.json
```

如果其它历史 donor 在同一环境实际存在，可以额外加 `--object-root`；不存在的 object-root 只返回无对象，不制造缓存失败。

路径校正：当前私有工作树没有本地发布归档的 docs/verification census 路径；原 qualifier.stage 保存、Qualification.__init__ 使用的是上述 stage/SOURCE_CENSUS.json，其预期 SHA 仍是 ba08551ba6a326527d938439b96c06efa829e028bda88fc1497898645e282cc1。root 后续实际查询已确认当前 P2 环境不含 Blue Member/P6 donor 目录、selection 或转存 receipt；其它既有环境的 production provider 仍需按原路径/哈希寻找。

输出会给出真实完整 topo、超出旧 515 的精确 source 差集、原 CP 匹配行及原分类、候选对象位置、active/research 变体冲突和缺失来源。本地只做了工具 CLI 加载与静态审查；完整 checkout 的实际扫描由 root 调度。

## 随后的最小扩展资格步骤

1. 先取得上述实际 census。只针对它列出的新增 native closure 查原 CP / donor；旧 515 个源和对象不重编译。
2. 从原 CP 的新增 source 匹配行传输完整原 source/setup/trace/loadable facets，保留 classification、原实际 imports 和原 runtime 记录。当前原分包只有旧 request 的 711 个候选，不假设已包含新增对象。
3. 对 Wu production donor，取得本次源 SHA 匹配的每个实际 receipt payload、完整 portable facets 和它所绑定的实际 import closure。后续 compressed 版本的其它 provider 不整树覆盖；本次直接入口中已有 3 个 active 与早期 research source 不同：B8FibreSieve、SuzukiMovingSigmaElementaryHead、SuzukiUpperRosserBoundarySourceSuccLayer。
4. 独立 extension producer 保留原校验强度：source exactness、真正 producer command/setup/trace、所有 actual imported source/object 字节、Lean/runtime ABI、依赖递归资格。任何缺失 payload 或不同输入都明确 blocked。原 production 的“已通过”不能替代当前重绑。
5. 合并为新 snapshot 时须重新计算真实 search roots、dependency signatures、closure/context signatures，并通过现有 ExternalSnapshot 的物理文件和实际 resolution 检查。尤其 MathlibNt 目录有 package-root 遮挡规则，不能简单把几个新 .olean 放在更早的不完整目录，再依赖后面的旧 cache 补齐。
6. 若某模块确实没有可复用对象，才考虑对**已找到的精确原源码**作最小缺口编译；不改原定理、定义或假设。不要把它误算为 23 或 28 个文件的预算：按旧 research manifest 的历史 import 图、遇旧 515 即停的粗估仍有 972 个新增 native 节点，且有 3 个尚未在该旧 manifest 的 active 入口。这只是历史图的预估，不能替代实际 census，也不应据此启动整库重编。

本任务没有执行云端命令、没有 Lean 编译/内核调用、没有修改原项目、extraction 文件或 rank candidate；上述文件均为隔离来源审计、原源码副本及只读工具。

