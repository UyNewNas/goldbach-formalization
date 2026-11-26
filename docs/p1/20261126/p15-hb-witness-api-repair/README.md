# HBWitnesses 词法修复与 Cutoff 伴随修复

本目录为发布 **C** 准备两份固定源码的安装入口。它沿用 A 的失败配置保留流程、原 lane 0 serializer、guard 和 `h.install_sources`，不运行 Lean、Lake、normal 或 kernel，不产生新的验收信用。

原 B 为 `3d292e4cd193ab422ca990e80a25165d5aca33a1`。实际 `job_216f3dbd13b24dab8524da9ada0cac1b` 已完整接受 SupportData，随后 HBWitnesses normal 失败；Cutoff 尚未开始。B 失败组的结果保持失败，Support 的单 owner 验收保持原 B 身份。

## 精确源码修复

| 源码 | 原字节数 / SHA256 | 修复后字节数 / SHA256 |
| --- | --- | --- |
| P5OriginalPrimeChartHBWitnesses | 8656 / `93858742e3c6fd13e69bea47e0c92af273d913784a96f10ac03883a6a8823075` | 8716 / `15c3a939529b5af6133467b8922e7fa8179218b127c31bd22bd9e535de3df569` |
| P1OriginalSingletonCutoffData | 12390 / `3e78ff44ad0e6fdea017402b6ff2b431a81c9c9c01a12611c8b405aad22e9cc4` | 12510 / `c61b80c930959e86f310299c8c4b1d0b86d358320f08a89be404dbadc33c8b1d` |

修复仅在三个已有 namespace 各加入一条 `local notation "R" => ExactOriginalSmoothDyadicPartition.R`。这与直接已接受 supplier `P5ActualLabelledPrimeSmoothCharts` 的写法相同。删除这三处新增 notation 及相邻新增空行后，两份完整文件逐字节恢复 B 原像；原 theorem statements、证明正文及 imports 均保留。

HB 的完整 cons 错误目标表明，`hR` 受前面的 `R` 名称歧义影响而包含编译器错误恢复占位；因此保留原 list simp。Cutoff 的两个 namespace 存在相同裸 `R` 冲突，本次只做这两个明确授权的伴随词法修复。其余 15 个候选不在本次修改范围内。

[REPAIR_MANIFEST.json](REPAIR_MANIFEST.json) 固定三段非空原字节区间、全部 pre/post SHA 与 Git blobs、11 份实际失败证据，以及唯一已检查的 setup 指纹。入口用这些 splice 重建完整 postimages。

## 保全 Support 的原 B 验收

SupportData 不是 fresh target。入口以固定 B 失败 `RESULT.json` 内的 `acceptance_bindings[Support]` 为依据，调用原 B `existing_owner` 和 `require_completed_existing_owner`，实际只读执行原 `normal_valid` 与完整 `audit_valid`。

C 同时绑定公开的 [SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json](../../20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json)：1894 B，SHA256 `25a6333e4b89b03ca541d72a26b5d7f9273849bb7cc8aed6cc351db99bbc3c1a`。其中六项 normal/audit/owned 证据指纹及 5 owned、5 public 覆盖均需匹配。它记录的 source commit 仍为 B，既有组失败状态也保留。

Support 的全部已观察 cache artifacts 加入保全依赖；其固定 owner 证据目录和 B `runs/attempt-00000/Support` 调度证据目录内所有常规文件均逐文件指纹绑定并前后核对文件集合。六个公开 pin 已核过的值不能被后续目录观察覆盖。两源安装后，再以原 B 身份复核 Support 完整验收；不重新 normal/kernel，不改 receipt 字段。

固定范围为 **360 发布源 / 130 live 源 / 148 监控模块**。只有 HB 与 Cutoff 可改，因此其他 **358 发布源 / 128 live 源** 保持原字节。保全依赖为 **128 = 9 个原 supplier + 118 个 fixed dependency + Support@B**。HB 的失败 normal 闭包为 67；Support 的原闭包为 109，不含 HB 或 Cutoff。

## 唯一失败 setup

实际只读 metadata 检查任务为 `job_eeeb8862992b45ca99209d70704ca0ad`。HB 的 21 项 artifact 中只有以下路径存在，另 20 项 absent，normal pass receipt 也 absent：

`/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalPrimeChartHBWitnesses.setup.json`

该文件固定为 **6328085 B**，SHA256 **`99cad186ff4aa90dee75dfed9f9c858d4ee2f518f49d1903ef353d5ef181dd3a`**。

原失败证据和 Support 完整验收匹配后，入口先独占创建 0600 私有原字节副本，flush/fsync 并核对指纹，fsync 目录和元数据，再检查原 dev/inode/size/mtime 及全部字节，最后只移除这一活跃路径。完整原文件和证据保留在 C 的本次 attempt；正文不进入 stdout。

随后重新读取真实完整 artifact 集合，只对 **HB 与 Cutoff** 调用原 fresh gate。Cutoff 没有任何 artifact 例外。任一未知 artifact 或指纹不同都 HOLD。若 HB setup 已 absent，必须有同一 C 下匹配固定 B/job/manifest 的完整先前 archive。失败时保留 archive 和源码备份，不自动清理或重试。

## C 安装与 D 验收

C 必须包含本目录、两份修复源码及上述 Support 公开摘要。原 B `run_selected.py`、`SOURCE_MANIFEST.json`、`install_sources.py`、`verify_static.py` 在 C 全字节不变。入口不保存 C 的自引用 SHA；由 `--source-commit` 绑定包含这些精确文件的完整 C commit。

从 C 取得精确脚本后使用：

```bash
python3 -B <C-script-path> --source-commit <full-C-SHA> --check
python3 -B <C-script-path> --source-commit <full-C-SHA> --apply
```

`--check` 只读，不创建 attempt、archive、receipt，不安装源码。`--apply` 经原 lane 0 serializer，使用原 `h.install_sources` 的一次两项批量调用：先完整验证两个原像和 postimage，再独占备份、替换；已是 postimage 的项可在 HB/Cutoff 仍 fresh 时 noop。C 不编译任何目标。

后继发布 **D** 由原入口负责人单独处理来源重锚和固定 Support@B 复用，再验收 HB 与 Cutoff。C 不把 Support 重新定义为 C 的新验收，也不改变 B 原 fresh/guard/runtime/cache 政策。

完整执行证据仅保存在 `/workspace/p1-complete-proof/20261126-p15-hb-witness-api-repair-v1/<C>/runs/attempt-xxxxx/`。原 dirty Git 保护的准确边界是 HEAD/status 前后相等；入口没有写入原 `REPO` 的代码路径。

## 静态审查边界

[STATIC_REVIEW.json](STATIC_REVIEW.json) 记录源码 splice、AST、原 helper/归档流程及独立只读审查。未执行 updater、原 driver、Lean、Lake 或云任务，未创建 Git 提交。词法修复后的两份 Lean 源仍待真实验收；本目录不增加形式化信用。
