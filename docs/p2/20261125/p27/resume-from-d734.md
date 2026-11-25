# 从 d734 的实际成功对象继续 P2.7

本文是恢复步骤，不是执行回执。P2 连接已恢复，d734 原编译登记的 capture 已实际成功，登记与 capture 清单的独立双锚保存在 [original-capture-observed.json](original-capture-observed.json)。后续任务 `33664c31d5c8417b92b296f4784657ed` 已 checkout 固定候选 `549ea2164c17a8a3f66edbbd88262ea9d5ef05f0` 并核对 81 份源码，但 native attempt-002 因稀疏检出缺少 `docs/source-only` 而失败，见[原始日志](resume-20261126-binding002.log)。本修订补齐遗漏的旧协议文件恢复步骤，并使用新的 attempt-003；不据此声称后续资格、重绑或 P2.7 最终验收已经通过。

需要保留的工作目录是 `/workspace/p2-7-20261125`。原成功任务 `d734023ac6d243279c3f73e3308f111f` 运行于 `9c5a20ab9e13bc9393db8c9f5b0b0e4212006970`，已完成 73 个数值/Fubini 模块、19 项审计及 551 个所属声明，完整分析闭包达到 77/81。不得删除这些对象、登记、日志、审计文件及已完成的 capture。

所有阶段均使用 **Bash**，在 `/workspace/p2-7-20261125` 工作目录下串行执行，并启用 `set -euo pipefail`；任何失败都立即停止，不进入下一阶段。capture、CurrentChen 接收和记录重绑前，必须确认同一工作目录没有编译、接收或 registry 写入进程。原字节 CAS 是一致性检查，不是跨进程锁，不能在其他写入者运行时执行。

## 1. 先捕获原登记，再更新源码

**首次恢复必须先保持原 HEAD 完成 capture 并独立留存输出，再执行 P2 的 `git fetch` 或 `git checkout`。本轮 capture 和固定 checkout 已完成，以下 capture 命令仅保留原流程；不要重跑 capture，也不要退回旧 HEAD 重做。当前从本节末尾的协议文件恢复步骤继续。**

将已审查、已提交的 `verification/part2/p27_rebind_unchanged_native_records.py` 原字节传到工作目录之外的临时路径，并核对该固定提交中该文件的 SHA。此传输不能覆盖 P2 工作树中的原工具，也不能修改 `.olean`、登记或日志。随后以旧工作树的冻结协议模块为 `PYTHONPATH` 执行：

```bash
set -euo pipefail
cd /workspace/p2-7-20261125
PYTHONPATH=/workspace/p2-7-20261125/verification/part2 \
python3 -B /tmp/p27-reviewed/p27_rebind_unchanged_native_records.py capture \
  --project-root /workspace/p2-7-20261125 \
  --original-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json \
  --out /workspace/p2-7-20261125/.lake/p27-native-record-rebind/input-d734
```

实际 capture 必须核对旧 snapshot、原成功记录、源文件和对象、工具链及依赖，保存原登记、旧 snapshot、原严格编译日志及清单。日志哈希只表示 capture 时实际读到的文件；原 compiler record 没有日志 SHA 时，不补写一个虚构的原编译时日志哈希。

从该任务的真实工具输出独立留存两个 SHA：原 `records.json` 的 SHA 和 `CAPTURE.json` 的 SHA。后续命令里的 `CAPTURED_RECORDS_SHA256`、`CAPTURED_MANIFEST_SHA256` 必须替换为这两个实际值。不能仅从准备被接收的文件自身读取一个 SHA，再把它充当独立来源证明。

此时才可以 fetch 一个已核对的固定候选提交，并 checkout 该提交。记录实际 HEAD，核对 `source-manifest.json` 的全部 81 个源码 SHA。不要使用运行途中自动刷新分支的旧 `queued-resume-command.sh`。

### 恢复稀疏检出遗漏的旧协议文件

本轮固定候选为 `549ea2164c17a8a3f66edbbd88262ea9d5ef05f0`。在 capture 完成且该固定提交 checkout、源码清单核对成功之后，必须先恢复以下既有文件，再调用 native 资格核验器：

| Git 路径 | 字节数 | SHA-256 |
| --- | --- | --- |
| `docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py` | 1,766 | `cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff` |

原 [queued-resume-command.sh](queued-resume-command.sh) 已有该 Git 原字节恢复步骤，此前恢复文档遗漏了它。下述步骤只物化该固定旧协议；文件已存在时仅核对原字节，不覆盖。不改 qualifier、重绑 helper 或数学源码，也不重跑已成功的 capture。

```bash
set -euo pipefail
cd /workspace/p2-7-20261125
python3 -B - <<'PY'
from pathlib import Path
import hashlib
import json
import subprocess

project = Path.cwd()
revision = "549ea2164c17a8a3f66edbbd88262ea9d5ef05f0"
relative = "docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py"
expected_sha = "cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff"
head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if head != revision:
    raise SystemExit("Unexpected checkout; preserve the recorded fixed candidate")
raw = subprocess.check_output(["git", "show", revision + ":" + relative])
if len(raw) != 1766 or hashlib.sha256(raw).hexdigest() != expected_sha:
    raise SystemExit("Original protocol Git bytes differ")
destination = project / relative
if destination.is_symlink() or destination.resolve() != destination:
    raise SystemExit("Original protocol path is redirected")
existed = destination.exists()
if existed:
    if not destination.is_file() or destination.read_bytes() != raw:
        raise SystemExit("Existing original protocol differs; nothing overwritten")
else:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("xb") as stream:
        stream.write(raw)
if destination.read_bytes() != raw:
    raise SystemExit("Original protocol readback differs")
print("P27_ORIGINAL_PROTOCOL_VERIFIED " + json.dumps({
    "git_commit": revision, "path": relative, "bytes": len(raw),
    "sha256": expected_sha, "existing_file_checked_only": existed,
    "compile_credit": False, "kernel_credit": False,
}, sort_keys=True))
PY
```

## 2. 正常生成新调用方绑定并接收 CurrentChen 原对象

旧 attempt-001 包含全部 81 份旧项目源码的物理身份。VariableLower 的源码修正使旧 snapshot 不再是当前有效快照；不得把旧 snapshot 验证成功当成新源码的证据。

失败的 P2.7 native attempt-002 及其日志、失败回执保留原样，不删除、不覆盖、不复用为新输出。完成上述协议恢复后，使用原资格核验器和原 Winner9 基础 snapshot 生成新的 attempt-003，不把已经失效的 P2.7 attempt-001 当作基础输入：

```bash
set -euo pipefail
python3 -B verification/part2/p27_qualify_native_inputs.py \
  --project-root /workspace/p2-7-20261125 \
  --base-snapshot /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json \
  --bundle /workspace/p2-7-20261125/.lake/p27-inputs/native \
  --out /workspace/p2-7-20261125/.lake/p27-native/attempt-003

python3 -B verification/part2/adopt_p27_currentchen_cache.py \
  --project-root /workspace/p2-7-20261125 \
  --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json \
  --native-bundle /workspace/p2-7-20261125/.lake/p27-inputs/native \
  --project-bundle /workspace/p2-7-20261125/.lake/p27-inputs/currentchen \
  --out /workspace/p2-7-20261125/.lake/p27-currentchen-adoption/attempt-003
```

这些目录必须是首次运行的新输出。若某阶段已经成功，按真实回执从下一阶段继续，不删除结果后重新运行。这里的 attempt-003 只统一新的 native 资格、CurrentChen adoption 和 record migration 三组目录；首次完整 export 路径及 delivery attempt-001 保持原约定，其编号独立，不能跟随 native 尝试号改写。

## 3. 核验三个原严格编译来源，仅重绑两条记录

`PairedV2` 没有 native 祖先，其 schema-2 原记录可直接保留。只有 `CurrentPairedBuchstabBridge` 和 `PairedV2FullBuchstab` 的 schema-3 记录需要新的调用方绑定。新工具核对三个原成功来源，以及共 13 个项目模块的保护闭包（包含这三个目标），只允许写入这两条记录，不能把 PairedV2 强改为 schema 3。

```bash
set -euo pipefail
python3 -B verification/part2/p27_rebind_unchanged_native_records.py rebind \
  --project-root /workspace/p2-7-20261125 \
  --original-records /workspace/p2-7-20261125/.lake/p27-native-record-rebind/input-d734/records.json \
  --original-records-sha256 CAPTURED_RECORDS_SHA256 \
  --capture-manifest-sha256 CAPTURED_MANIFEST_SHA256 \
  --original-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json \
  --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json \
  --out /workspace/p2-7-20261125/.lake/p2-private/native-record-migration/attempt-003
```

真实原记录必须符合工具支持的严格编译格式，所有非项目输入也必须有可核对的旧来源。原登记虽已捕获，old snapshot 是否覆盖全部所需 import facets 仍须由实际重绑逐项核验；缺失时必须报告具体输入并停止，不得直接重算闭包签名绕过门禁。三个原成功模块都不得因此重复编译。

重绑不调用 Lean，不修改 `.olean`，不增加新的严格编译或内核证明信用。原数值记录、19 项审计和 PairedV2 的原记录均保留。输出置于 `.lake/p2-private/native-record-migration` 内，使原 exporter 的既有 supplemental JSON 与 migration 日志规则收入原登记、原 snapshot、原日志及重绑回执；验收时仍应核对实际导出清单。

## 4. 继续未通过模块和最终审计

仅在前述真实核验成功后运行原检查器。它应复用已经有效的对象，而只编译尚未通过的 VariableLower 及其三个下游模块：

```bash
set -euo pipefail
python3 -B verification/part2/run_winner9_private_checks.py \
  ImbalancedChen.P2PairedCertificateCompletion \
  --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json \
  --workers 1 --threads 1 --memory-mb 12288 --time-budget-seconds 900

mapfile -t p27_all_targets < docs/p2/20261125/p27/audit-targets.txt
LEAN_NUM_THREADS=1 python3 -B verification/part2/run_winner9_private_audit.py \
  --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json \
  --memory-mb 11264 --summary-name p27-complete-summary.json \
  "${p27_all_targets[@]}"
```

必须观察实际 `REUSE`、`REUSE_AUDIT` 和汇总结果。目标是 81/81 项目闭包与 26/26 目标审计，19 份有效审计沿用原件；在实际输出出现之前不得把期望计数写成已通过。如果还有 Lean 错误，先回到 1106 稿件对应段落判别错误性质，再作最小改动。

## 5. 第一次完整导出与接收

最终审计通过后恢复两份固定原始 driver 字节，SHA 必须分别等于：

| Git 路径 | SHA-256 |
| --- | --- |
| `docs/verification/20261124-p2-private/driver-v1.py` | `05f31ad7f78c69bf58a1f0daab4b597db9a90190f255a880abdab22767c864b5` |
| `docs/verification/20261124-p2-private/audit-driver-v2.py` | `b214fe826d40f96c9907cb9c42f0ac96dcc9bc48dc080a264c9c13de2b43cc08` |

使用 `git show HEAD:<Git 路径>` 原字节保存到 `.lake/p27-repro-drivers/`，存在时只核对，不覆盖。然后仅生成一次原始完整导出：

```bash
set -euo pipefail
mapfile -t p27_all_targets < docs/p2/20261125/p27/audit-targets.txt
python3 -B verification/part2/export_winner9_private_evidence.py \
  --output-dir .lake/p2-private/exports/p27-complete-20261125 \
  --split all --transfer-page-bytes 1000000 \
  --driver-file .lake/p27-repro-drivers/driver-v1.py \
  --driver-file .lake/p27-repro-drivers/audit-driver-v2.py \
  --extra-evidence docs/p2/20261125/p27 \
  "${p27_all_targets[@]}"
```

从原 exporter 的真实输出独立保存 `manifest_sha256`。使用以下唯一打包入口，调用一次即生成增量包并输出第 0 页：

```bash
set -euo pipefail
bash docs/p2/20261125/p27/next-private-step.sh 0
```

第 0 页内部调用 `prepare-delta-evidence.sh`，该脚本已配置使用 CurrentChen adoption attempt-003；首次 delivery 仍为 `.lake/p27-delivery/attempt-001`，与 `next-private-step.sh` 的读取路径一致。不要提前单独执行 prepare，再次生成同一目录。将输出的 manifest anchor 与原 exporter 独立保存的 SHA 比较。此后按实际输出的页数，对第 1 页至最后一页分别调用 `next-private-step.sh PAGE_NUMBER`，这些调用只读既有增量包。若第 0 页传输失败而打包已经成功，应从既有包读取缺失字节，不能直接重跑会再次创建目录的第 0 页入口。

由 `p27_delta_evidence.py verify` 在接收端逐字节重读固定旧 Git 分片和新证据。不能只相信增量包自报的 manifest SHA。

最终发布前还须核对全部 81 个已接收源码与固定 Git 提交一致，提取 26 份审计的声明与公理结果，以及 Completion 的七个完整定理类型。只能在这些实际结果齐备后更新 P2.7 的完成状态；P5 算术计数许可及整个 1+1.7482 工程不在这一完成声明内。
