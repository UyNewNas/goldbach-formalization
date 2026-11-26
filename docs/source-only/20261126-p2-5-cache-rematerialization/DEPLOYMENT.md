# 恢复包部署闭包

已核对 HEAD `1e80a5fa2fa2dbb346dbdef5760a7361a8001a46`、index 和工作区。原恢复程序的 124 个 `repo_file`、13 个 `repo_archive` 以及三个启动 manifest 都已逐项核验，明细在 `DEPLOYMENT_INPUTS.json`。

**无需新增压缩包，也无需提交五份原 RESULT 全文。** 五份原文共 24,565,777 字节，均可从已 tracked、与 HEAD/index 完全相同的五个 xz 无损恢复；原压缩证据共 3,671,928 字节。`bootstrap_receipts.py` 只提取原字节，核验 SHA/长度，全量预检完成后才独占写入。已有不匹配文件会使部署停止，不覆盖，不运行 Lean。

## 必须进入本次 publication 的最小新增路径

```text
docs/source-only/20261126-p2-5-cache-rematerialization/restore_p3_cache.py
docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json
docs/source-only/20261126-p2-5-cache-rematerialization/bootstrap_receipts.py
docs/source-only/20261126-p2-5-cache-rematerialization/RECEIPT_BOOTSTRAP_SELECTION.json
docs/verification/20261126-p2-5-resumed/p3-cache-recovery/RECOVERY_MANIFEST.json
docs/verification/20261126-p2-5-resumed/p3-cache-recovery/expected-original-witnesses.json
```

这六项共 603,262 字节。父线程选择通过 Git 交付 payload 侧车时，还加入本包的 `P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json`：5,534 字节、SHA `24cf2b46e8850bf2147ac5e751049a3915466ab6131d12ab07405cb9478f0c5d`。2.64 MB 对象归档继续使用已安排的外部交付，不进入 commit。

五份 `RESULT.json` 不需要 `git add`。其原目录为 `consumer-attempt004`、`consumer-attempt005`、`field-explicit-attempt005`、`field-final-attempt004`、`field-symbolic-attempt006`。第一份来自其 `RESULT.json.xz`，其余来自各自 `ACTUAL_EVIDENCE.json.xz` 中唯一的 `RESULT.json` 原文字符串。8 项本地恢复/不覆盖核验已通过，见 `BOOTSTRAP_LOCAL_VERIFICATION.json`。

## 固定身份

| 文件 | SHA-256 |
| --- | --- |
| 原 recovery runner，未改 | `d6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542` |
| 原 recovery selection，未改 | `cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf` |
| Bootstrap runner | `46fa4a87040115bd8a1fa59abb598836063363374c2878992e4b7ac6ad000293` |
| Bootstrap selection | `845ebbb50bc889d05d6ecb81e41b44eb2e95ffafa187dc7c82bae4181170cf31` |

## 最小顺序

1. 发布上述路径及审核材料，P3 fetch 并 checkout **本次新 publication**，保持 tracked checkout 干净。把准确的已发布 bootstrap 提取到 `/workspace/p25-bootstrap-receipts-20261126.py`。
2. 执行以下前置。`P25_RECOVERY_PUBLICATION` 必须是本次发布的完整 40 位 commit：

```bash
python -B /workspace/p25-bootstrap-receipts-20261126.py \
  --apply \
  --repository /workspace/p25-q96-20261125 \
  --manifest /workspace/p25-q96-20261125/docs/source-only/20261126-p2-5-cache-rematerialization/RECEIPT_BOOTSTRAP_SELECTION.json \
  --manifest-sha 845ebbb50bc889d05d6ecb81e41b44eb2e95ffafa187dc7c82bae4181170cf31 \
  --publication "$P25_RECOVERY_PUBLICATION" \
  --runner-sha 46fa4a87040115bd8a1fa59abb598836063363374c2878992e4b7ac6ad000293
```

3. 用同一 publication 提取 recovery runner。运行 `--plan`；payload archive 指向 `/workspace/p25-cell00-recovery-delivery/objects-local-only.tar.xz`，payload manifest 使用本包已发布侧车及其固定 SHA。依据真实 plan 继续 `--restore`；历史非对象字节未齐时不能启动 normal 重建。
4. 全部恢复门禁满足后，在**同一新 HEAD**运行原 v7，并把**同一个 publication**作为其参数。

当前 v7 允许 `initial_head == publication`，仅在二者不同时要求祖先关系并 checkout。`be20f0b050bb787ecb98f9afdd9b6a386706f45a` 是旧 consumer005/Decoded 的 owner 来源，应原样保留；它不是当前运行 HEAD 的要求。不要回退到 be20，也不要站在新 HEAD 却向 v7 传较老的 fd92 publication。原 v7、原 recovery runner/selection 和生产 Lean 源码均未修改。
