# P0 `p2-prefix64` 分批入口静态审查

## 结论与检查范围

**已静态确认 root 落盘的最小隔离方案：旧 owner audit 保留 309 项版本；新固定
12 模块 audit 原字节复制到 P0 自有路径
`verification/parts/p0/CertificatesPrefix64Audit.lean`；新增
`p2-prefix64` 严格编译新三模块和新 audit，供应者明确列旧九模块，原装重放
完整十二模块。** 第 7 节记录对实际落盘脚本的逐项复查。

该方案没有发现自身模块名或路径依赖风险。新 owner audit 的内容只包含：

1. 十二个确定的生产 import，以及 `Lean.Util.CollectAxioms`；
2. 用 `env.getModuleIdxFor?` 与十二个**生产模块名**组成的数组选择声明；
3. `isUnsafe`、`isAxiom`、传递公理白名单、完整 pp.all 输出及 census。

源码没有 `__FILE__`、自身模块名、相对读文件、`verification.part2.CertificateAudit`
字符串或依赖其文件路径的定义。移动后的 audit 主模块名会变化，但它选择的是
已经导入的十二个生产模块；其自身生成声明不属于生产模块数组，因此不改变
709 项生产声明或 `P2_AUDIT_*` 输出协议。严格编译的源路径和 `-o` 对象路径须
一起使用新的 P0 模块名。

本文件是**实现静态审查和待执行命令**，不是新 Lean/CI 运行回执。本任务没有运行
任何生产编译、内核重放或 CI；已成功的 P2 专项 run 38252572597 继续按准确
源码复用。P0 最终 SHA 的根三门、原 Round3 类型门和新 Round4 类型门另行执行。

已读取版本：

| 文件 | SHA256 |
|---|---|
| 原 P0 check_batch.sh | `a2f93f436aef3d9384dbcde82117e4e6420743bec4157a018e250f6478b3b94f` |
| 新 P0 check_batch.sh（已静态复查） | `828bfb8435cc56b64bc306f8cc85528ea97225c6314b64ef8a181de07db6897e` |
| P0 check_sources.py | `b7fcfbb62374004d00551e3549e4a3c411e4562775dcece4c3e85f13d5ac6716` |
| P0 check_pins.py | `276072bb14bc52fcd9544bb3557870b1edf6d3ab2ff8aaf8360ad541f0fd3633` |
| 新固定 generate_paired_prefix.py | `45dcd50cd60f00bc676f5a2510a613b790a94eab17757f1147fb0129b0a3ab3f` |
| 新固定 owner CertificateAudit.lean | `78d45ffba85b40aa9f52e01f95473db904c270fbd299dea42f649a9572336d00` |

新 generator 与新 audit 的固定 proof 是
`f0c00f9ccce98e04af439321a92eb9fd0dd26203`，在真实成功 CI 源
`e6d6d57323cc358cef060fb243ec386c13cb662d` 和交接 head
`101bb2291cd51f9717544ce477122fdd44eda44d` 保持相同字节。

## 1. 新 case 的确切清单

可以原样加入 P0 当前 `case "$batch" in`：

```bash
  p2-prefix64)
    production=(
      ImbalancedChen.Certificates.PairedV2Batch4To64Data
      ImbalancedChen.Certificates.PairedV2Batch4To64
      ImbalancedChen.Certificates.PairedV2Prefix64
    )
    suppliers=(
      ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.PairedFibreIntegral
      ImbalancedChen.Certificates.PairedCertificateChecker
      ImbalancedChen.Certificates.PairedV2Data
      ImbalancedChen.Certificates.PairedV2
      ImbalancedChen.Certificates.AboveMuSecondCoarse
      ImbalancedChen.Certificates.PairedV2Geometry
      ImbalancedChen.Certificates.PairedV2Prefix4Data
      ImbalancedChen.Certificates.PairedV2Prefix4
    )
    replay=("${production[@]}" "${suppliers[@]}")
    audit=verification.parts.p0.CertificatesPrefix64Audit
    ;;
```

新三模块声明数固定为 Data 72、Batch 207、Prefix64 121，共 **400**。
旧九供应者保持 **309**，新独立 audit 共 **709**。

`AboveMuSecondCoarse` 虽不在新 Prefix64 数学依赖闭包中，仍是 709 项 audit 的
显式 import。因此对这个 audit 使用旧九个供应者清单是必要的；只列新模块的
最窄数学闭包，会在缺缓存的普通 checkout 中遗漏该审计所需对象。

旧 `p2`、`p2-prefix4` 的 production/suppliers/audit 保持原样，继续使用
`verification.part2.CertificateAudit` 的旧九模块版本。这样不会把旧批次
隐式扩大为对新增三模块的依赖。

## 2. 接入既有源版本和 source guard 机制

将 `p2-prefix64` 加入现有两组条件：

- 使用 import_paired_v2.py 和冻结数据的批次；
- 使用 generate_paired_prefix.py 的批次。

具体来源输入必须包含：

```text
lean-toolchain
lakefile.toml
lake-manifest.json
verification/parts/p0/check_batch.sh
verification/parts/p0/check_pins.py
verification/parts/p0/check_sources.py
verification/verify_variable_envelope_boxes.py
verification/part2/import_paired_v2.py
verification/part2/generate_paired_prefix.py
verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json
新三模块、旧九模块对应的全部十二个 .lean
verification/parts/p0/CertificatesPrefix64Audit.lean
```

保留当前脚本的每项 `git ls-files --error-unmatch`、工作树和暂存区
`git diff --exit-code`、源码 sha256 前后复核、确切 HEAD 回执。所有新 source、
audit 和脚本修改应先形成固定提交；尚未提交时源一致性拒绝是正确行为。

沿用现有的精确 source guard 命令：

```bash
python3 verification/parts/p0/check_sources.py \
  "${production[@]}" "${suppliers[@]}" "$audit" \
  | tee "$receipt_dir/source-guard.json"
```

check_sources.py 使用原项目 scanner 去除注释/字符串后拒绝 sorry、admit、
axiom、unsafe、native_decide、sorryAx 和 debug.skipKernelTC；它只是补充检查。
严格 elaboration、原装 replay、所属/传递公理审计继续保留。

## 3. 三项数据生成一致性检查：确切命令

以下变量沿用 check_batch.sh 创建的 `receipt_dir`，从集成仓库根目录执行。
**全部使用 `--check-generated`，不使用 `--emit-dir`。**

### 3.1 首行导入器和冻结完整数据

```bash
python3 verification/part2/import_paired_v2.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --check-generated ImbalancedChen/Certificates/PairedV2Data.lean \
  --report "$receipt_dir/decode-report.json" \
  | tee "$receipt_dir/decode.log"
```

### 3.2 旧四行保持同源同字节

```bash
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --count 4 --check-generated ImbalancedChen/Certificates \
  --report "$receipt_dir/prefix4-decode-report.json" \
  | tee "$receipt_dir/prefix4-decode.log"
```

此命令只再核对旧生成结果，没有执行旧四行的 Lean 数值证明。新 generator
默认 start=0、count=4，生成 PairedV2Prefix4Data.lean 和 PairedV2Prefix4.lean；
它与已接收旧源码逐字节相同。

### 3.3 新原始第 4–63 行

```bash
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --start 4 --count 60 --check-generated ImbalancedChen/Certificates \
  --report "$receipt_dir/batch4to64-decode-report.json" \
  | tee "$receipt_dir/batch4to64-decode.log"
```

这是新批次专属检查，产物名为 PairedV2Batch4To64Data.lean、
PairedV2Batch4To64.lean。不要用 `--count 64` 代替：那会尝试生成一份直接认证
64 行的不同模型及 PairedV2Prefix64Data.lean，无法对应当前保留旧四行证明、
用标准 Fin.append 组合的 PairedV2Prefix64.lean。

三个命令只核对冻结原文件、行号、精确有理生成结果及源码字节，不承担积分证明。
新 Prefix64 是手写的有限拼接证明，靠固定源哈希＋真实 Lean 编译/replay/audit
验证，不由生成器重建。

## 4. 旧九供应与接收源码的精确身份

P0 起点 28fd630 已接收旧九模块，其 source 必须保持下列 SHA256。
可在新批次进入 Lean 前执行只读源匹配；不得将重编译生成的对象强制等同为另一
环境的旧序列化对象。普通 Lake 可以复用已有同 pin 缓存、按需构建供应对象，
新运行应记录实际对象哈希。

```bash
sha256sum --check --strict - <<'SHA256'
4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22  ImbalancedChen/Certificates/RationalLogCertificate.lean
d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4  ImbalancedChen/Certificates/PairedFibreIntegral.lean
454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c  ImbalancedChen/Certificates/PairedCertificateChecker.lean
a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82  ImbalancedChen/Certificates/PairedV2Data.lean
e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7  ImbalancedChen/Certificates/PairedV2.lean
85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2  ImbalancedChen/Certificates/AboveMuSecondCoarse.lean
68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238  ImbalancedChen/Certificates/PairedV2Geometry.lean
25ffbba57b5fdff9ce23290ade00fbeaa2b38c2e44ffe9e8637404c8287aab2c  ImbalancedChen/Certificates/PairedV2Prefix4Data.lean
dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395  ImbalancedChen/Certificates/PairedV2Prefix4.lean
4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c  ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean
c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4  ImbalancedChen/Certificates/PairedV2Batch4To64.lean
11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da  ImbalancedChen/Certificates/PairedV2Prefix64.lean
45dcd50cd60f00bc676f5a2510a613b790a94eab17757f1147fb0129b0a3ab3f  verification/part2/generate_paired_prefix.py
78d45ffba85b40aa9f52e01f95473db904c270fbd299dea42f649a9572336d00  verification/parts/p0/CertificatesPrefix64Audit.lean
f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json
SHA256
```

已有验收需要重新比对时，从固定 P2 提取树执行原纯 Python 接收器，或者使用
本次 P2_INTAKE_RECEIPT.json（360 项 CI-source 比较、50 个原 gate 对象绑定、
709 项原始 compiler records 相等）。不要仅为取得相同输入的第二张回执再次
启动专项 CI。此可选 P0 分批入口按 root 的选择会重放全部十二模块；它没有在
本次静态审查中执行，最终统一 CI 已完整覆盖同一集成 SHA 时也无需另行重复执行。

## 5. 普通固定工具链中的新增模块门

沿用既有 check_batch.sh 公共执行段即可。它在对应固定 HEAD 上按以下命令
显式检查：

```bash
lake env lean --version 2>&1 | tee "$receipt_dir/toolchain.log"

lake build "${production[@]}" "${suppliers[@]}" \
  2>&1 | tee "$receipt_dir/lake-build.log"

for module in "${production[@]}" "$audit"; do
  source="${module//.//}.lean"
  object=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$object")"
  lake env lean -DwarningAsError=true -o "$object" "$source" \
    2>&1 | tee "$receipt_dir/$module.compile.log"
done

for module in "${replay[@]}"; do
  lake env leanchecker --verbose "$module" \
    2>&1 | tee "$receipt_dir/$module.replay.log"
done
```

还应保留当前公共段已有的逐模块 exact `replaying MODULE` 检查、
production＋suppliers 对象 sha256 记录、源/对象前后复核和运行后 pin 复核。
以上展示的是共同段核心命令，并未替代这些已有回执检查。
顶层 `set -euo pipefail` 必须保留，避免管道中的失败被 tee 隐去。

新 audit 的 compile log 内应得到：

```text
P2_AUDIT_MODULE {"count":72,"module":"ImbalancedChen.Certificates.PairedV2Batch4To64Data"}
P2_AUDIT_MODULE {"count":207,"module":"ImbalancedChen.Certificates.PairedV2Batch4To64"}
P2_AUDIT_MODULE {"count":121,"module":"ImbalancedChen.Certificates.PairedV2Prefix64"}
P2_AUDIT_COUNT 709
```

记录仍应包括旧九模块的 309 项声明。完整 Root Round4Audit 对 permit 14＋
本批 400 共 414 项作另一个范围明确的完整类型确认；不要把此处 709 的 owner
总数误填为 414，也不要将旧 309 再计入累计“新增声明数”。

在新 case 与三个数据检查接入并形成明确提交后，正常运行入口是：

```bash
bash verification/parts/p0/check_batch.sh p2-prefix64
```

这是一条必要时可直接执行的批次入口，本轮没有执行。若最终统一 CI 的确切
集成 SHA 已覆盖这些模块和门，不需要为同一源码重复执行此可选分批入口。

## 6. 为什么不直接复制运行新的 owner check.sh

新固定 `verification/part2/check.sh` 会先运行新 archived receiver。
后者逐一比对 P2 父提交的 424 文件，其中包含公共根、共享状态及原 P2 元数据。
P0 在 28fd630 起点已经有公共根扩展与独立接收历史，新整合又增加不同 Part；
它不满足这个**固定 P2 历史快照**的输入契约。

此外，P0 有意保留旧 prefix4 receipt 原字节；P2 后继给该 receipt 增加
fixed_proof_source_commit/tree 元数据，新 archived receiver 要求的是后继
原字节。直接复制运行会在这些准确的身份比较中拒绝，不是新证明有 Lean 错误。

正确做法：

- 原 receiver 在完整固定 P2 提取树运行，保留其已实际 PASS 的纯接收回执；
- P0 接收的生产源码字节与它的 proof 对齐；
- P0 自有批次入口检查 P0 固定提交、源 guard、三项生成一致性和实际对象；
- 12 模块 audit 复制到 P0 自有路径并记录原 SHA/字节不变；
- 旧 owner audit 和旧分批入口保持原范围；
- P0 对最终集成 SHA 运行原根三门、原 Round3 门和新增 Round4 门。

没有必要重写原 owner receiver、移除其 424 文件检查、覆盖历史 receipt，
也没有必要为搬动这份纯 import/枚举 audit 修改任何生产定理。



## 7. 实际落盘实现的复查回执

已只读复查 root 新脚本及两个审计源：

| 项目 | 实际结果 |
|---|---|
| 新 check_batch.sh SHA256 | `828bfb8435cc56b64bc306f8cc85528ea97225c6314b64ef8a181de07db6897e` |
| Bash 语法检查 | `bash -n verification/parts/p0/check_batch.sh`，退出 0 |
| 原十个 case | 逐块与固定 28fd630 原脚本完全相同 |
| 新增 case | 仅 p2-prefix64 与 p1-permit |
| 原公共 Lean/object/replay/pin 执行段 | 从 `lake env lean --version` 起与原脚本逐字相同 |
| p2-prefix64 生产 | 3，依序 Data / Batch / Prefix64 |
| p2-prefix64 供应 | 旧九个，含 audit 所需 AboveMuSecondCoarse |
| p2-prefix64 replay | 12 个唯一模块，各一次 |
| 原 owner audit | 与 28fd630 原件逐字相同，3921 bytes，SHA256 `3e62f723f3b472fdb26e5d02704119320510c764d7ff6544466cb1393c398828` |
| 新 P0-path audit | 与固定 P2 新 owner audit 逐字相同，4246 bytes，SHA256 `78d45ffba85b40aa9f52e01f95473db904c270fbd299dea42f649a9572336d00` |
| 新 generator | 与固定 f0c0 源逐字相同，16159 bytes，SHA256 `45dcd50cd60f00bc676f5a2510a613b790a94eab17757f1147fb0129b0a3ab3f` |
| 旧四行参数 | `--count 4 --check-generated ImbalancedChen/Certificates` |
| 新六十行参数 | `--start 4 --count 60 --check-generated ImbalancedChen/Certificates` |
| 生成写生产文件 | 无 `--emit-dir` |
| 新 Lean/CI 执行 | 无；只有 Bash 语法与只读文本/Git blob 比较 |

**没有发现阻止接收的实现错误。**

一个非阻塞的回执格式细节：公共对象收集段遍历
`"${replay[@]}" "${suppliers[@]}"`。新 p2-prefix64 的 replay 已经含十二个模块，
所以 object-sha256.txt 会有 **21 行、12 个唯一对象**，旧九供应者各重复一次。
实际 replay loop 只遍历 replay，仍是准确的十二次；末尾 hash 核对只是对同一路径
重复核对，没有减弱检查。为保留旧公共执行段，可保持这一实现；台账应按唯一
对象计数，不能把二十一行写成二十一个模块。

p1-permit 的新增 case 没有改动其他批次；本审查未把 P1 的新证明回执纳入 P2
接收结论，其数学及生产身份由 P1 专项接收负责。
