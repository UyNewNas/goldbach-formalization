# P2 原字节恢复设计：prepared-only，当前环境阻塞

## 当前结论

本文件只记录来源和后续阶段的验收条件，不是恢复成功收据，也不是执行授权。

冻结的外部输入清单没有改变。原 P2 上缺失 41,505 个 Mathlib 文件，原始字节合计 5,712,781,792 B。完整缺失清单已经无损取回并本地复核；这恰好是 8,301 个模块各自的 `.ir`、`.ir.sig`、`.olean`、`.olean.private`、`.olean.server` 五种文件。其余 28,878 项在该次探测中只有存在性和大小相符，尚未据此重新确认 SHA256。

官方缓存的源码提供了一条可能不需要重新编译的取回路径，但**可访问性和原字节匹配均未建立**。实际任务 `d61bbe8cdf374c8eb298fe462cd6381a` 对两个官方 commit-index URL 的 GET 均得到 `URLError: Tunnel connection failed: 403 Forbidden`。这是网络隧道拒绝，不是官方对象返回 404；不能据此断言索引不存在。探测脚本 exit 0 只表示完整记录了探测结果，不能称下载成功。

现阶段停止下载、解包和恢复变体，不更换代理、直连 IP 或绕过网络限制。继续的前提是环境维护方恢复符合原清单 SHA256 的文件，或提供已经批准且可用的原缓存访问。不会重新 qualification、改快照、重编译原生输入或降门控。

## 固定绑定与实际证据

- 项目源码 pin：`b55fa93d39e6a4ddf2abd37b9b8481078e329f70`。
- Mathlib pin：`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
- Lean pin：`62eed1db4d67327ec8120be05f1a1b0847d74561`。
- 原 external snapshot：`/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json`，20,904,189 B，SHA256 `ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27`。
- 原 context signature：`71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90`。
- 当时 registry SHA256：`3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445`。
- 完整 missing inventory 本地文件：`/tmp/p24-b-rfl-diagnostic-20261126/native-missing-complete-inventory.json.gz`；2,034,654 B，SHA256 `371180d13bcfc651df35e9712dba3b1ce6a1bc1aa5ad1020f33e18fd0b836a57`。解压后 14,064,089 B，SHA256 `297f3c77f8494ac78ba5694872bf214b464bea3c601404fa2a0bf61f3251f505`。
- 官方索引探测原日志：`/tmp/p24-b-rfl-diagnostic-20261126/native-official-cache-index-probe-01.log`；679 B，SHA256 `ee10722af6648d5e44310fcfcefecaa041fd447752879353adf10db0aa102da0`。
- 已有缓存探测原日志：`/tmp/p24-b-rfl-diagnostic-20261126/native-recovery-cache-probe-01.log`；2,463 B，SHA256 `4da07697e39e5efcfc71111b544aaa14673943366d162c00ae4520b7d0837c0a`。

| 缺失后缀 | 项数 | 原字节数 |
| --- | ---: | ---: |
| `.ir` | 8,301 | 228,368,568 |
| `.ir.sig` | 8,301 | 1,460,976 |
| `.olean` | 8,301 | 1,817,987,920 |
| `.olean.private` | 8,301 | 3,562,823,952 |
| `.olean.server` | 8,301 | 102,140,376 |
| 合计 | 41,505 | 5,712,781,792 |

表中每一项都位于 `/workspace/compile-deps/mathlib/.lake/build/lib/lean/`。本次只读探测未改变任何 native 文件，未运行 qualification，也没有 proof credit。

## 锁定 Cache 源码的精确接口

本地五个源码副本位于本目录，完整 SHA256 见 `locked-cache-source-index.json`。来源统一为上述 Mathlib pin 的 `Cache/`。其中 IO、Requests、Hashing、Lean 四文件与实际 P2 只读缓存探测记录的 SHA256 完全相同；Infra 依据此前锁定 GitHub 获取内容保存，没有在本次 P2 探测中独立哈希。

### Commit index

`Cache-Requests.lean:1188–1211` 的 `commit` 用 `git rev-parse HEAD` 作为文件名；具体 Git 调用见该文件 388–389 行。内容由下式构造：

```lean
("\n".intercalate <| hashMap.hashes.toList.map toString) ++ "\n"
```

`Cache-IO.lean:258,273–274` 将 module hash 定义为 UInt64，并将它们收集到按 `compare` 排序去重的 TreeSet。因此实际非空索引格式是**十进制 UInt64，每行一个，末尾 LF**。它没有 module 名称到 cache key 的映射。仅看到某个索引或其条数，不能证明覆盖所需的 8,301 个模块；也不能从 external snapshot 的 SHA256 直接算出 UInt64 cache key。

Commit 文件固定使用 `/c/<commit>`，不加 repo namespace。`Cache-Infra.lean:97–103,124–128` 与 `Cache-Requests.lean:355–365` 定义了下面两个官方候选位置和对应包位置：

```text
https://lakecache.blob.core.windows.net/mathlib4-master/c/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1
https://lakecache.blob.core.windows.net/mathlib4/c/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1

https://lakecache.blob.core.windows.net/mathlib4-master/f/<16hex>.ltar
https://lakecache.blob.core.windows.net/mathlib4/f/<16hex>.ltar
```

以上是源码定义的地址格式，不是可访问性或对象存在性的证明。两次实际索引 GET 均已经被隧道 403 阻止，不再探测替代访问方式。

### asLTar

`Cache-Lean.lean:19–29` 每字节写两个十六进制字符，共八字节，即 16 位零填充小写十六进制，加 `.ltar`。对已经严格解析、范围在 `[0, 2^64)` 的十进制值 `n`，Python 格式等价于 `f"{n:016x}.ltar"`。这个 UInt64 文件名不是待恢复文件的 SHA256，不能替代原清单逐文件校验。

### leantar 位置及原 CLI

`Cache-IO.lean:95–104` 通过 `lean --print-prefix`，查找同一 sysroot 的 `bin/leantar`。实际只读探测已确认：

```text
/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leantar
2,692,960 B
SHA256 06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3
```

`Cache-IO.lean:108–113` 的原库调用为：

```text
leantar [可选 -f] -x --delete-corrupted -j -
```

stdin 为紧凑 JSON 数组。该文件 431–442 行明确支持重定向基目录的对象：

```json
[{"file":"/独立试验目录/输入包副本.ltar","base":"/独立试验目录/解包根"}]
```

这里记录的是原 API，不是在当前环境执行该命令。`--delete-corrupted` 会涉及输入包处理；未来单包试验只能对本任务的独立试验副本使用原调用，保留下载原件和 SHA 记录，不能将其指向现有缓存或 native 路径。不用 `-f`。

`base` 参数是解包路径重定向接口，**尚未审查 leantar 内部路径校验，不能把它当成操作系统沙箱**。未来实施前必须确认绝对路径、`..`、symlink 等不能逃逸独立可写区域，或由执行环境提供只允许该区域写入的隔离。仅在解包后检查目录不构成“从未写到外部”的证明。

## 为什么原保全包不能填补这个缺口

实际 `kernel-metadata.zip` 探测为 248,047 B、24 个成员，未发现 Mathlib native 成员。探测过的常规 Mathlib 缓存目录均不存在或没有 `.ltar`。这些结果不等于穷尽环境方备份，但当前没有已确认的本地恢复源。

原 exporter `/tmp/p24-export-retention-recovery-20261126/original-exporter-test.py`，SHA256 `fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645`，49 行及 365–369 行明确只选 provenance 文本或原 `.trace`，并排除 `.olean`。它不保存 Mathlib `.ir`/`.olean` 二进制。旧 581,735,403 B 导出包及其已验证 xz 保全方案不能据此重建当前缺失的 5.71 GB native 字节；1752 个共享 staged 成员也不能等同于完整 Mathlib 二进制备份。

## 仅在访问问题由环境方解决后的阶段设计

### 0. 固定恢复白名单

重新读取原 snapshot，先确认其原 SHA256、context signature、source pins、工具、registry 与当前恢复授权一致。完整 missing inventory 是唯一待恢复路径和字节要求来源；不得从可下载内容反过来重建新资格清单。并发出现任何已有文件都先停止并记录，不能覆盖或当作已经验证的成功。

### 1. 官方索引：只读获取

在获准访问后，原 URL 的 GET 只写独立派生目录，记录状态、响应长度、原始 body SHA256 和实际地址。严格按上面的 UInt64 格式解析；保留原 body，不更改或“修复”索引。仍须区分获取成功、索引格式正确与覆盖所有缺失模块三个不同结论。**当前停在本阶段的访问前提，尚未取得 body。**

### 2. 单包试验：生产目录零写入

从取得的索引选择一个包，先保存下载原件和 SHA256，再使用已记录 SHA 的同 sysroot leantar，在经过路径隔离核实的独立 `/tmp` 目录解压一个试验副本。JSON `base` 指向独立解包根。完整记录 decoder 返回码、成员路径/类型/大小/SHA256。

索引没有 module 映射，所以不能宣称第一包一定含待恢复模块。只有它实际解出的相对路径能对应白名单，且对应的原文件大小和 SHA256 均一致，才有“该包可恢复这些原文件”的证据。包级 hash、HTTP 成功或 decoder exit 0 都不足够。若路径逃逸、特殊文件、同名冲突或字节不匹配，停止并保留失败证据；不触碰 canonical。

### 3. 完整覆盖与容量计划

单包成功以后，先建立“官方包原件 → 实际解包成员 → frozen missing path/bytes/SHA256”的覆盖记录，要求全部 41,505 项最终各有经过检查的来源。不得用数量相等代替逐路径覆盖。源码 `Cache-IO.lean:282–319` 显示 `.ltar` 还可能包含 `.ilean`、C、hash、trace 等额外成员；它们不属于本次恢复白名单，不安装到 canonical。

本次只读 inventory 后可用空间为 12,014,116,864 B。只计缺失文件，最终安装占用为 5,712,781,792 B；同时保留一份全量解包副本至少要 11,425,563,584 B，还未计压缩包、额外成员、目录和日志。因此不能承诺一次全量下载、全量解包及复制都能容纳。未来应根据单包和分批测得的实际大小、文件系统块占用与实时余量制定有界批次，持续保留至少 32 MiB 及当前步骤所需开销；不得通过删除现有任何数据换空间。不能把未知压缩率当预算依据。

### 4. 原路径恢复：仅创建缺失文件

既有用户 continue 授权已经覆盖必要、可逆且逐原 SHA 匹配的缺失文件恢复；在环境方提供获准可用的字节来源，并通过前述路径隔离、完整覆盖及容量检查后，可按该授权逐项安装已经核验的字节，无需再次向用户请求许可。每个目标必须仍不存在，且其父路径为允许的真实目录，不通过 symlink。使用同目录暂存及不覆盖发布机制，例如已完成 fsync 的暂存普通文件加原子 exclusive-link；不能用会覆盖目标的 rename/replace。已有目标即使字节相同也不得由本恢复步骤覆盖，应记录冲突交独立复核。

每个新文件记录来源包 SHA、原清单 SHA、安装后 SHA、大小、实际路径与成功/失败状态。中途失败保留真实完成子集和 pending 集合，不报告全量恢复；不删除或回滚任何既有文件，不修改 snapshot、registry、源代码或资格元数据。

### 5. 原门控确认

全部缺失路径恢复后，用**未修改的原 `ExternalSnapshot.verify`** 重新验证完整 70,383 项，涵盖此次缺失项和此前只核过大小的 28,878 项。原实现 193–208 行还核 snapshot SHA、各 source pin、原 import/source Git blob 和路径解析；须保持同一 binding/context signature，不能换新资格或新 snapshot。使用新进程，避免继承恢复前哈希缓存。

同时核项目 source、registry、工具与恢复前绑定不变。只有原检查全部成功才能说明环境恢复了原输入条件，随后才可继续尚未执行的 B WHNF 诊断。环境恢复本身没有新的编译、proof、replay、owned-audit 或 canonical 验收 credit。

## 当前停止条件

访问被拒绝、原包不存在、包的原字节不匹配、decoder 路径隔离未核实、完整覆盖不足、空间不足或已有文件出现冲突，都必须保留阻塞状态，不能用重新 qualification、重编译、修改原 SHA 或放宽检查来继续。目前确立的阻塞是缓存访问被网络隧道拒绝且没有已确认的本地完整二进制恢复源。
