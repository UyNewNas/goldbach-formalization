# Stored020–030 远端验收独审

GitHub Actions 43153562459，attempt 1，job 130968171010，head 3fdc2e362d97a03aabef60cfdf68da2f7597be35，直接父提交 356c3782e9428098a2fcbfb18c689bef264d84fa。父线程和监测线程记录终态 success。第一次本地下载截断。实际逐件读取的是 ci-watch-v2/stored-blocks-020-030-43153562459-recovery.zip，artifact 13924520315，80402328 字节，SHA256 5d05d304fe22d56efe1315281a53e4856c256418ef5e4397b70687f26d12966b，与监测线程取得的 GitHub 摘要一致。独立流式复算归档及全部 62 个成员，展开共 332980972 字节。

**允许扩大现有单一绿叶到原 Stored000–030 的连续 126976 行。** 新增 11 块从 020 到 030，各 4096 行，总计 45056 行，sourceIndex 为 [81920,126976) 中的整数。001–019 与 000 的既有证据依旧沿用先前两次允许表。尚有 41 个原块；整 72 块、143 项几何、typed/Q80 与后续积分、整个 T01 均保持各自原状态。

- 实际依赖为 Lean v4.33.0-rc1、Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1、goldbach-lean 09b97db5764ade1246bfb77206baa1b124760958。每个新块的 guard 编译命令绑定本模块输入、输出和 setup，trust 0、2 threads、12288 MiB、两个 D 选项 maxRecDepth=100000 和 maxHeartbeats=4000000 均与选本一致，slot owner 为该实际进程。guard 为 837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877。运行时审计的 state 和 command log 两个 SHA 均与实际成员相符，51 个命令，24 个 source 命令。
- 12 个实际 Built 行、12 个 bundled checker replay 行与 11 个目标块加 StoredParentTypes 的清单精确相等。每个源、.olean 与 .olean.hash 均与 BATCH_OBJECTS_BEFORE.json 中的实际路径复核。该快照 SHA256 为 34f2565b60ee89900c1c88f25f78606bd07562cfc05bf4d5296297d5ca19ca26。11 个块的完整源等于所选原 Git blob 经允许的单项变换所得后像，也逐字等于 Fine/Winner 对应的新选源。原 literal rows 与 rows_size 及其余源字节均得到保留。
- 完整类型审计中，12 个模块的 serialized names、环境所属模块 names 和逐声明输出的多重集逐项相等。实际共有 2887 个全局唯一声明，父模块 27，每块 260；每条均有未截断的完整和 readable 类型、无 unsafe/partial/axiom 声明，传递公理仅观测到 propext 2841 次、Quot.sound 2838 次。每块有完整的 64 个明确名称的分段定理，以及 rows、rows_size 和 source_index_at。对每块这三项，将先前已审 Block009 的 complete 及 readable 类型替换模块名和真实起始索引后，分别与本批输出逐字比较一致。行数、真实 rows 数组、每个 Fin 元素与原 sourceIndex 的等式全部进入内核。
- 此次确实保留了父模块源、119440 字节的父 .olean 和 sidecar。实际父 .olean SHA256 为 5279a69ca840610060458af722024d79af001be859eb1f8efc78d7c15ae7c2af，与上一批快照相同。完整 setup/trace/ilean 等恢复要件仍须单独验收。不能据这 12 组源及 .olean 对 Fine 1816 模块宣称已有可恢复的 Lake cache。

逐成员摘要、十二组源和输出、实际完整 public types、所有边界在同目录 STORED_020_030_ALLOWLIST.json，59740 字节，SHA256 5fa5ddda0d11e2578640cf8b30c9d1ca83d92f7f055df1776b45d6cebba37aaf。本文离线静读已完成的远端证据。

