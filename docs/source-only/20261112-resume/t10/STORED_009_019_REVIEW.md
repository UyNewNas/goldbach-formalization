# Stored009–019 远端验收

**已有绿叶可扩为 Stored000–019。** 每一块的字面父表有 4,096 行，每个有效块内下标的 `sourceIndex` 等于块起点加该下标。新增 11 块覆盖 `[36864,81920)` 的 45,056 行。三批合计 81,920 行，连续覆盖 `[0,81920)`。精确类型、各块源与对象 SHA-256 见 `STORED_009_019_ALLOWLIST.json`，SHA-256 为 `5f817006db2cbd5ccc55e969144a2d5f66dbae8f94bc6144daf2d7fb30fb2cc7`。

运行 `43122130246` 的 attempt 1、job `130864952699` 已成功结束。源头为 `356c3782e9428098a2fcbfb18c689bef264d84fa`，唯一父头为 `f12fde61ac82c5e001332dba4a5eca5f4eda24fb`。我重算了 artifact `13910907180` 的 SHA-256 `42168a2ef0b44081db03eb4b7051a097146b66a5d48c3e6638d22ca77eb04f36`，比对 GitHub digest、ZIP 长度、59 个成员及解出的每个成员字节。 [GitHub Actions 运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43122130246)

逐块回读 `124d09f9fc74e7b78261e2471a573f1657b5633e` 的原始 Git blob，每个字面 `rows` 数组的源文本与这次实际编译源一致。十一份修复后的源码及 `.olean`、`.olean.hash` 均复算匹配验收快照。三批的公共父模块源 SHA-256 一致，为 `87f1a913c44347bac32b2ed3458b4e16e136a81a0e7d98f38b4296d722a44a0e`，其 `.olean` 快照 SHA-256 同为 `5279a69ca840610060458af722024d79af001be859eb1f8efc78d7c15ae7c2af`。本批 ZIP 实际保留十一块的二进制，父模块保留编译与重放日志和对象快照。

`batch-build.log` 和 guard 命令记录均包含全部十二个模块，锁定 Lean `v4.33.0-rc1` 与 `-t0 -j2 -M12288`。checker 实际重放同十二项。父模块 27 个声明，十一块各 260 个，共 2,887 个不重名声明。每模块序列化名称清单、环境所有权清单及逐声明输出完全一致。逐条确认两种完整非空类型、无截断、无 unsafe、partial 或公理声明。传递公理仅出现 `propext` 和 `Quot.sound`。两个端点定理 `rows_size`、`source_index_at` 在每个实际模块、数组和起点上分别核对。

`PASS_SELECTED_BLOCKS_ONLY` 与 `whole_t01_accepted=false` 符合实物。此次扩围保留原绿叶计数，`oldQ80`、`newQ80` 的正确性，完整 72 块 summary / entry2，143 块几何与原始 cells 数据，以及完整第五层积分仍需各自验收。
