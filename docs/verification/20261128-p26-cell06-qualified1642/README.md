# P2.6 Cell06：qualified1642 增量证明检查点

本检查点保存已接受的 1642 项项目证明前缀。它在 [through1641](../20261128-p26-cell06-through1641/)（证明提交 e4c7fd9205bd4a31655b8e8a101b4496e29a4d4f）基础上只新增 ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode000To014。

该模块的 normal、官方 stock leanchecker、full-owned 三份成功记录来自原 geometry8p，身份和全部原始日志不变。本次没有执行新证明模式。原 full-owned 核验为 10 canonical、0 shared、13159 imports；自1512检查点累计 canonical 为18178。

## 资格与原失败批次

新资格协议 source_revision4_transport_verified_pending_prefix_v1 在独立目录中接受这一成功前缀：实际校验原143258个输入文件、16974482127字节，完整映射 SHA 为7e7563e5852a08e36dcb8181581f1f0dca6e480a5c16f01adb5f4b6467548889。该次真实资格任务为519716dcd5124ff58dd4d0b81b2fe336。

原 geometry8p 整体仍失败且未封口，没有补造旧 POST、seal 或 accepted context。ShapeArrays 的原失败五文件 tuple 和含编译错误恢复标记的原日志完整保留，只作为失败证据。归档内 ShapeArrays 修改前后源码保存两处 proof-body 修订，修改后仍是候选源码，本检查点不给它证明信用。公开 Lean 树只新增已接受的 RowsNode000To014。

## 实际增量归档

实际 MCP 打包任务 e0956280efb6484cac44458b0ec70415 成功退出：41.318677226秒，采样树 RSS 峰值420093952字节。

- evidence.tar.xz：10529540字节，SHA256 5b42a3a58f02f504c980e3a8c895d3b7c0ed4ea1a6dc169e556a3a5903d9bb55。
- 175个 regular members，展开104913179字节；内外 MANIFEST 逐字一致。
- 实际局部读取188个文件、97178774字节，涵盖元数据、局部D和选定证据。
- 原 G 的143258份物理输入完整保留为引用，其中143239份没有在打包时重新读取；打包不计新的 G 校验。
- 4069份资格复制体的引用分区完整：39份实际归档、1份同字节 payload alias、4029份 reference-only。4030份复制体没有宣称在本次打包中读取其物体。
- 12份资格元数据、37份原8p文件、完整 typed audit、失败 tuple、source revision、源码锁和测试证据均保留；原 normal 物体以精确SHA保存。

[CAPSULE.json](CAPSULE.json) 与 [MANIFEST.json](MANIFEST.json) 给出原始逻辑路径、物理来源、别名与全部 SHA。公开文件只是同字节副本，不改写其中历史身份。当前上下文为 [CURRENT_ACCEPTED_CONTEXT.json](CURRENT_ACCEPTED_CONTEXT.json)，SHA256 e22fc5fc1f9803baa6269e255378b785d39fa669d8324399b7242f9143c0b5fa。

[INPUT_CONTRACT.json](INPUT_CONTRACT.json)、[PACKAGE_COMMAND.txt](PACKAGE_COMMAND.txt)、[MCP_PACKAGE_RUN.json](MCP_PACKAGE_RUN.json) 保存真实输入及执行记录；[SOURCE_REVIEW.json](SOURCE_REVIEW.json)、[INPUT_REVIEW.json](INPUT_REVIEW.json)、[COMMAND_REVIEW.json](COMMAND_REVIEW.json) 和 [REVIEW.json](REVIEW.json) 分别保存独立源码、输入、命令与实际归档复核。

## 依赖与剩余范围

工具链为 leanprover/lean4:v4.33.0-rc1，Mathlib commit e4c91783ca8e6a7c693ae624ade32fd22d4e43c1。传递依赖沿原 lake-manifest.json 锁，运行时及继承 bulk 依赖前述归档链和原始物理引用。

本检查点时 Cell06 core 尚余191个 owner，另17份 postfinite 为后续候选。完整积分 cell 仍只有0、1、5；Cell06 integral、完整13-family/28918-row覆盖与全局 P2.6 均未完成。original_full_snapshot_verified 仍为 false。degree6/exp3、Q80/Q96、保存的 max(old,new)、原97 gates、物理域及原 policy/history 边界保持。
