# Actual small-payment：部分来源归档

**SOURCE_ONLY / NOT_CLOSED / ZERO FORMAL CREDIT。** 未修改证明、active Lean、原 AUDIT/REVIEW、rank manifest 或 AllRank 已接受成果；未编译、未运行云命令、未 commit/push。

## 归档范围

当前可按精确 pin 或唯一字节选定 **764 个 project modules**。只新增 **70 个原供应源码**（680944 bytes），复用现有 694 个源码路径，没有重复复制已有字节。原 commit 分布：

- 20701a39ebd15e41b39b8f1a9f5a977312169352：67 个文件。
- 69ee64474e5832b35b159ba9d4920f31203fcdf9：3 个文件。

全部新增 Lean 文件逐字节保留原源，并验证 SHA256、Git blob SHA1 与原 commit/path。位于 reused-suppliers/ImbalancedChen/；完整逐项列表及相对安装路径见 SOURCE_INSTALL_MANIFEST.json 的 new_archives，不依赖 scratch 安装。

## OriginalRootQBound 与 owner 兼容

OriginalRootQBound 原源确实只在恢复 scratch 集中，未进入原 repo/rank manifest。已归档固定 69ee64474e5832b35b159ba9d4920f31203fcdf9 版本，SHA256 a3db3b4be59382c61491e9bc3436bbef9b57a924ea71748a693302810479b0ae，Git blob e519bfcf7c8bfbfab41c32e574380b8cb140a282。同来源 ActualMarkedRootConsumer、ActualEmptyLevelUnpaidReceipts 一并沿原 import 归档。

三个完整 H430 owner 均选择 rank manifest 的机械 postimages：TaggedArithmeticReceivers、HistoryQuotientCounts、SeedHistoryMass，避免完整原 owner 与抽取 core 双重声明。Fibre 固定为 7fdc2cca74d8711cd7e24db361518c9ba3840dc70df763b52bb42837d3b0410b。

RootIntervalTheta 按直接经典 caller 的 classical-h430/REGISTRY.json 精确 pin 使用 cc3ef5f1c7d692d1b062ffb0c2738bf9f43edd87ce98918900367ecec39e6833；未依据日期选择 later literal-public-api 版本。

GlobalFloorBaseLedger 只从已有固定 index 的 20701a39ebd15e41b39b8f1a9f5a977312169352 原路径恢复，验证 Git blob f21fd3d9a677efc7697df2fbd8cef07cfa8599b6，没有继续扩大寻找新版本。

## 明确未决

仍有 **5 个缺失 project import**、**1 个未决版本分叉**；UNRESOLVED_IMPORTS.json 给出直接 importers 和 consumer 最短 import 链。

- 缺失：ImbalancedChen.P2N48TermOneAllPatternClosedVolumes。
- 缺失：ImbalancedChen.Part5OriginalH430ActualFeedbackQuotientRemainders。
- 缺失：ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge。
- 缺失：ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget。
- 缺失：ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource。
- 版本未决：ImbalancedChen.P5OriginalSignedMidpoint。保留原版/修复版各自路径、SHA 和安装记录，未擅自选择。

另列出 **71 个非标准 native/research 外部 module 边界**，不当作已获得源码、对象或收据资格。归档不能替代 project closure、编译、stock replay 或 owned audit；本目录保持 source-only。

## 复现

按 SOURCE_INSTALL_MANIFEST.json 每个 selected_sources 项，将 repository_source_path 的精确 SHA256 文件映射到 install_path。不要把所有 source-only 目录同时放进 Lean 搜索路径。缺失和版本分叉解决前不声称 consumer 可完成 build。

归档结束后已复核新增源码、三个 owner-postimage、原 consumer 和原 AUDIT/REVIEW 哈希。全部既有小付款文件的哈希保留在 manifest，验证未变。
