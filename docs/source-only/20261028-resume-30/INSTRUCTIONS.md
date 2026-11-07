# 本轮子任务统一约束

权威仓库：E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation，原稿：../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex；scope: docs/source-only/20261028-paper-first/SourceReview-V2.md。请先读你的 TASKS.json 任务项、scope、最近 source_directory 的 boundary/registry/Lean，再找精确原稿步骤，避免重复现有工作。所有 exec 必须显式 Set-Location 且 $ErrorActionPreference=Stop，禁止无界列举或扫描 .lake。指定 .lake/source-reviews/drafts 目录可按需定向读取。

每人独占 output_directory，只写新 .lean、REGISTRY.json、REPORT.md。共享文件、生产 ImbalancedChen、旧 draft、Git index/commit/push、看板一律不改。不要再派子代理。不要编译、跑 Lean/lake、修编译、执行大型数值 checker、检查额度。父代理集中验收与更新看板。

目标是实质原稿内部证明和接口连接，禁止仅把待证 hMedium/hPP/hUpper/hLower/hCertificate 或最终目标作为假设再包装。允许精确列明原始引用经典 primitive；已存在 Mathlib/本地库引理优先复用。不得 sorry/admit/新增 axiom/unsafe/虚构外部 theorem，不改定理到较弱无关目标。如果整体任务太大，完成真正消除下一处证明义务的必要引理，明确未完成原目标。原稿存在错误/证明缺口先提供准确原文与数学反例或缺失推理证据，并及时告知 root；实现缺口与原稿缺口分开。

source-only 依赖必须在 registry 精确注明路径、SHA256、声明/namespace；生产导入按真实名称，draft 依赖给出安装/import 对应，不可假装已编译可用。无须把库代码重复抄入。REGISTRY.json 必须记录 task_id、paper_anchors、source/import hashes、新增引理、实际消除的义务、remaining、complete_module(是否文件文本闭合)、task_complete(原分配目标是否达成)、compiled:false、formal_credit:0。REPORT.md 用清楚中文说明证明主线、前提、实质进展与缺口。每个完成源码需能供编译专员直接取用。验收只做源码逻辑审阅，不可声称内核通过。
