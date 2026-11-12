# P2 远端部署复核

**实际提交符合此前独审的 25 路径清单。** 我从父提交 `356c3782e9428098a2fcbfb18c689bef264d84fa` 的 Git 树出发，只代入清单允许的 25 个 blob，独立按 Git 树对象格式复算出整个根树 `5cd3fd854df7fe038a1206b47083241df1bcda44`。原始 commit header、作者字段及消息复算出 `aecf552cd61970fea72b4d892ab296a60e06f34e`。三个未截断的远端子树、远端 commit 与分支 ref、当地 payload 的长度/SHA-256/Git blob、`PREPARED.json` 和 `PUBLICATION_RECEIPT.json` 均对应同一清单。根树复算也覆盖所有未变路径。 [实际提交](https://github.com/UyNewNas/goldbach-formalization/commit/aecf552cd61970fea72b4d892ab296a60e06f34e)

清单包含 22 个 bundle 项、实际部署的 P2 与 VE 两个工作流，以及在 bundle 外提交的选择文件。其余六个工作流与父提交完全一致。该精确提交的启动快照只有 push 运行 `43147273995`，job `130947911930`。独立只读查询时，步骤 1–11 成功，步骤 12 正编译。102 模块的 kernel、完整类型和传递公理、对象及最终结果仍待远端证据。 [运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43147273995)

## P1.4 后续证据

三笔 frontier 费用的源码结论覆盖同一许可日程下 `X ≥ N^(3/5)` 的高模数差。原始 143 块 typed shape/顺序/编码、`cells.npy` 与 typed rows 的独立字节对应、全部 72 块的 summary/entry2、typed rows 到实际 J5/owner/积分字典、全 archive 的动态 Q3/Q4 及 owner/mask/refinement 绑定仍各有独立职责。Stored000–019 的下标绿叶只覆盖其字面表长度与位置。

对需要严格统一 `θ* < 3/5` 的使用处，应在原预八、raw/ licensed 三段按同一个预选 `ε < 1/500` 保留 `ε + 299/500`，并核对实际 lower/upper 端点继续使用同一系数、Q/rho 与原 PP 实例。现有三笔费用的等式和 sharp original-prime endpoint 的 PP 前提分别需要同源远端验收与真实分析供应。 [前沿独审记录](P1_FRONTIER_INVOICES_REVIEW.md)
