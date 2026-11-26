# P2.1 原始数值执行器增量 — 2026-11-26

本轮补齐作者原始 **96 项 W224→P160 对数**和 **P160 直接四角除法**的 Lean 证明。三个新增模块的严格编译记录、完整 owned 声明审计、独立 stock `leanchecker` 重放及两份公开契约均已通过；原始 Python `log_interval` 与 Lean 在 20,290 个有理输入上的两个整数输出全部一致。

**P2.1 已通过明示稿内范围的整节点验收：143 个项目模块，18,699 个唯一声明，零重复；独立最终审查没有未解决的 Critical 或 Important 问题。全 P2 仍未完成。** 最终结论见 [FINAL_ACCEPTANCE.json](FINAL_ACCEPTANCE.json)，逐模块源码、对象及回执绑定见 [ACCEPTANCE_MANIFEST.json](ACCEPTANCE_MANIFEST.json)，独立审查见 [INDEPENDENT_REVIEW.json](INDEPENDENT_REVIEW.json)。原增量、修复和联合回执保持原字节，其阶段字段没有被改写成整体结论。

## 本轮新增的数学结果

| 模块 | 完整 owned 声明数 | 结果 |
|---|---:|---|
| `ImbalancedChen.Certificates.P2OriginalLog96Series` | 16 | 固定 W224、P160 和 64 位缩放，证明作者的 `TAIL = 1`，并证明现有有理级数余项不超过该工作尺度单位。 |
| `ImbalancedChen.Certificates.P2OriginalLog96` | 81 | 按原整数舍入执行 96 次循环；证明幂和部分和的不变量、原形 fold 与递归的返回值相等，以及两整数解码后包含真实对数。 |
| `ImbalancedChen.Certificates.P2OriginalP160DirectDivision` | 21 | 复用既有 P160 区间类型，证明原四角商直接取整与精确有理区间除法最后一次 160 位舍入相等，并证明实数包含。 |

三者共 **118 个 owned 声明，118 个唯一声明，零重名**。审计包含私有及生成声明。允许的基础公理只有 `propext`、`Classical.choice`、`Quot.sound`；没有引入新的公理、占位证明、原生判定 oracle 或不安全声明。

对数主定理的域精确为任意有理数 `1 ≤ q ≤ 2`：

```lean
((logInterval q).1 : ℝ) / outputScale ≤ Real.log (q : ℝ) ∧
Real.log (q : ℝ) ≤ ((logInterval q).2 : ℝ) / outputScale
```

`logInterval_eq_source` 是两个逐操作对应的 Lean 整数实现之间的全称等式。Python 程序的执行对照另有下述有限证据。端点 `q = 1` 的原输出确为 `(0, 1)`，未额外收紧成另一对整数。

直接除法允许任意带符号分子区间和严格为正的分母下端。`directDiv_eq_round160` 要求分母端点有序；实数包含定理 `directDiv_contains` 从输入区间对真实值的包含自动取得有序性。不能用先舍入倒数再乘的返回值替代原程序：对精确单点 `2/3`，原下端为 `974334424887268612135789888477522013103955028650`，原上端为 `974334424887268612135789888477522013103955028651`，而旧倒数相乘法的上端为 `974334424887268612135789888477522013103955028652`。[直接除法契约](../../../verification/part2/original96/P160DivisionContract.lean)

## 原程序与执行对照

冻结作者仓库为 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。文件 `verification/data/corpus-renewal-paired-certificate-v2-20261010.py` 的 Git blob 为 `ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce`，原始 14,016 字节的 SHA-256 为 `6e47caa91bd5e47678bcd8e2a1dc35659d25d44481c41dc437002be92d8b83dc`。[SOURCE_BINDING.json](SOURCE_BINDING.json) 逐项记录第 42–47 行的直接除法和第 50–61 行的对数，以及依赖的尺度、整除和 raw 构造器。

对照程序先核对原始文件的散列，再直接载入其 AST 中的原始类、函数和参数，避免把重新抄写的算法当作 oracle。Lean 只收到规范的分子、分母输入；原程序的预期输出不会传入 Lean。输入包括两端、代表点、稿件网格相邻比值，以及不依赖历史 mask 的几何比值集合。去重后共有 20,290 个输入。

这 20,290 是 **`log_interval` 的输入数**，不表示重放 20,290 个历史账目或证明 Python 虚拟机语义。实际 Lean 输出的 SHA-256 为 `3c04ec7a1f9bef8c81d8441cc312ae97cf0cde31a5167f9c94ae06d7d7552a4e`，逐项比较均通过。[check_source_outputs.py](../../../verification/part2/original96/check_source_outputs.py)

## 云端检查与复用

执行环境为用户指定的 P2 `/workspace`，固定 Lean `4.33.0-rc1` 和 Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。所有新源码和运行脚本均在主运行时编写，云端只接收原字节并执行。

作业 `155475f0294d4ea4b22d1d92613d696e` 的 attempt-001 严格编译通过两个对数模块；直接除法仅因两条冗余 `change` 触发 warnings-as-errors 而未通过。删除两条冗余指令后，作业 `aacffde21ac8418e88d591bd7769bfc5` 的 attempt-002 复用前两条原编译记录，新编直接除法，并对全部三个 owner 新执行独立内核重放和完整声明审计。

该 attempt 还完成两个公开契约、规范输入生成、真实 Lean 执行和原 Python 比较，各命令均退出 0。随后生成归档 `original96-acceptance-attempt-002.tar.xz`，共 1,369,720 字节，SHA-256 为 `8ef2c54ee98551220e4af28cabea2448a646757fb95c41eedc10eb6cd5c9482b`；因大于脚本设定的 1,200,000 字节单次回传预算而停止输出整包，归档和检查结果仍完整保留。分块传输已成功，29 个原始读回页面组成的完整归档与云端 SHA-256 一致；25 个源码及执行输入与主工作区逐字节相同，18 个源码及对象文件符合原摘要。分块传输仅搬运已完成的证据，不重新编译或重做审计。见 [ARCHIVE_RETRIEVAL.json](ARCHIVE_RETRIEVAL.json)。

六个直接依赖沿用已接受的源码、对象和原始编译记录，详见 [accepted-dependencies.json](../../../verification/part2/original96/accepted-dependencies.json)。五个检查驱动保持既有版本不变，见 [REUSED_AUDIT_TOOLS.json](REUSED_AUDIT_TOOLS.json)。旧五根的 140 个模块和 18,581 个声明继续引用[原验收记录](../20261126-p2-1/P21_STATUS.md)，不再计为本轮新编译或新证明。

## 整节点的范围

[SCOPE_MATRIX.md](SCOPE_MATRIX.md) 将构造、加减、取负、乘除、96 项对数、P112 原 40 块查询、Q80 终点 8/12 查询和实际 Buchstab 区间逐项对应到稿内需求。十条 [P160RemainingContract.lean](../../../verification/part2/original96/P160RemainingContract.lean) 实例把其余字面 P160 操作与已接受的 `IV` 和 `Encloses` 直接相接。

联合探针已在保留旧实际对象及 native 上下文的条件下导入旧五根和新两个入口，检查 30 个公开类型与十条实例，并核对旧 18,581 与新 118 的声明集合互不重名。作业 `70e84dacdf074fc29cdd15b98c004dd0` 退出 0，Lean 探针耗时 9.301 秒。共有 143 个项目对象、6,727 个实际导入，40 个 FullCheck 均在其中。143 个项目对象及 489 个专门 native 模块的 845 个加载文件按固定摘要核对；其余外部库复用固定工具链与路径绑定，未声称本轮逐字节重哈希全部外部库。该步骤只证明同一固定环境下的兼容性和源程序形式契约，不重复授予旧编译、内核或审计信用。

本轮范围是稿内查询与所列整数算术的精确返回和真实函数包络。旧 E2 `P5U7Q80Backend` 的 VM、`qpow/box/Repr/decision-instance` 及 saved 端点等价仍保留原历史边界。自适应树、逐行费用、saved-floor 总量、指定历史表的消费者整数和主定理分别由其所属节点处理；P2.1 的结论不会替代这些验收。

## 联合检查发现并消除的声明冲突

初次三个新 owner 内部有 122 个唯一声明。与旧 140 个 owner 合并时，实际检查发现直接除法的 `simp` 展开懒生成了四个既有方程声明。只调整三个证明体的展开方式后，直接除法由 25 个声明变为 21 个；算法、导入、全部定理类型保持逐字相同。新旧全集最终为 **143 个模块、18,699 个唯一声明、零重复**。此次只重新编译和审计受影响的直接除法，原两个对数对象及其 20,290 项执行比较按精确原字节复用。原失败和原归档保留，见 [DIVISION_COLLISION_REPAIR.json](DIVISION_COLLISION_REPAIR.json)。

## 保留的历史边界

旧 140 模块验收中八份常规编译日志缺失的历史注记原样保留在总清单；本次没有补造日志或重复计算旧证明。旧归档与证据发布仍引用固定的原提交，新增三份小归档记录本轮原执行、声明冲突修复与最终联合检查。它们共同支持明示稿内范围的整节点结论。

开发期的预期失败、提交信封和真实作业输出保存在 [DEVELOPMENT_HISTORY.tar.xz](DEVELOPMENT_HISTORY.tar.xz)，逐文件散列见 [DEVELOPMENT_HISTORY.json](DEVELOPMENT_HISTORY.json)。准备过的提交参数不代替实际执行回执；尤其是被拒绝、超限或失败的尝试均按原状态保留。

## 发布与收录结果

源码与完整验收证据已通过非强制、校验原分支头的更新发布到 [`4d3284e0bb927a3f51ec00786076728f9cb070a4`](https://github.com/UyNewNas/goldbach-formalization/commit/4d3284e0bb927a3f51ec00786076728f9cb070a4)，远端提交树与主工作区精确一致。[SOURCE_PUBLICATION.json](SOURCE_PUBLICATION.json) 保留该次提交的逐文件绑定及读回结果。

[项目看板](https://goldbach-formalization-board-20261107.slava2333.chatgpt.site) v13 已部署成功，线上 `/api/board` 回读确认 P2.1 与 P2.1.3 为绿色且已核验，原始历史蓝色与前 60 个轮次均保留。全局绿色节点为 65；P2 叶节点为 30 绿、26 蓝、1 黄，运行时统计经看板 MCP 写后逐值读回。看板的 35 项既有测试全部通过。[发布记录](BOARD_PUBLICATION.json) · [线上节点回读](BOARD_LIVE_READBACK.json) · [测试执行记录](BOARD_TEST_RESULT.json)。

[现有 P2 Draft PR #11](https://github.com/UyNewNas/goldbach-formalization/pull/11) 已按看板顺序收录 P2.1，增量提交为 [`12cfb718e9317d1a5eab47d0347333dc82f5e527`](https://github.com/UyNewNas/goldbach-formalization/commit/12cfb718e9317d1a5eab47d0347333dc82f5e527)。它新增 123 个规范 Lean 路径并复用原有 20 个精确共有源码，两个历史验收配置单独存档；原 Draft 的其他内容和主配置保持原字节。全部 443 个结果文件条目均已与准备树逐一核对。该 PR 仍为 Draft，未合并；合成分支的联合编译与内核重放保持 `NOT_RUN`。[DRAFT_ADMISSION.json](DRAFT_ADMISSION.json)。
