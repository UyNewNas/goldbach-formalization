# 1+1.748 原稿内部证明：30 项独立源码交付

本轮按依赖拆分 30 个独立代码任务，优先原稿内部推导及实际对象衔接。编译、安装和由编译产生的修复交由用户负责；本目录没有运行 Lean、lake、内核重放或大型数值 checker。

`TASKS.json` 保留原分配目标与当前状态，`DELIVERABLES.json` 列明每份实际源码的 SHA256、文本行数、词法声明数、独立审阅及剩余义务。`NEXT_ACTIONS.json` 收集所有登记的剩余义务。每项独占目录内有 Lean 源码、`REGISTRY.json` 和 `REPORT.md`；源码依赖及建议安装位置见各 registry。source-only 依赖必须按其真实模块名和哈希安装，不能当成已存在的编译产物。

`reviews/` 是与作者分离的源码逻辑审阅，核对证明数学主线、原稿范围、前提、实际父 cap/同一 rho 和依赖哈希。`SOURCE_REVIEW_PASS` 仅表示所述局部源码可保留，不表示已通过 elaboration、内核或完整传递依赖验收。局部引理完成与原分配任务闭合分开记录。

重点增量包括：S1 除数矩支付和 S2 同 d 包的有限 Fubini；canonical 素因子分解与固定块重索引；实际低 conductor 系数 SW；同一 rho 的 count/互素均值与 retained-frontier 展开；混合 W/tent 选择器及真实 W chamber；冻结父 cap 的整数平方门槛；实际积分无重计数/Fubini；真实 Mellin 模态、任意 occurrence-word Leibniz 与全 rank Cauchy 尾积分。

仍须保持的边界：完整模数秩排除不是 BV 估计；单个局部 cap 与全局非零系数支持的合取不证明该局部叶的 q-fibre 归属；`decide` 证明项未执行，不计为数值核验；整数总和不替代积分、Wu-h licence 或完整证书。当前未确认新的原稿数学缺口；实现遗漏和错误候选的修正均单独说明。

主定理仍为 **OPEN**。本轮新编译/内核正式验收为 **0**；历史正式基线保持 266 模块、8851 完整声明、167 收据，30% 为历史人工估计，不因源码增长自动改变。

`refresh_snapshot.py` 只收集本目录源码事实、剩余义务及 root 会话额度事件，并同步现有看板的数据文件；不执行证明。`ROOT_QUOTA.json` 为带时间的 root 额度快照，剩余不高于 10% 时停止新增证明工作并保存看板状态，子代理不检查额度。
