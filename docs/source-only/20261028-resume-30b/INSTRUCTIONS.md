# 第二批：继续原30个目标的真实缺失衔接

首先读 ../20261028-resume-30/INSTRUCTIONS.md，全约束仍适用。第一批全部文件冻结不可修改；只写本目录你自己的 task_id 子目录，新 .lean/REGISTRY.json/REPORT.md，不修改前任/生产文件、Git、看板，不编译、不修编译、不检查额度、不再派代理。

读TASKS.json明确单个下一步，并读第一批自己任务、独立reviews与邻近依赖。新任务必须消除实际对象绑定/证明义务，禁止把尚待证明的结论改为前提或交付无关泛引理。不能闭合则提供实质必要引理并保留全目标OPEN，task_complete必须按TASKS原完整目标口径，另用local_step_complete记录窄步骤。实际source-only导入需精确路径与SHA。

编译/内核和大型checker由用户专项处理。任何经典primitive复用要准确归属和接口，不另造原稿输出作为primitive。证明疑问先核原手稿；实现错误与原稿缺口分开。代码完成后发root及相应reviewer验收，等待后续工作。
