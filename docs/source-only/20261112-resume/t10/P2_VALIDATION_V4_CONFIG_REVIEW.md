# P2 整数质量 R3 的远端配置独审

**静态配置复核通过。** 从唯一父提交 356c3782e9428098a2fcbfb18c689bef264d84fa 创建 ci/p2-integer-mass-r3-20261112 的拟议驱动共 26 路径、274854 字节。P2_VALIDATION_V4_SCOPED_CONFIG_ALLOWLIST.json 为 25441 字节，SHA256 bda1d144e29601f4e1b1ee1b219cd326798b75b19484e2aa56b40dac21d04830。

- 逐一读取两个固定提交中的全部 102 个源 blob。92 个源来自 eb035a259f2f40853e9899f6d98af25852184fee，10 个归为 abi 的源全部实际来自 32d541884c85748e3fb18f7a83801b2f8b16e359。同路径追溯至 51859a24c91580f885afd2a781dcb48b07177529 的四个 R2 后像及 8003 字节 ABI 均字节、SHA256、Git blob 相同；另五个后像各自符合 R3 独审批复。实际运行仍只需两个 source checkout。两个提交之间的五项继承来源证明 SHA256 为 958e2fcae82124d9b1375b5903412434244d9f5b25d9313515b4b9ab44a3a5a6。
- 从每个源解析直接 imports 后重新求得原次序的 101 个 ABI 自然闭包模块，再加独立 FinitePiIntegral，合计 102，项目实际源共 1246785 字节。没有遗漏原目标或原 import；配置三种原始输入及 data_include 空表与 v3 对齐。关键信息取自逐模块 records。manifest 内单数 overlay 描述 8003 字节 ABI 的原始路径。
- 对 v3 逐字比较工作流，只更换窄分支、bundle、source commit 和 manifest hash，全部 17 个步骤及参数保持。Python validator 只更换分支、bundle 两个字符串。stage、collector、守卫、工具链和故障诊断模板沿原字节。对每个模块均执行原编译与 bundled kernel 重放；执行前后比对源及 .olean 对象快照。完整 serialized 常量与环境归属名称严格相等，每个声明输出完整显式和 readable 类型以及 collectAxioms，继续拒绝未证公理、partial、unsafe、类型截断或非法传递公理。FinitePiIntegral 的旧问题在此新环境仍须实际通过。46eedd90… 的完整 diff/owner 诊断保留原 throw。独立 T01/Fine 的九个 floor 与两份公理输出不在这次 P2 验收范围。原实际运行状态、资源和失败后研判所需证据留存步骤均保留。
- 独立通过父 Git 树读取全部 7 个原 workflow 及 before/after 指纹。6 个完全相同；VE 只添加这一分支到 push.branches-ignore。新增工作流要求此精确分支且 .github/workflows/p2-integer-mass-validation.yml 自身改变，goldbach-p0-heavy 的 cancel-in-progress 仍为 false。实际 checkout 后将按自身 commit、直接父、根选择及八个 workflow 的完整字节绑定。外置选择仅在 verification/parts/p0/P2_INTEGER_MASS_DRIVER_SELECTION.json 安装，独立于 bundle registry 的自哈希。
- 作者最初冻结的注册表保留三条 v3 路由说明。最终注册表已修正字段并记录实际失败作业。正式最终 REGISTRY 为 b3943e6fea3defa4b5f2c4e8aae496ebcd553ef4c652ef17636b41772eb4ac57，manifest 为 0a7790ab937c3ab85bb12a658522e23fe1ff84e00acb059585d118486c5492ba，629 字节的外置选择为 99c2372f9ee5bcaced9213c86bf5d6873852a97bc24b85b02ba2444d434ca7a8。

本次只核准上述未来驱动的固定字节。实际提交树、运行结果、cache 可恢复性及数学绿色节点仍各需自己的运行证据。

