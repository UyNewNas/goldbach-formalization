# P2 v5 前置审计及完整 102 模块配置独审

**限定配置通过静态审查，待 GitHub 实际执行。** 以原父提交 356c3782e9428098a2fcbfb18c689bef264d84fa 为基准，拟安装的 30 个路径共 275471 字节。独立按 Git 树序列化规则在内存重建的根树为 848f85cfb09f030b278d5d916711c487144c9eca。标准清单 P2_VALIDATION_V5_SCOPED_CONFIG_ALLOWLIST.json 为 23036 字节，SHA-256 5dc7022819ee91bed92baab4a58544cb785d448fe474b31c7646ce11cdd8e0d3。此结论未运行本地证明、安装、守卫、工作流或归档程序。

**数学选本。** 从两个固定 Git 提交读取所有选中源，复核每份实际字节、大小及原始 blob。88 份来自 eb035a259f2f40853e9899f6d98af25852184fee，14 份来自 e6874f0fadb15515e5363ce92d57b73079425283，后者含 4 份已独审的 r4、5 份 r3、4 份 r2 及原 8003 字节 ABI。旧 10 个路径与 32d541884c85748e3fb18f7a83801b2f8b16e359 的相应 Git 对象逐字相等。从实际文件重新提取直接导入，独立求得顺序相同的 101 模块 ABI 闭包，再加入专门审量的 FinitePiIntegral。合计 1247606 字节，45 个外部直接导入名。原配置文件、数据输入和两个验收分组的模块清单保持。

**前置 FinitePi。** 原 prepare 的完整 102 个命名模块渲染分支逐行留存，同一函数同时产生完整 exporter 和仅含 FinitePiIntegral 的 exporter。运行时还会比较完整输出与原渲染结果。两个 exporter 都使用已审 SHA-256 46eedd90437fae00921f2a5a6a39abb5996125f45033b230c17d1403d16eec95 的 Round6Audit，原含重数的名称排序比较、失败诊断、flush 及 throw 均保留。同一项目、同一 guard 下先以 Lake 构建 FinitePi，然后运行单模块 exporter。前置记录绑定实际源、olean、两个 exporter、独立 build/types 日志、manifest、registry、run/attempt/job 和 driver。独立解析器要求一份非空 legacy SERIALIZED，owned/serialized/逐 DECL 重数精确相符，每个声明原两种完整类型和传递公理、三类声明安全状态、模块计数及总计一致。若 Lean 本身失败，pipefail 中止正常通路，原差异 JSON 和真实退出码留在作业证据中。

**全量门控。** 前置 receipt 既在完整 build 前复验，也在最终验收重算。单模块环境通过只会放行完整流程。完整环境依旧重放 102 个模块与原 102 模块实际归属清单，执行全声明双类型及 collectAxioms、前后 source/olean 快照比较、实际运行守卫、按源及配置绑定的最终验收。审核器仍只接受 propext、Classical.choice、Quot.sound。额外导入可能改变同名声明的规范归属，完整环境仍须独立通过。旧 P4 的 146 模块环境和 Y18 均不在所授范围内。

**失败证据。** YAML 19 个步骤中，独立的轻量证据上传在 always 运行时审计之后、大对象压缩之前使用 always()。它包括当时已经产生的顶层日志、JSON、文本、两个 exporter 和 runtime 目录。初筛失败后不会出现有效的 pilot acceptance。全 build 若失败，后续 kernel/types 步骤跳过。原完整对象压缩与最终 always 上传继续执行，完整验收仍要求所有原门。早期轻量包由当时已经存在的证据组成，最终的重归档及验收回执由最后的完整包保留。跨 run 可恢复数学对象本次为零。

**发布身份。** 26 个 bundle 文件、registry 及外置选择均已逐字回验。bundle 之外另装新增 workflow、仅增一行排除的 VariableEnvelope workflow 及外置选择，共 30 路径。原父提交的六个其他 workflow 未变，检查了七条 push 的分支过滤。新工作流只允许 ci/p2-integer-mass-r4-20261112 上自身 workflow 路径变化，原 heavy group 与 cancel-in-progress=false 继续生效。实际 checkout 后仍要绑定直接父、精确安装的八份 workflow 和外置选择。最终 REGISTRY 为 33d79da8decbd26860037441e511db27da16b9845b2c582897322c967d09de67，manifest 为 2c81eccdac19920af512db18088d0b2e562b960234404ed5ea713325ded8c8ff，外置选择为 805b20fe4af768086569c34241d9de1ea0a5040b40a97934259cf17b7638b6bb。
