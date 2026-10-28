# lower_functional 第二批交付

新增 `P2N48ActualGeometricKeyDecoder.lean`，186 行，完整闭合源码，未编译、未执行 finite checker、零正式信用。第一批及原始 archive 均未改动。

本次核对原始 `certify_sharp_248_four_min.py` 的 `rectangles` 和独立 replay 的 `keys`：先列全部 249900 条 U10，再按 ix 分块列 U11；每个 ix 含 19600 条 `(iw,iz,iy)` 升序允许重复三元组，再反转存为 `(iy,iz,iw)`。因而实际 high row 的零基 source ordinal 为

`249900 + 19600*ix + Σ(w<iw) choose(49-w,2) + Σ(iw≤z<iz)(48-z) + (iy-iz)`。

源码给出两个封闭 `decide +kernel` 命令，分别验证冻结 `rawSelectedRows` 每条记录的 term、弱序和上述 decoder 等式，以及相邻 original ordinal 的严格递增。**命令只写出，没有执行；目前不能声称实际数据检查成功。** 相邻检查仅线性遍历行表，后续用纯证明的传递性推出全体 ordinal 注入。

关键逻辑不是单凭 ordinal 不重：同一 geometric key 先经实际 decoder 等式推出同一 original ordinal，再经严格 source-order 注入推出同一完整 SourceRow。随后 actual method-zero/非priority crop 通过原 `actualRetainedRows_policy` 继承 key 注入。这样第一批整体真实 U10/U11 coefficient 的行成本加未覆盖余项恒等式，以及当前 K 的逐行 recost 上界，可在源码中去掉 `hkeys` 形式参数。

本轮的 closed source 消除了一个外加 ownership 前提；其形式成立仍须用户编译/内核执行两项实际 finite checks。若大表 reduction 需要分块，由编译专员处理，本轮未试运行或做编译修补。`hMass`、原 switched/Q80 row 上界及 `uncoveredCost` 的完整补集认证仍未闭合，因此原完整 lower_functional 任务继续 OPEN，`task_complete=false`；`local_step_complete=true` 仅指这一 decoder 证明源码已写全。

原稿第 897–905、1354–1362 行要求真实共同分区与完整负域，本实现遵守该边界。没有新增原稿数学缺口，也未把 selected method-zero crop 当成完整覆盖。精确 source/import/producer SHA 见 REGISTRY。
