# P1.5：原 dyadic 常量的明确名称修复

本目录保存 D 的实际失败记录、五份原源码的最小名称修复，以及精确保全后部署的入口。**源码发布、部署成功和 Lean 验收分别记录；本目录的静态核验不增加编译信用。** P1.5 整体尚未关闭。

## 实际失败与修复范围

D 是 `7ca00b5fcc24e188a53d3a645808d388a5b9e6d1`。任务 `job_7292274bc17b4af7b07b528d872e02b9` 运行 65.1786 秒后 exit 1。它没有接受新的 owner：HBWitnesses 的 normal 编译失败，Cutoff 尚未尝试。八个既有供应 owner 仅按原来源和完整回执重新核验，没有重新编译。

C 的局部 `R` notation 消除了原名称歧义，但真实 D 编译发现该 notation 也影响了结构字段 `R := …` 的解析，以及 `dsimp [N, R]` 中应当作为定义名使用的 identifier。五条诊断中的字段缺失和未完成目标包含这两处错误的后续影响。此处的修复分类是 Lean 解析与名称展开；没有据此宣称存在数学证明缺口。

HBWitnesses 删除这条局部 notation，把九处真正的 dyadic 常量引用明确写为 `ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition.R`，保留字段名 `R`。另外四份已审的后续源码共有十八处同一常量引用，也作直接限定；PerGroup 的 `unfold hbCap R` 使用明确的 identifier。没有新增 notation、声明或假设，没有改变 imports、证明步骤或估计。

`REPAIR_MANIFEST.json` 保存五个前像、后像及全部 28 处精确字节 splice：27 个引用限定，以及一条 notation 的删除。其余 355 份当前固定源码保持 D 原字节。旧 B、C、D 的记录不被改写。

## 有界只读观测

`collect_original_D_failure.py` 是实际执行的固定 collector 原字节。任务 `job_727544538bbe4829a237fe3449e9ea0a` exit 0，输出 16963 B，已经读到 EOF 且无截断。它只读固定失败记录、指定模块的 artifact 指纹和已固定的 157 源码清单；没有调用 future preflight、Lean 或 kernel。

`ACTUAL_D_METADATA.json` 保留了十八项原记录的指纹、两个目标各 21 项 artifact 状态、五段有界源码诊断以及后续源码的存在状态。完整私有 owned types、原 archive 和生成文件内容均保留在 P1；没有导出。

HB 的唯一残留产物是已经观察到的 `.setup.json`，6328085 B，SHA-256 为 `99cad186ff4aa90dee75dfed9f9c858d4ee2f518f49d1903ef353d5ef181dd3a`。Cutoff 的 21 项产物均不存在，两个目标都没有 `NORMAL_PASS`。

后续十五目标的闭包共 157 项：150 份源码精确匹配，7 份缺失均属于待安装目标，没有固定依赖缺失或源码不符。在本次四个后续名称修复中，Licensed、PerGroup、AllK 三份源码已经存在，都是已检查的 D 前像，且各自 21 项产物均为空；AtlasRough 的源码和 21 项产物都不存在。

## 部署的精确顺序

入口为 `apply_source_repair.py --source-commit <本次发布的完整 commit> --check` 或 `--apply`。它不编译。

1. 从固定 D manifest 校验原 360 源码图，实际首对闭包仍为 68，依赖仍为 66；用原 API 验证八个供应 owner 的完整原审计及固定依赖。此时仅核对那个已经观察到的失败 setup，尚不调用要求目标产物全空的完整 preflight。
2. 单独执行未经修改的原 Support B 只读 collector，要求输出逐字等于已发布的 1894 B 摘要。其 109 源码闭包、完整 normal/owned 审计和原 B 身份保持不变。两个检查的来源并集是 130；加上固定目标的 artifact 保全清单，共观察 148 个模块。编译选中闭包仍为 68。
3. 在原 lane 0 内，按原 C 的四个 archive 函数逐字保全唯一失败 setup：独占创建私有备份、`fsync`、校验完整字节和 inode/mtime，再移除这个固定生成文件。没有一般性缓存清理或 fresh gate 例外。
4. 产物真实为空后，调用未经修改的完整 D preflight。HB、Cutoff 必须通过原 21 项 fresh 检查；四个后续修复目标也通过原 fresh gate。若任一状态不符，入口 HOLD，不进入源码写入。
5. 调用原 `h.install_sources`，只更新已经存在的四份精确前像：HB、Licensed、PerGroup、AllK，并保留完整源备份。AtlasRough 继续保持缺失，后续由原 additive installer 安装。
6. 比较全部观察源码、artifact、两份独立上下文、原 D 失败记录和两个 Support B 证据目录。只有四份已登记源码和唯一已归档 setup 的活动位置可以改变。旧 Git 状态、配置、runtime、guard 和原回执均须保持。

入口不能接受已经改过或已经通过编译的 HB 后像作为新的前像。未知、部分完成或并发变化的状态均 HOLD；不自动覆盖，也不重复编译已有验收工作。

## 随后的编译身份

本发布保留 D 的 runner、manifest、installer 和 verifier 原字节。后续 F 另行锚定这五份明确名称的源码；Support 的 normal/kernel/owned 回执继续属于 B，公开摘要继续属于 C。F 第一批仍只选 HBWitnesses、Cutoff。只有真实 normal 加完整 named-kernel/owned 审计通过后，才登记新的接受结果。

`STATIC_REVIEW.json` 是这份部署候选的静态来源核验，不是 Lean 通过回执。与本提交一起发布的 LongComplement 数学桥也另列为 source-only；不把其静态审查计入本目录编译结果。
