# Y18 内核验收配置独审

冻结包的**静态配置通过**。36 个文件共 6,445,547 字节；作者 REGISTRY 的 SHA-256 为 `ad2f974d49c24296cd2f7fd079d78e60c56dcc5aa96180064b1ef4289b8f7568`，Y18_MANIFEST 为 `8c48f34f4479b13cb38749360df78ed06f1d80ddee646472579ad0f1e214a496`，作者 ALLOWLIST 为 `2b7308a2b02083677347439152249601652e972af8298472f00f3b181d5edd6c`。逐文件核对了实际字节数、SHA-256、原始 Git blob SHA-1，并核对 manifest 支持文件、registry 和作者 allowlist 各自的完整文件集合。本次结果供根制作并另审实际不可变 driver 使用。

## 数学来源和验收范围

从本地固定 Git 对象重新读取 f1bcf37 的 335 份历史源和 794fe55 的两份 Y18 原源。按 T15 的原文件行号独立删除 `List.mem_cons_self` 的两个旧显式参数，在内存逐行得到 12 份预期 SHA 的 13 个替换；再与作者变换逐字节比较。三个直接历史进口及两个目标完整可达。选源与 P2r2 交集为 28 份且逐份 SHA 相同，与已验 Stored 000–030 加父类型的 32 个模块交集为零。

原生 Git 09b97db 的 38 个直接根进入 1,348 份实际可达源码。其中 460 份仅在原研究档有源，888 份取原包标准位置。核对了全部 61 份双版本的原路径和 blob、T15/T16 的六个原生产者锚点、两项双版本直接 API 及其实际调用。两个直接 API 的所用声明类型在两文本中一致，原四库配置选择标准位置，另追加七个原进口实际需要的裸名库，不替换标准库源码。总共 1,685 个可达源。460 份研究文件和 337 份项目文件各自执行完整声明核对；888 份作为原库依赖，每一份需有真实源码、编译、setup、输出及实际消费记录。单纯重导出的标准聚合模块按依赖登记。

797 个数学模块的完整所有权/声明审计和这 797 个模块加一个已生成的 CandidateAudit 的 798 次内核重放，均属待执行的通过要求。另对两份原目标中的 17 个确切定理逐条核原定义模块、定理种类、展开与可读类型，以及传递公理与独立 `#print axioms` 的相等性。17 项均匹配 794fe55 原源和先前独审给出的原行。整个 Y18 的源码蓝色结论已在前次独审给出。

## 所有权、历史失败和运行材料

逐段比对了原 P2v3 Round6Audit。保留以结构化 Lean Name 排序逐重数核比较的硬门；包括私有、生成和公开常量，额外生成的无 kernel ConstantInfo 名单单独记数。完整定义模块、重复与缺失、两种完整类型、unsafe/partial/本地公理和传递公理检查均在。仅许可 propext、Classical.choice、Quot.sound。原 P4 运行 43108198136 的 batch-checker.log 第 78 行已重放 FinitePiIntegral，batch-types.log 第 72 行仍因 serialized 与 owner 不符而抛错。Y18 这份输入 SHA 为 `22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c`；旧日志未给冲突名。现配置在原抛错前输出含模块、名字、重数及索引的诊断并 flush。实际执行存在再次遇到该错的可能。

原 P2v3 runtime guard 和诊断模板均通过逐字节对照。项目的 maxRecDepth 与 maxHeartbeats 为 100000 和 4000000，原生库沿用原包参数，审计包装器显式使用项目限值与 warningAsError。Lean 实际参数归一化为 trust 0、两线程和 12288 MiB，原有串行编译锁、原生 checker、工具链版本与运行二进制 SHA 均在合同内。外部锁包括 LeanArchitect 原版本。每个源均需由已锁定的配置、真实的命令输入与输出、实物 setup 和本次编译记录相连。

复核了修订后的终端。所有项目与原生模块在 setup 中实际使用的已选直接或传递 import facet 都须逐路径、SHA 和字节数联回对应模块的规范输出。项目源根额外裸名可加载文件会触发拒绝。手工 wrapper、checker 和最后 audit 在实际同一 lake env 中，记录有序 LEAN_PATH 并检查首个可见的 public olean；在受检绝对可执行文件运行前后重新核对全组对象和工具，再与终端 checkpoint 中逐文件 SHA 和字节数相连。允许的运行根在本次没有受认可的旧项目或原生对象缓存。

捕获器保留真实 setup、olean、ilean、trace、本次生成的 IR/C、object、库与链接产物，保存所用依赖和 ABI 标识，并在进一步验证之前写入逐路径对象日志。已产出的局部对象和出错日志可单独隔离。手工 wrapper 触发的严格审计若提前失败，就没有完整 wrapper 产物；此时不可能取得 798 完整重放收据。失败留存、始终上传和总收据必须由实际工作流兑现。

## 待独审的实际 driver

这份批准不含任何 workflow 或提交。实际 driver 需要把外置选择、提交与父提交、完整 workflow 清单、候选全套字节及运行条件绑定到真实 checkout，复核近期 P2/R3 如有的同源失败或修改，并保留原并发组、失败日志和 checkpoint 产物。候选配置明确要求每份原生源都有真实编译记录。根的下一次独审以实际 driver/payload 为对象。未执行 Lean、Lake、checker、LSP、stage、guard、producer、Git 写操作或 CI；本次没有 Y18 内核、缓存/ABI 恢复、全 PP 或 K 的验收结果。

可复核数据在同目录 SOURCE_AUDIT.json、REVIEW_BASES.json、NATIVE_SOURCE_CHOICES.json 和 GOLDBACH_ROOT_FIRST_COMPLETE_GRAPH.json，逐文件冻结清单在 ALLOWLIST.json。
