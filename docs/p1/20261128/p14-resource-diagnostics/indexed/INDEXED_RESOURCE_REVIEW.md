# IndexedOwnerArchive：完整 partial log 与资源中断审查

## 结论

当前保持 **未完成、零验收 credit**。原任务的 `memory_exceeded / exit -9` 是父代理提供的运行结果；本次独占只读任务成功读取了全部 2 页、34415 字节 transport 至 EOF，并逐份核对原文件长度与 SHA-256。完整 normal 日志没有目标声明名、Lean `error:`、Built 或正常结束记录，因此没有行级证据支持某个证明改写。

## 可复核事实

- 原任务：`job_25b5b644a3a94fb3baca594930540942`。父代理报告 90.780 秒、peak 23633944576 B、22528 MiB；这些指标不冒充本次独立读取的原任务 metadata。
- 专属读取：`job_63fe03b5febd4bcaaed812b19b7374f0`。完整 stdout SHA-256 `c7c9fb54d3bd248705990d4acbc6390ab8952c642ce139a21fb44928aef1ff66`。
- normal.log：197994 B，SHA-256 `f5abbec123516731f42ee1112d176cf363456b4cb8d5ecd253e442e49c07b21b`，2743 行；只有 124 条依赖 Replayed，0 条 Built，0 个目标模块名，0 个 `error:`。
- directdeps 原 `--no-build` 退出 0，actual_built_modules 为空。target-ready 原 `--no-build` 退出 3，仅目标未 ready，且没有编译任何模块。
- `SOURCE_INSTALL.json` 是 `ALREADY_AFTER_NOOP`，mutated=false。恢复的原源码与当前仓库逐字节相同：11489 B，SHA-256 `e729c1e6b3ac170786550d52e6f5982969f30814c43bc13e773311737fdfb58f`。
- 原 normal-command、单 stage RESULT 和 pipeline RESULT 在所请求路径均不存在，不能补造完成记录。读取的 BINDING 路径位于 runs/attempt-00001；原 run_stage 通常在 stage/source 根写 BINDING，所以该位置的缺失不证明根 BINDING 缺失。

## 稿件与已有工作的边界

已复用本地冻结 1106 全文 `references__numerical-appendix.tex`：42662 B，SHA-256 `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`。277–284 行要求 292633 个父区域、18728512 个子区域和完整子和；505–512 行要求 cap、branch、parent 联合固定，同时允许只积分非负增益的子集。这支持现源码保留完整原索引和显式 residual/missing 分区的范围；它没有把某个资源中断转化为证明缺口。

已验收 Shape 源 SHA-256 `8e13f914299d71a288833cb751b60e437d0cdc61e6183865cc0ba6a9de01fd7c`，其 624–626 行给出 `rows_toList_length`。Indexed 的 31–32 行已经直接使用该定理，不再重做 card，也不重编 Shape。

## 静态候选，不是已定位原因

| 原源码边界 | 可核实表达 | 证据限制 |
|---|---|---|
| 1–4 | 大表、Shape、AdoptedOwnerBank、Mathlib 导入 | 日志不能证明已进入第一条声明；导入本身也需区分 |
| 26–35 | `ArchiveIndex := Fin rows.toList.length`；`archiveRow` 的 getElem；成员关系 | 闭表长度进入类型，可能涉及 definitional conversion；未证明发生了大表展开 |
| 78–87 | `List.mem_iff_get` 与 `archiveRow` 的索引表示对接 | 可能需要 List.get/getElem 类型转换；尚无耗时或失败定位 |
| 53–66 | `Finset.univ`、filter、sdiff 的符号成员证明 | 没有显式遍历所有行的决定式证明，只是较弱候选 |
| 107–117 | `simp only [sourceOwnerRow, FifthRow.mk.injEq] at *` | 没有显式展开 `rows`；不能据此认定 simp 是原因 |

## 最小下一步：一次有定位能力的诊断

先核对**现用 Lean runtime**已经支持的 frontend profile/trace API及异步完成语义，再准备一次独立 scratch 诊断。至少采集导入完成、上述 26–35、78–87、107–117 边界与 RSS；保持所有原声明、命题和证明字节不变，保留原 serializer、guard、toolchain 和资源上限，复用全部已编译依赖。普通 BEGIN/END 标记只能说明主前端经过了某处，不能当作异步证明已完成；未核对的 profiler 选项不应直接运行。

这一步只用于找具体边界，不能生成 normal/kernel/full-owned 验收，也不能改变节点状态。获得实际定位后再选择单个最小表达修复；当前没有依据增加内存、修改 ArchiveIndex 定义、重做 card 或盲目改 simp。

分类：**资源中断已知；形式化表达错误未知；可补齐的省略推导及实质数学缺口均未由本证据展示。** 本轮没有远程编译、任务提交、仓库编辑或 Git 操作。
