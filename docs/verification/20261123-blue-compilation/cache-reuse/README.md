最初的 portable-facet 安装器遗漏了归档中的生成 `.c` 和 `.c.hash`。固定版本的 Lake 需要 `.c` 才能认定模块产物齐备，因此部分本可复用的依赖发生了重复编译。修正过程恢复真实归档辅助文件，并保留原安装 receipt 的历史状态。

| 工程 | 恢复组数 | C/hash 文件数 | 物理导入身份不符而跳过 |
| --- | ---: | ---: | ---: |
| P6 | 89 | 178 | 35 |
| Member | 15 | 30 | 30 |
| Prototype | 11 | 22 | 8 |

来源为已鉴别的既有 GitHub 构建归档。安装前核对源码、选项、Lean runtime、实际导入产物与 payload 的 SHA；原源码、证明产物、IR、trace、manifest、receipt 与 guard 均未改动。原 trace 的 synthetic 标记和预期哈希保持原样。检测到的运行或排队源码被跳过，安装采用缺失文件名的原子无覆盖链接，并在登记的 owner 窗口执行；helper 自身不持全局编译器锁。

实际 stock 验证对同一个 `FiniteFibres:leanArts` 目标由退出 3 变为退出 0，前后原 source/proof/trace 与 depHash 均不变，新增源码或 native 编译调用为 0。元数据 `--githash` 查询单独计数。原始记录为 [before.json](before.json) 和 [after.json](after.json)。恢复辅助文件的数量与各证明模块的验收分别记录。

[SUMMARY.json](SUMMARY.json) 保存原 zip、原资格记录、执行 helper、partial 恢复、Architect supplement 和完整本地记录的身份摘要。[PUBLISHED_FILES.json](PUBLISHED_FILES.json) 将原路径映射到本目录的逐字节副本。[INDEPENDENT_REVIEW.json](INDEPENDENT_REVIEW.json) 保存独立只读复核的范围。

三个 `executed_*.py` 文件是本轮实际执行源码的原样快照，保留其固定工作路径和登记输入。它们用于核对执行记录；复用时需要准备对应的原始归档、选源、资格 manifest 和工程目录。
