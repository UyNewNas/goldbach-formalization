# P1 供应依赖：P2 Winner9 数值 Block01 已有验收证据

**Block01 在 P2 私有环境中已完成 normal 编译、独立 `leanchecker` 重放和完整 owned-declaration 审计：17 个模块、545 个 owned declarations、256 个原始行。** 与此前已验 Block00 合并，数值覆盖恰为 Pages0000–0031、两个 block aggregator、512 行（零起编号 0–511）。

本目录复用既有源码、编译结果和导出档案。整理期间没有调用 Lean、重放内核、增加数值证书、改 checker 或启动云任务。P1 联合环境的导入与终端验收仍须由 P1 主流程记录；本证据包不把 P2 私有验收提升为 P1 全链完成。

## 精确验收范围

| 范围 | 数值页面 | 聚合模块 | 原始行 | owned declarations |
| --- | --- | --- | ---: | ---: |
| 已有 Block00，直接复用 | 0000–0015 | `P2Winner9NumericalCheck00` | 256（0–255） | 545 |
| 本批 Block01 | 0016–0031 | `P2Winner9NumericalCheck01` | 256（256–511） | 545 |
| 两批并集 | 0000–0031 | 2 个 | **512** | **1,090** |

每页 16 行、34 个 owned declarations；每个 aggregator 1 个 owned declaration。结合原导出中的逐页 ordinal binding 验证了行区间无交叠、无缺口。11026 行全集及之后的页面不在本次结论内。

机器可读结果和逐模块源/object/receipt SHA 见 [RESULT.json](RESULT.json)。

## 源码与发布绑定

Block01 的 17 份目标源码与公开提交 [a5a42f8f70418a7b2b8a378713911e829786ec8b](https://github.com/UyNewNas/goldbach-formalization/commit/a5a42f8f70418a7b2b8a378713911e829786ec8b) 的 `docs/source-only/20261124-p2-winner9/ImbalancedChen/` 字节完全一致，逐文件 Git blob 与 SHA-256 见 [SOURCE_PUBLICATION_BINDING.json](SOURCE_PUBLICATION_BINDING.json)。

完整项目依赖闭包为 **74 个模块**。其中 72 份源字节在上述提交中有精确对应；已验稳定版 `P2Winner9RowArithmeticChecker` 与 `P2Winner9SelectedArchiveChecker` 的源字节位于后继公开提交 [0f87651d2f27a6de1900b717b8703f2c6cbcb0ae](https://github.com/UyNewNas/goldbach-formalization/commit/0f87651d2f27a6de1900b717b8703f2c6cbcb0ae)。两个提交的远程存在及 tree 已通过 GitHub API 确认，原响应保存在任务证据压缩档中。完整源绑定见 [DEPENDENCY_PUBLISHED_SOURCES.json](DEPENDENCY_PUBLISHED_SOURCES.json)。

编译器为 Lean `4.33.0-rc1`，Mathlib pin 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。原工具、对象、递归依赖签名及继承的历史 provenance 见 [DEPENDENCY_BINDINGS.json](DEPENDENCY_BINDINGS.json)。继承的 baseline 记录保留原信用，整理操作没有产生新的编译信用。

## 原始执行记录

| 已有任务 | 实际结果与复用范围 |
| --- | --- |
| `b7039f3f188b4b4ea9c214097bbdf401` | 完成 Pages0016–0021；退出 2 表示原 driver 的分段时间预算暂停，`failed_or_blocked=[]`。 |
| 既有后续 normal 回执 | 在续作前的实际 preflight 中，Pages0016–0028 均已有源/object 绑定有效记录；直接复用。 |
| `c6e528abc2984ffb8c1571f635fd2125` | 退出 0，202.113 秒；仅新编 Pages0029–0031 及 Check01；闭包复用 70 个，新增 4 个，pending 为空。 |
| `eaf64cad17f14acabd5cb1f7d540d313` | 退出 0，873.048 秒；独立内核及 full-owned 审计 Pages0016–0028，共 442 个 owned declarations。 |
| `3a5f35ce413f49c8a1fc138a17f65246` | 退出 0，207.685 秒；独立内核及 full-owned 审计 Pages0029–0031 和 Check01，共 103 个 owned declarations；两独占 lane 均退出 0。 |

原 normal driver SHA 为 `df9949270753bb36cace92d70099de4a7c30dcea8f761ade36ecd03f50c5684d`；Block01 原审计 driver SHA 为 `b214fe826d40f96c9907cb9c42f0ac96dcc9bc48dc080a264c9c13de2b43cc08`。对应不可变工具字节在档案中保留，后来新增的工具版本没有替换本批原始 provenance。

## 证据文件

| 文件 | 内容 |
| --- | --- |
| [evidence-numerical16-31-20261124.slim.tar.xz](evidence-numerical16-31-20261124.slim.tar.xz) | 435,268 字节；17 份完整原审计回执、normal registry/日志、独立 replay 日志、full-owned 日志、完整类型与声明清单、原工具及输入快照。原导出 manifest SHA 为 `b726b3acbac0402f7c1d5bdcf82412da1429b204c3d5afbe333b199c10252dd1`。 |
| [evidence-checkpoint-20261124.slim.tar.xz](evidence-checkpoint-20261124.slim.tar.xz) | 569,980 字节；此前已发布的完整原档，原样复用以支撑 Block00 和相关历史依赖。它保留更宽的 126 模块历史证据；本目录的 512 行合计只计入其中的 Block00 数值模块。 |
| [task-and-publication-evidence.tar.xz](task-and-publication-evidence.tar.xz) | 本批原任务元数据、完整已有 stdout、preflight、命令文本、原分类记录及 GitHub 发布响应，逐文件校验见 [TASK_EVIDENCE_INDEX.json](TASK_EVIDENCE_INDEX.json)。 |

两个主要档案沿用现成 slim 导出，保持全部非源码成员的原始字节；已有公开源码用长度与 SHA 引用，未替换的源码 payload 继续内嵌。没有分发或采用无来源 object 缓存。必要 object SHA 保留于回执，不需要把编译二进制纳入 Git。

`SLIM_MANIFEST.json` 可定位档案内每个原始成员；每份 `selected-receipt.json` 绑定对应的 `replay.log`、`audit.log`、`declarations.json`、`types.txt` 和生成的 `Audit.lean`。检查过全部 34 个目标模块：所有 replay/audit exit code 为 0，声明名无重复，所有 `axiom`、`unsafe`、`partial` 标志为 false；传递公理均限于 `propext`、`Classical.choice`、`Quot.sound`。

## 整理后的字节核验

现成导出 verifier 的原字节另存为 [verify_original_export.py](verify_original_export.py)，SHA 为 `bf20e2992d7f798b3bf5b00d054b56503796ff29822e1bb8ae03bff4b166cb5b`。它已验证档案成员、原 manifest 与所有省略源码的 SHA/长度绑定：结果见 [BYTE_VERIFICATION_PRIOR.json](BYTE_VERIFICATION_PRIOR.json) 和 [BYTE_VERIFICATION_BLOCK01.json](BYTE_VERIFICATION_BLOCK01.json)。Block00 直接对不可变 Git tree 验证；Block01 的现成 source catalog 对源工作树验证，并另由 `DEPENDENCY_PUBLISHED_SOURCES.json` 逐项绑定全部 74 份已提交源码。

在本目录运行 `sha256sum -c SHA256SUMS` 可验证交付文件。以上均为证据完整性核验，不是新一轮数学证明、编译或内核验收。
