# Stored031–041 终态验收

允许把原 Stored000–030 这一绿叶扩至 Stored000–041。新增 11 个原块、45056 行，sourceIndex 区间为 [126976, 172032)，累积覆盖原 42 块的 [0, 172032)。绿叶计数增量为零。此验收仅覆盖原 literal rows、每块 rows.size = 4096，以及逐个 Fin rows.size 元素的 sourceIndex 等于该块起点加局部下标。[本次 GitHub Actions](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43342877411)

## 来源与实物

run 43342877411，attempt 1，job 131615167793，实际 head `e94213659a5a01a3790baf41a8d49610cf9793aa`，直接父 `5667c944d301707beac811189e12939760f3f499`，根树 `cd3ede7b68a53312b90fb620049bba2510f51e02`。重读 Git 对象与此前独立范围清单相符。实际证明步骤均报 success。按交付方单次取得的原 ZIP 逐件审核，artifact ID 14009233352，80224048 字节，SHA-256 `38fd77a23829da47ae25d2f5b1de05be80f660a7913f973b0dc83e1d88c19947`，与 GitHub 摘要相同。全部 62 个成员的解压长度、CRC 和 SHA-256 逐件复算，展开共 332124741 字节。没有触发新运行或本地 Lean 执行。

## 数学范围与完整核验

- 11 份实际生成源共 2711511 字节，都与三份树已核的原始输入和冻结的单项修复后像逐行对应。原输入合计 2439360 字节，生成收据的来源、实际起点、大小和前后散列逐块比对。逐个源和已序列化名录均有准确编号 0 至 63 的 64 个 Fin 64 私有分量，合计 704。父源沿用已验的 470 字节输入。
- 构建日志和原守卫都记录父及新 11 块的源码编译。每次的输入源、olean、ilean、C、setup、JSON 输出、trust 0、2 threads、12288 MiB、两个原 D 参数和真正的编译槽所有者逐项核实。12 套留存源、olean 和 sidecar 的实际 SHA 全部对应 replay 前快照；原 verifier 在导出后再次比较快照。source/environment/serialized 的完整审计脚本，与上批已验程序只差实际目标编号。三处 package/toolchain 配置、依赖收据及安装日志也匹配已验基线。
- Bundled leanchecker 的实际 replay 名录恰为 12 个目标，每个出现一次。当前父 27 项，每个新块 260 项，共 2887 个全局唯一声明。逐模块核过 serialized、环境所属和单项记录三份名录的重数、所属模块和总计。每个声明均有两份未截断类型，无 unsafe、partial 或新 axiom。传递公理清单观测到 propext 2841 次、Quot.sound 2838 次。每块 rows、rows_size、source_index_at 的完整及可读类型和传递公理，与已验 Block020 模板按实际模块名和起点逐字对应；父的全部 27 条声明与上批导出逐字段相同。
- 原 runtime guard 为 `837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877`。真实 probe 通过，实际 51 个 compiler 命令、24 个 source 命令；运行时审计引用的 state 和命令记录 SHA 分别为 `9aefdb4ebb8855c0ef8fcca6a41859c76c97eb54d316186f42f3cc0c866a6d81` 和 `d06ad9ab0e3f2abd2fc6cccbe1abba14490b24d8d26de20957505af33e3afb4f`。这些摘要与归档成员相同。

## 父与旧块

标准依赖缓存日志显示 8679 个文件解压。项目父模块直接由 Lean 编译，build 日志记为 631 毫秒，所得父 olean 为 119440 字节，SHA-256 `5279a69ca840610060458af722024d79af001be859eb1f8efc78d7c15ae7c2af`；其 16 字节 sidecar 同样匹配已验 020–030 产物。这次对父的编译及重放不增加证明计数。旧 000–030 源的实际编译数和 kernel 重放数均为零，以原已验实物承接。剩余 30 块、整 72 块、typed/geometry 143、Q80、积分及整个 T01 均在范围外。

逐件 CRC、散列、实际编译命令、12 项 replay 和逐块公开声明的原始类型保存在同目录 `STORED_031_041_TERMINAL_ACCEPTANCE.json`，101647 字节，SHA-256 `5bb48ff14b7486f9f9276b5264629b4e62d981e1e6e109be06074e19112c22fd`。
