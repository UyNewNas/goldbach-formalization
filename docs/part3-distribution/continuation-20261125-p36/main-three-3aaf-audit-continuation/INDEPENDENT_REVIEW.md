# P1 三个主模块：独立组合证据验收

## 结论与范围

**通过本次独立验收，限固定提交 `3aafcd2464df9486f98788a657086db9d686b187` 的三个 owned 模块与 28 条完整声明。** 信用由父任务真实完成的 strict compile、官方 bundled leanchecker replay，与本次真实完成的完整声明审计共同组成。本次没有重编这三个模块，也没有重做 replay；原任务的 timeout 及 `COMPILED` 报告原样保留。

| 模块 | 定义 | 定理 | 完整声明数 |
| --- | ---: | ---: | ---: |
| `ImbalancedChen.P2ActualPairPlanRunSupport` | 1 | 6 | 7 |
| `ImbalancedChen.P5OriginalU5PhysicalRho` | 7 | 3 | 10 |
| `ImbalancedChen.P3OriginalU5PhysicalModulusCap` | 0 | 11 | 11 |

Cap 的 11 条包含 **六个公开定理和五个自动生成定理**。完整审计包含 `ImbalancedChen.P2OriginalLowerCompactStartCapConstructor.topCap.eq_1` 等在不同 namespace 下生成、实际 defining module 属于 Cap 的声明，未以 namespace 前缀筛选漏掉这些记录。

这不是整个 P3.6 的验收，也不授予 queued EXTRA 或任何 source-only 候选信用。common Q、PP/admission、whole-atom/tensor 与 density 供应的未完成义务仍维持原状态。

## 实际归档与传输

独立从 147 页无损输出重建 `[0, 4627683)`，核对连续偏移、每页长度及 binary frame。归档实际为 **4,559,760 B**，SHA-256：

`95c14de12928cf047491db283d098ce99de6a789e25b4074c00f154dabea986c`

原始完整 stdout SHA-256：

`d11c75f324b75bd110578d4870b502eb11ddbebf673e2c7903933200e749fbd3`

314 个成员的集合与外层 receipt 完全相同，逐个重算 SHA 全部相符；所有成员均为路径安全、唯一的普通文件。解压字节总量 24,738,455 B。没有依赖单独截断的显示输出作接受判断。嵌套 Tagged 旧证据包的 31 个成员也全部重新核 hash，并核对其源码和实际复制对象仍与旧 receipt 相同。

## 父阶段与续跑绑定

父任务 `job_345d68b9a44a4e33b6913f4e612cac72` 原终态仍为 `timed_out / -9`。固定父报告 SHA 为 `5e8ef35a629f17056b6daf1ce57605c887cc0ddb5e762976c17500d20c18f766`，原审计日志仅有 command，SHA 为 `ea7651df820ee185d32133c1485f76ac7e42bcb14cbcb1efc44f19dbc98b82cd`。

逐项核对三份源字节、三份实际对象、三条 `lean -t0 -j1 ... -DwarningAsError=true -o ...` 命令和三条官方 `leanchecker --verbose` 命令。原报告中六个阶段均 exit 0，原日志 hash 相符，replay 日志逐个含精确模块名。

| 模块简名 | 父任务 compile 秒 | 父任务 replay 秒 |
| --- | ---: | ---: |
| RunSupport | 6.776 | 10.659 |
| PhysicalRho | 6.343 | 8.307 |
| PhysicalModulusCap | 8.057 | 8.892 |

本次 `job_3f41695f60954734a1340a4fa4e96cba` 终态 `succeeded / 0`，只运行 audit，耗时 678.86 秒。实际 task command 中内嵌脚本和 Lean 源经静态解码后与归档逐字相同。脚本 SHA `f6a7b0a64bdad9d0d79c217fa20df5c9b2d902b1779fc22cde22668b889e78b3`；观测版 SHA `f33b70d44efc07ac15c5852f544570c8cf56e6038eccd9aab1b0c0f4f96ef67c`。去除 10 个 `P36_PROGRESS` 块后，精确恢复原审计 SHA `809eaabdbfa2546cf255bd6f9103f3623acb14e97acd365b75f8103b093529ec`。

## 源码、依赖、缓存与路径

独立将 SOURCE_SELECTION 的全部 261 份源码及 10 份配置/验证文件与固定 Git 对象逐字比较。重新计算报告所记录 9,892 个节点的递归签名，其中 256 个项目节点的 input key、依赖签名及对象 hash 全部一致。核对了 251 个普通本地 reuse 的 state 和原成功日志；这条路径没有接受未绑定依赖的 donor cache。

本父轮的项目动作准确为：251 个普通本地 reuse、4 个 compile、1 个以前已验收 Tagged receipt reuse。4 个 compile 包括三个 owned 目标和一个普通依赖 `P2OriginalPairBufferedRootProvenance`；本报告不把该依赖另算作 owned 验收。

绑定文件覆盖 37,744 个快照，含 27,708 个对象及 private/server sidecar hash。43 个 native alias 均限固定 goldbach `research/wu2008/src/` 对应路径。实际执行的冻结脚本在 audit 前后检查完整快照、完整 sidecar 集合、Lean 4.33 按顶级 namespace 首根解析的实际路径，以及 compiler、11 个 package pin 和 tracked-clean 条件。记录的前检查时间为 14:19:20.114197 UTC，后检查时间为 14:31:09.717957 UTC。

此处应准确区分证据来源：本独立审查对本地归档、源码、递归签名及执行程序作了重算核对；远端 before/after 文件检查由 hash 绑定且确实成功执行的 continuation 程序完成，本审查没有再次读取全部远端文件或重跑 Lean。当前 checker hash 也仅作为续跑时官方 checker 的快照记录，旧 replay 的信用来自保留的旧命令与日志。

## 完整类型、公理与实际结论

`declarations.json` 的 28 条记录与实际 audit log 的 `PART3_AUDIT_DECL` 逐条相同。模块计数和总计相符；全类型共 28,146 字符，无截断标记。逐项读取了六个公开 Cap 定理、其生成声明和另两个模块的完整类型。所有传递公理都在 `{propext, Classical.choice, Quot.sound}` 内；未变化的 Lean 程序还拒绝 unsafe/axiom 声明，并交叉比较 defining-module 环境清单与 legacy object 的完整 serialized `constNames`。

六条公开 Cap 定理的实际类型仍是原 literal `selectedPolicy ... false N t` 与同一 `rho`/整数 pushforward 的模数界，保留 `0 ≤ buffer ≤ 1/1000`、适用的 `attachmentNu * epsilon ≤ buffer`、`N ≥ 2`、pairSupport/非零入口等条件。最终整数 rho 定理还保留 `0 < epsilon < 1/8`，得到 `q < N^(599/1000)`。没有把 coefficient 或 policy 换成 rounded 输出，也没有把该模数界称为 PP/density 结论。

**未发现阻断验收的问题。** 完整来源、阶段日志 hash、工具 hash、每条声明的 type hash 与公理清单见同目录 `INDEPENDENT_REVIEW.json`；原完整类型仍在归档中的 `continuation/declarations.json`。
