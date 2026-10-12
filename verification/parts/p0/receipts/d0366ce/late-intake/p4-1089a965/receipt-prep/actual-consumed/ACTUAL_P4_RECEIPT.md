# P4 1089a965 实际接收回执：已完成阶段与 fresh 超时

## 结论

**本次正式接收真实的部分成功证据及 73 项完整编译器类型；整套 P4 专项 CI 仍为 FAILURE，五模块暂不接入 d036。**

在固定源 `1089a965e20664e63ffd51e0105c11befa406a1f` 上，依赖与五目标的 `lake build`、五个强制 strict source compile、五个 individual stock replay，以及完整 Audit strict compile 都实际成功。随后第 18 个 stage——`leanchecker --fresh --verbose verification.Part4UpperAudit`——触及 1,800 秒 timeout。该失败不是前期依赖 build timeout，也不是新增 Lean 源码诊断。

Audit 已实际输出全部 **73 owned declarations：68 个 theorem、5 个 definition**。本回执从保存完好的原始 stdout 中提取完整类型与逐声明公理；它们的类型口径现在是 **compiler printed，pp.all=true**，不能再称为仅源码候选。与此同时，fresh、末尾 source/object/binary recheck、final HEAD 与最终 required outcome 未通过，不能把这些已完成阶段称作完整封存成功。

## 1. 固定身份与原件

| 项目 | 实际值 |
|---|---|
| P4 源 SHA | `1089a965e20664e63ffd51e0105c11befa406a1f` |
| 直接父提交 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 现有集成基点 | `d0366ce64272e81faf6166a8a90050f56b328d38`；本回执没有接入 P4 源码 |
| GitHub run | [38288356713](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38288356713)，attempt 1，completed / failure |
| 实际 job | `114942066124`，completed / failure；结束 `2026-10-12T19:17:11Z` |
| Artifact | `11768093422`，`part4-upper-38288356713-1` |
| ZIP | 121,929 bytes，28 members |
| ZIP SHA-256 | `37663f49d9e1537167c62ffd3b291772f1761c562d1cc61b52e4b43cd424fb6b` |
| Audit 原始日志 | `run-1791828370977599814/axioms-and-types.log`，93,993 bytes |
| Audit log SHA-256 | `e2c2d23216027005e6ec65794abaa565c964c65d0d3f74df30689f131b2dca86` |

ZIP 大小、digest、所属 run/source、实际 job 和全部 28 个成员已经独立核对。顶层与独立 run 子目录的 `report.json` 原字节一致。原始 `run.json`、`jobs.json`、`artifacts.json`、`job.log`、ZIP 保持不动。

## 2. 实际执行结果

依赖与全部五目标 `lake build` 从 `18:06:15.964737Z` 开始，**2,131.595 秒、exit 0**，完成全部 9,404 个构建任务。日志中五个目标均有各自真实 `Built` 标记；这里没有“目标尚未到达”的歧义。

| 模块（`ImbalancedChen`） | 强制 strict 编译 | individual stock replay | owned 声明数 | theorem / definition |
|---|---|---|---:|---:|
| `ActualUpperPolicyDensity` | 5.584 s；exit 0 | 11.194 s；exit 0 | 13 | 13 / 0 |
| `UpperCoefficientPerturbation` | 3.874 s；exit 0 | 9.791 s；exit 0 | 7 | 7 / 0 |
| `ActualUpperDensityAssembly` | 6.080 s；exit 0 | 11.344 s；exit 0 | 11 | 11 / 0 |
| `RealPhysicalUpperWeightBridge` | 4.128 s；exit 0 | 9.840 s；exit 0 | 38 | 33 / 5 |
| `RealUpperCountingAssembly` | 6.281 s；exit 0 | 11.394 s；exit 0 | 4 | 4 / 0 |

五个 strict 命令逐一包含 `-DwarningAsError=true`、显式源文件和目标 `.olean`。五个 replay 逐一使用记录的 sysroot 下 bundled `leanchecker --verbose MODULE`，各自精确 `replaying MODULE` marker 恰一次，exit 0。

Audit strict compile 从 `18:43:07.108908Z` 开始，**239.657 秒、exit 0**。原始输出有全部 73 条声明 JSON、五条 module count，以及最终 `PART4_UPPER_AUDIT_COUNT 73`；原输出未截断。成功 stage 总数为 17，失败 stage 为 1；第 19 个 `final-head-commit.log` stage 没有执行。

### 源码与当时记录的目标对象

| 模块 | 初始源 SHA-256（已与固定 Git blob 比较） | strict 后记录并在 individual replay 前后核对的 `.olean` SHA-256 |
|---|---|---|
| `ActualUpperPolicyDensity` | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` | `1af138f17ad6bf918dc74ee44adb0c9a6c94cacc672d4b6814d1fb341917a7d9` |
| `UpperCoefficientPerturbation` | `e4d1d84fa128f7f84fb4f7d4f0b03acf8401312de1ceaed045de3aaf3b5d6e86` | `e7a1054b0deb8941b167251324956b190abef52f2b6cf4544179bc9131781096` |
| `ActualUpperDensityAssembly` | `659aa3d8cfa50345f912ba070e30cd57a6caa1738e4146d1c051a7506f944cec` | `5fdc744503a4c3f5100fc92bdfc49aac58ce707af4d14935471abfe42bb290a8` |
| `RealPhysicalUpperWeightBridge` | `8a86c2e7fd2383fcae243b5958f3447675a4f5b7a4c9078ba1ba832ea067878f` | `c11d69c64ba3c4efe11870bc4c3d85b576c425a50218ad0a3a8b105aa03003f1` |
| `RealUpperCountingAssembly` | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` | `805f285fa45c39b7aa075b2430e1417ec02e7329f48f58e8762fcedb0d5c24d3` |

实际对象清单只有这五个主要 `.olean`，没有记录 `.olean.server` / `.olean.private`。这是固定 runner 当时检查到的实际部分集合，不假定每个目标必须有三个文件。报告在所有 individual replay 循环通过后才写入 `compiled_module_sha256`，故这五个前后 replay 对象检查已经由真实执行路径支持。

这些对象实体未归档在当前 ZIP，离线接收没有假称重新读取或重放它们。Audit 自己的对象哈希只在 fresh 成功后写进报告，因此本失败产物没有该字段；不能用源文件哈希替代 `.olean` 哈希。

## 3. 完整编译器类型与所有 owned axioms

五模块实际所属声明计数依次为 **13 / 7 / 11 / 38 / 4**。构成为：

- 53 个原始公开 source theorem，全部能对应到真实 compiler inventory 的名称、所属模块与 theorem 类别。
- 1 个 private theorem。
- 14 个额外生成的 theorem，包括 `_proof`、`_simp` 和 `.eq_1` 声明。
- 5 个 definition。

因此总计 `53 + 1 + 14 + 5 = 73`，其中 theorem 为 68。采用 defining-module metadata 统计，不能只看 `ImbalancedChen` 名称前缀或源码中 `theorem` 的行数。

73 条类型全文共 73,351 个 Unicode 字符；全部有 universe_parameters 字段，实际未见 `⋯` 省略。对应已绑定的 Audit 源码使用 `pp.all=true`、`pp.privateNames=true`，并拒绝 unsafe 和 own axiom；该 Audit stage 实际 exit 0。

逐声明 transitive axiom 集合的实际分布：

| 公理集合 | 声明数 |
|---|---:|
| `Classical.choice`、`Quot.sound`、`propext` | 65 |
| `Quot.sound`、`propext` | 7 |
| `propext` | 1 |

没有其他 transitive axiom，也没有 axiom 类别声明。完整逐条结果、私有和生成声明名称均保存在派生清单，不能由这张汇总表替代。

### 本回执提供的完整类型文件

| 文件 | 口径 |
|---|---|
| `COMPILER_DECLARATIONS_73_FROM_RAW_AUDIT.json` | 73 条原始 JSON payload、原始 log 行号、parsed record 和来源身份 |
| `COMPILER_TYPES_73_FROM_RAW_AUDIT.md` | 全部 73 个实际完整 pp.all 类型与逐条 axioms |
| `KEY_COMPILER_TYPES.md` | 8 个关键 P4 公开接口的完整编译器类型，包含 full-policy density、compiler reserve、same-rho majorant/counting 等 |
| `PUBLIC_SOURCE_VS_COMPILER_TYPES_53.json` | 原 53 个完整源码声明头与对应实际 compiler type 并列保存 |
| `ACTUAL_MODULE_LEDGER.json` | 五模块的 source/object 哈希、严格编译、重放、owned 数量、公理和接收范围 |

生产者 runner 只在 successful fresh 之后才写四个正式 export：`declarations.json`、`declarations.tsv`、`declaration-types.txt`、`theorem-types.txt`。**这四文件本次实际不存在。** 上列另名 P0 派生文件只是保存已经实际输出的 Audit 内容，没有伪造缺失的 producer export 或最终 PASS。

## 4. 第一条真实失败诊断与 fresh 证据

aggregate fresh 从 `18:47:06.769610Z` 开始，报告 timeout budget 为 1,800 秒；实际 stage elapsed **1,800.037 秒**。首次失败文本在原 `runner.log` 第 **36** 行，GitHub 原始 `job.log` 对应第 **512** 行（`19:17:06.8140537Z`）：

```text
FAILED: Command '['lake', 'env', '/home/runner/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/bin/leanchecker', '--fresh', '--verbose', 'verification.Part4UpperAudit']' timed out after 1799.999991103 seconds
```

之后的 `runner.log` 第 60 行、`job.log` 第 536 行是同一 `subprocess.TimeoutExpired` traceback。分类为 **进程时间配额耗尽，发生在 aggregate fresh 阶段**。没有带 Lean 源文件、行号、列号的实际错误；fresh 进程的 exit code 未被本 runner 记录，不能写成 124、130、-9 或另一个猜测值。Python runner / GitHub step 的退出 1 与 fresh 子进程未知 returncode 应分开。

fresh 原始 phase log 只有 **161 bytes、1 行命令头**；命令后的正文为 **0 bytes**，completed fresh marker 为 **0**。因此只能确认 stock fresh 命令已启动并耗尽配额，**不能断言它已经重放任何特定模块**，也不能把日志空白归因于已证实的 buffering、hang、死锁或某个 Lean 证明错误。

首诊断 JSON、精确原始行、原始 runner 全文及 fresh log 都保存在 `consumer-v2/`；`FIRST_DIAGNOSTIC.json` 的原始 log SHA-256 为 `c8237361e067f0d2dfc65777e072f79e73eb08ec641267877ba02385eaa918fd`。

## 5. 未闭合验证门与源码身份限制

此次明确没有完成：

1. aggregate stock fresh replay 的 successful exit 与精确 completed marker。
2. fresh 后所有源文件 SHA-256 的末尾重查。
3. dependency HEAD / cleanliness 的末尾重查。
4. `final-head-commit.log` stage。
5. Audit 对象哈希落报告，以及最终对象部分集合/哈希重查。
6. 三个工具链二进制 SHA-256 的末尾重查。
7. 最终 count/module records、四个正式 export 和成功 required outcome。

实际 `outcome.log` 是：

```text
cache=success
verification=failure
```

实际 workflow 的综合验证步骤、required outcome 步骤均失败；artifact 上传成功，不构成证明成功。GitHub run 和 job 都最终 completed/failure。

### 初始源、对象、工具链证据的准确范围

报告初始 `source_sha256` 含 717 个源/配置文件。本地固定 Git 对象可以独立核对其中 **200 个项目源/配置文件**，包括五生产模块、Audit、runner、源码 lexer、workflow 和锁文件。另 **517 个依赖文件**尚无本地固定 Git 对象可独立读：goldbach 506、LeanArchitect 9、batteries 2。共同 repo 的这三个 `.lake/packages` 目录确实不存在，没有假定其他会话缓存共享。

实际 CI 在编译前检查了全部十一 dependency revisions 与 clean dependency working trees；该记录已保留。独立离线源码比对缺对象，与实际完成后 CI failure 是两个不同状态：**不能用 INCOMPLETE 覆盖已经确定的 FAILURE，也不能用 GitHub 运行事实假称已离线重 hash 517 个未读文件。**

初始 Lean/Lake/checker SHA-256 分别为：

- Lean：`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`。
- Lake：`60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3`。
- leanchecker：`ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a`。

实际 `lean --version` 与固定 `leanprover/lean4:v4.33.0-rc1` 一致。由于末尾 binary recheck 未执行，这些是初始记录，不升级为完整前后绑定。

## 6. 消费者首轮、定位修复与保留结果

准备好的消费者 v1 对真实 ZIP 首次执行 exit 1、stderr 空，无 Python 消费异常；得到 **385 PASS / 11 FAIL / 14 INCOMPLETE**。这些是离线回执门的计数，不是 Lean 定理数；多个失败门是同一 fresh 超时及后续未完成步骤的体现。

独立逐行查看原件发现 v1 的诊断正则没有收 `FAILED:` 前缀，故选中了第 60 行 traceback，而不是更早的第 36 行首诊断。这是 **消费层定位遗漏**，不是 Lean 源码修复。

v1 代码、原执行 JSON、stdout/stderr 与完整结果都保留。新 v2 仅扩展该前缀，并因代码移到独立目录而保持同一获准 `receipt-prep` 输出根；没有改编译器、Lean、证书、CI、timeout 或成功门。v2 再消费同一未改 ZIP，正确定位第 36 行；所有 gate count、73 项库存与 actual CI failure 保持一致，exit 1、stderr 空。

定位问题保存在 `CONSUMER_V1_DIAGNOSTIC_ORDER_ISSUE.json`，消费层 diff 在 `consumer-v2-code/consumer-v2-change.patch`。新消费者 SHA-256 为 `6d475152ef800aa506820d69ae604d2777a941caa113af47efe13b2636527891`。

## 7. 接收范围、开放数学接口与下一最小动作

本次接收的对象是：固定五模块真实 strict 与 individual stock replay 阶段结果、73 项 complete compiler inventory，以及真实 fresh failure。**不把五模块标成完整项目门通过，不接入 d036，也不把四个 common-carrier `.lean.txt` 候选纳入本 Audit。**

最新 P4 状态应更新为“修复源码已有原始严格编译/重放/完整 Audit 证据；fresh 及末尾封存未完成”。此前“最新 P4 原始类型清单丢失”的状态被这份新的真实原件补充；旧 3d5d/262f、d036 版本范围内的历史记录仍保留原身份。

数学接口仍保留原类型中的 `hIntegral`、`hCertificate`、完整实际政策和 compiler reserve。same-rho `hmajor`、`hdensity`、`hcoprime`、`hdistribution` 没有实际全套供应者。actual sharp K、hUpper、完整 Chen mean、c、hLower 都未闭合；P5 仍只等待 P4-A，不必等待 P4-B。

下一最小动作是先保存并复用这些真实已成功阶段和完整类型。可独立准备 P0 所有的 timeout 可得 partial-output 记录补丁，以改善下一次实际失败记录；它不证明当前 fresh 曾完成任何模块，也不改变预算或成功门。本回执不启动验证。未来任何正式接收仍须在正常环境补足原 stock fresh 与末尾身份检查，并将完成结果绑定到明确的验证/集成 SHA。

## 留档与完整性

机器回执为 `ACTUAL_P4_RECEIPT.json`；源码/对象/import 范围另见 `SOURCE_OBJECT_IMPORT_BINDING_STATUS.json`。当前原件、原 44 文件封存、原 preparation manifest 及本次输出分别保留完整哈希。未运行 Lean、Lake、CI 或进程控制，未修改 Part 源分支或 d036 工作树。
