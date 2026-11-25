# P1.5 第四、第五层完整均值链：最终验收

验收源提交为 [29295f6a7196c523b525104f864da20035cc15d9](https://github.com/UyNewNas/goldbach-formalization/commit/29295f6a7196c523b525104f864da20035cc15d9)。选定的 **23 / 23 个模块**均有当前源码和依赖上下文下有效的原始正常编译、独立内核检查与全部自有声明类型／公理回执。共 **378 条自有声明、349 条公开声明**；实际公理集合恰为 `Classical.choice`、`Quot.sound`、`propext`。

最终 P1 任务 `job_01a0f20b7d60446bab9131098773bd2f` 退出码为 0。该任务只新验收最后的 `P1ActualVariableFifthFullMean`，随后只读复核全部 23 个模块的原始回执，未重新编译此前已验收的模块。

**整项 P1.5 和 P1 仍未完成。** 已验收的三个极限分别为原第三层至实际第四层、实际第四层至实际可变第五层、原第三层至实际可变第五层的归一化保留多项式差。参数、滤子、积分定义与剩余物理计数义务见 [PROOF_SCOPE.md](../PROOF_SCOPE.md)。

## 证据及验证范围

| 文件 | 内容 |
|---|---|
| [PUBLIC_ACCEPTANCE.json](PUBLIC_ACCEPTANCE.json) | P1 白名单程序输出的 23 个模块、各自原验收提交、源码与回执哈希、声明数量、公理集合及上下文稳定标记 |
| [PLATFORM_CATALOG.json](PLATFORM_CATALOG.json) | 20 个已捕获终态任务的公开元数据；19 份完整输出，1 个未启动的资源不可用任务；23 个互不重复的验收事件 |
| [LOCAL_VERIFICATION.json](LOCAL_VERIFICATION.json) | 已执行的本地命令、退出码、输入哈希与结果；逐项核对本地 Git 源码、原验收提交和公开摘要 |
| [ARCHIVE_METADATA.json](ARCHIVE_METADATA.json) | P1 内部保存的完整证据包大小、哈希与文件数；未传出原包 |
| [EVIDENCE_BOUNDARY.json](EVIDENCE_BOUNDARY.json) | 自动审批拒绝整包传出的原因、已获准的受限公开摘要方案，以及本地验证的明确边界 |

本地核对确认：第四层源码闭包为 252 个模块，并包含于第五层的 304 个模块闭包中；这 304 个源文件逐字节匹配验收源提交，规范源码映射 SHA-256 为：

```text
e5334405107c5372177318fea5d596be12e6f509a94994fe54ed22d273119da1
```

这些是依赖上下文的源码数量，验收对象仍为选定的 23 个模块。公开摘要记录的最终原始回执复核报告 SHA-256 为：

```text
a5dbdb1865f95e1b886cc1ce1fd7f84e3a5e09ae631eaa3e4e3b04fb289a8f31
```

全部原始 normal、kernel、owned declaration 回执及类型由 P1 内的固定版本复核程序验证。本地验证只对公开源码、任务事件元数据和摘要绑定进行交叉核对，未对未传出的 `.olean`、全日志或完整类型记录做离线重验。平台目录由已捕获的任务回执生成，不宣称穷尽该共享编译器的所有历史任务。目录保留修复前的失败记录；最终验收以当前源码上下文中的 23 个原始模块回执复核为准。

## 无需编译的本地复核

在仓库根目录执行，工作树中的 Lean 源码须与上述验收提交一致，并保留原验收提交的 Git 对象：

```sh
python3 -B docs/p1/20261125/p15-actual-means/verify_public_summary.py \
  --summary docs/p1/20261125/p15-actual-means/evidence/PUBLIC_ACCEPTANCE.json \
  --catalog docs/p1/20261125/p15-actual-means/evidence/PLATFORM_CATALOG.json \
  --source-commit 29295f6a7196c523b525104f864da20035cc15d9
```

实际运行退出码为 0，结果为 `verified_owners=23`、`project_source_count=304`、`owned_count=378`、`public_count=349`。复核不启动 Lean，也不重新生成或改写原始验收回执。

## 每个模块的原验收身份

下表的数量为“全部自有声明 / 其中公开声明”。最终复核保留各模块原来的验收提交身份，没有将历史回执改标为最后一次源码提交。

| 模块 | 自有 / 公开 | 原验收提交 |
|---|---:|---|
| `P1ActualVariableFifthFullMean` | 4 / 4 | [29295f6a](https://github.com/UyNewNas/goldbach-formalization/commit/29295f6a7196c523b525104f864da20035cc15d9) |
| `P1ActualVariableFifthGlobalPositiveLimit` | 4 / 4 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |
| `P1ActualVariableFifthSmallLastGeometry` | 7 / 7 | [4294a84d](https://github.com/UyNewNas/goldbach-formalization/commit/4294a84d24b24885eedfe101fe68a382879ab94d) |
| `P1ActualVariableFifthTailPointwise` | 9 / 9 | [915921f8](https://github.com/UyNewNas/goldbach-formalization/commit/915921f87cd7fa4f4ca6cc52af712adf02bb2fe8) |
| `P1ActualVariableFifthUniformTail` | 8 / 8 | [a0c521eb](https://github.com/UyNewNas/goldbach-formalization/commit/a0c521ebe87459c1fb7d40732f4382cd850c4921) |
| `P1ActualVariableFifthUntruncatedDomination` | 31 / 31 | [089a7f99](https://github.com/UyNewNas/goldbach-formalization/commit/089a7f99646fe1921d0cd1450485561e6b52b5e4) |
| `P1FifthMiddleNormalizedPointwise` | 21 / 21 | [b2fdcf78](https://github.com/UyNewNas/goldbach-formalization/commit/b2fdcf785d32b712b359d254947d97638b2c00ed) |
| `P1OriginalFifthMiddleShellFiniteBudget` | 13 / 9 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |
| `P1OriginalFifthMiddleShellMovingLimit` | 21 / 19 | [57608d49](https://github.com/UyNewNas/goldbach-formalization/commit/57608d49e043b1d6857145679b958d3416aa3122) |
| `P1OriginalFifthMiddleShellRemainderSplit` | 13 / 13 | [57608d49](https://github.com/UyNewNas/goldbach-formalization/commit/57608d49e043b1d6857145679b958d3416aa3122) |
| `P1OriginalFifthMovingScaleLimit` | 33 / 31 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |
| `P1OriginalFifthUniformSmallRemainder` | 12 / 8 | [915921f8](https://github.com/UyNewNas/goldbach-formalization/commit/915921f87cd7fa4f4ca6cc52af712adf02bb2fe8) |
| `P1OriginalFifthUntruncatedIntegral` | 26 / 26 | [a0c521eb](https://github.com/UyNewNas/goldbach-formalization/commit/a0c521ebe87459c1fb7d40732f4382cd850c4921) |
| `P1OriginalFifthZeroCutoffLimit` | 11 / 7 | [a0c521eb](https://github.com/UyNewNas/goldbach-formalization/commit/a0c521ebe87459c1fb7d40732f4382cd850c4921) |
| `P1OriginalFourthUntruncatedIntegral` | 28 / 28 | [9ea71479](https://github.com/UyNewNas/goldbach-formalization/commit/9ea714790c06b2270f2028555d9ba774b152d536) |
| `P1OriginalVariableFourthActiveMeshCover` | 13 / 13 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |
| `P1OriginalVariableFourthFullActiveIntegral` | 27 / 26 | [b2fdcf78](https://github.com/UyNewNas/goldbach-formalization/commit/b2fdcf785d32b712b359d254947d97638b2c00ed) |
| `P1OriginalVariableFourthFullActivePositiveLimit` | 20 / 20 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |
| `P1OriginalVariableFourthFullSmallRemainder` | 22 / 11 | [915921f8](https://github.com/UyNewNas/goldbach-formalization/commit/915921f87cd7fa4f4ca6cc52af712adf02bb2fe8) |
| `P1OriginalVariableFourthFullSmallSource` | 11 / 11 | [b2fdcf78](https://github.com/UyNewNas/goldbach-formalization/commit/b2fdcf785d32b712b359d254947d97638b2c00ed) |
| `P1OriginalVariableFourthFullSourceAssembly` | 14 / 14 | [57608d49](https://github.com/UyNewNas/goldbach-formalization/commit/57608d49e043b1d6857145679b958d3416aa3122) |
| `P1OriginalVariableFourthFullSourceMean` | 5 / 5 | [a0c521eb](https://github.com/UyNewNas/goldbach-formalization/commit/a0c521ebe87459c1fb7d40732f4382cd850c4921) |
| `P1OriginalVariableFourthUntruncatedDomination` | 25 / 24 | [c57be92d](https://github.com/UyNewNas/goldbach-formalization/commit/c57be92d833b429592d684da495d66db800d9dc8) |

## 完整原始证据包

P1 已生成并内部保存 `verification.tar.xz`，大小为 1,092,172 字节，包含 1,728 个载荷文件。其压缩包 SHA-256 为：

```text
2268244a65db1fdaf08b751e8a6524acb0c38552286687ef351e0950dfa4adae
```

自动审批拒绝了此前提出的整包传出操作，理由是完整载荷可能包含未公开源码、配置、日志和声明信息，且该完整载荷及目的地未获专门授权。被拒绝的传出任务没有提交，也未改用其他通道重试。当前交付采用已通过审批的白名单摘要和聚合元数据；原包仍留在 P1 环境。

## 后续依赖及未完成义务

同一最终参数族和共同充分大阈值下的 `middle`、`comparisonMiddle`、`savingMiddle` 仍需各自真实物理支撑与符号权的计数误差估计；`retainedAtlas` 的中段、remaining Type I、trim、proper powers 及物理碰撞恢复等余项仍须支付。上述均值验收没有替代这些义务。

[历史依赖源码核对](../history-source-recovery/README.md)记录了 26 名有界前沿中的 17 项可访问或已缓存输入和 9 项仍未取得的既有源码。P1、P2、P3、指定本地 Git／归档与文件检索范围均已有记录；未取得不等于全局不存在，也不构成手稿数学缺口的判定。遵守复用已有工作的要求，未重新编写这 9 个历史证明；OneLong 候选仍保持源码状态，未宣称通过编译。
