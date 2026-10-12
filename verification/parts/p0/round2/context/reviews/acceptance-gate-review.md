# P0 分批接受门槛独立复核回执

结论：本次六个生产模块与两份实际审计输出的只读复核通过；未发现会导致本批误收的剩余身份、类型或系数问题。此文件是代码与证据复核，**不是所有组件门槛已通过的接受回执**。

编制时间：2026-10-12 04:42:33 UTC。审查员：/root/p3_p4_intake。

共同证明基线：1a80c1bcce67886f699d097fc37fd245cd3620bf；手稿：ba6ec11d800eccc54406490631895e174de85766；工具链：leanprover/lean4:v4.33.0-rc1。

## 观察时间及重放状态

原审查脚本没有打印精确观察时间，故不补造单一时间戳。可证的观察窗口为 **2026-10-12 04:38:18 UTC 至 04:40:43.728929 UTC**：快照已包含 RationalLogCertificate 的成功重放，其开始时间为 20261012T043714705523Z，耗时 63.402 秒；该快照又早于 04:40:43.728929 UTC 的回执准备读取。

在该原快照中，RationalLogCertificate 重放已成功，并匹配相同起始对象；其余四个 P2 模块和 Buchstab 桥尚无匹配的重放完成记录。这里保留历史状态，不覆盖根之后获得的完成结果。接受脚本要求每个生产模块都有对应重放记录，所以当时不能提前出具全批通过回执。

## 两份实际审计

| 审计 | 实际声明数 | 编译与导入身份 | 完整类型 | 公理 |
| --- | ---: | --- | --- | --- |
| CertificatesFirstCellAudit | 182 | strict=true、trustLevel=0、verification_passed=true；源码、审计对象及五个导入对象匹配 | raw/readable 均无省略 | 全部在三个许可公理范围内，无自定义 axiom |
| PairedBuchstabAudit | 2 | 同样严格通过；桥的实际导入对象匹配 | 两项均无省略 | 同上 |

合计 **184 个定义模块所属声明**；逐模块为 47、13、58、18、46、2。声明名唯一，确切模块集合、各模块计数及总计数一致。枚举来自 Lean 环境的 defining-module 信息，包含私有和生成声明，不用源码正则替代。

## 已匹配的接受边界

- assemble_component.py 的 gate（审查版第 96–105 行）要求成功返回、当前源码前后哈希、当前对象哈希、strict/trust0，并排除 verification_passed=false 及已记录的导入漂移。
- 第 117–131 行检查模块/声明数量、唯一名、公理与类型省略。第 135–155 行绑定重放起始对象、严格编译对象和审计实际导入对象。
- 第 164–170 行保留现有 source guard 的真实执行结果。check_sources.py 明确将该扫描作为严格编译、内核重放和 Lean 公理盘点的辅助。
- check_batch.sh 的 paired-buchstab 入口已经把六个供应模块纳入 tracked/clean/hash/source-guard 检查，供应对象也进入前后哈希检查。没有因此声称重放了全部供应闭包。
- 两个 auditor 启用 pp.all、pp.proofs、pp.deepTerms 与 pp.maxSteps=1000000，并在打印后拒绝 U+22EF 省略符。实际 184 项的 type/readable_type 均未出现该符号或 ASCII 三点。

## 关键类型与系数

已读取编译器输出中的 first_certificate_checked、firstIntegral_bounds、firstIntegral_semantics、first_fibre_argument 和两个 Buchstab 桥类型。首格 certificate/bounds 没有额外分析前提；几何支持条件只包含实际坐标区间和次序，没有隐藏的 K、c、SW、hLower 或 hUpper 包装。

firstIntegral_semantics 明确保留真实四重积分及 (8452171/1250000)/80。桥只证明点态 omega≥11/20 与 omega−1/2≥1/20，没有再乘 firstIntegral；**K/80=(K/4)*(1/20) 已含增益，没有第二次计入 1/20**。

范围仍是实际首格及独立较弱的有理包围，不是存储 Q160 紧界、17572 行全集、完整 mask/算术父对象、真实 K/c 或最终 hLower/hUpper。没有声称完成完整根构建、最终集成 SHA 检查或 Actions。

## 审查文件 SHA-256

| 文件 | SHA-256 |
| --- | --- |
| assemble_component.py | 30611da487d8e1d445563782943a0d6f13cd9619a18eca30a82f977217e77145 |
| validation/verification/parts/p0/check_batch.sh | 2c08179e165c56033b8dfb4154bf542ce5f3f6a4fe9b38c48bbe7cdb47da4a16 |
| validation/verification/parts/p0/check_sources.py | b7fcfbb62374004d00551e3549e4a3c411e4562775dcece4c3e85f13d5ac6716 |
| validation/ImbalancedChen/CurrentPairedBuchstabBridge.lean | 280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550 |

## 实际审计证据哈希

### verification.parts.p0.CertificatesFirstCellAudit

- 审计源码 SHA-256：9273d183ab9216b5205fe7b6a0b063044337a423b8afa1cffc3e901712e549c3
- 审计 olean SHA-256：553e53633905312185ef24d1f9b5bb4b5c9f00aa8ddfbc4021d2edefe1974d54
- 原日志：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log
- 原日志 SHA-256：fb3c2e2daa41a195d9a5a7dbde963aded57d9401c15d39315c2b14cab1a269e7；204698 字节。

### verification.parts.p0.PairedBuchstabAudit

- 审计源码 SHA-256：58707245f39bdba0f3f9ada28e2477173ee4ad08e52aab402b384c67fb378d66
- 审计 olean SHA-256：05eb04a66a728b6df70e0a0285dc671af00377d5eebbcba74de19a0ce1c1f7b4
- 原日志：/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042731728340Z-compile-verification.parts.p0.PairedBuchstabAudit.log
- 原日志 SHA-256：0f7c703008a393a6d8dcf987ca0c00121de038dd2d51a33d7a8c740bdc7af28c；8068 字节。

完整六个生产源码/对象哈希和每项历史重放状态保留在同名 JSON。日志内容本轮仅用于读取和哈希，不改写原验证结果。

## 执行限制

本审查未运行 Lean、Lake、内核重放或 CI，未修改数学代码、验收代码或任何他人工作区，未操作 P1 构建。本次只新写本 JSON/Markdown 回执。LongSlot 仍等待根释放编译槽，未重新启动。
