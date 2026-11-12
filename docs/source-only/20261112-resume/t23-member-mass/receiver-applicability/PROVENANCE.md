# T23 适用性补件的来源和访问记录

本补件由 APPLICABILITY.md 与 PROVENANCE.md 两份文字组成。数学判定属于源文适用性核查。七源包及 T18 对七源的独立审查各自保有原冻结记录。

| 核查内容 | 源或冻结标识 |
| --- | --- |
| T23 七源包 | discrete-primebox-next/REGISTRY.json SHA-256 cd8a7117ed7db4f3daaf8b7f1aaa1023cd53551ad6e4fd036398955ed98ccfc2，REPORT.md SHA-256 e058b34998594433abc41177271ef04c2b5ec7320d754a57e2b95b219c92d1c9 |
| 七源独审 | t18-u34-review/t23/discrete-primebox-next/REVIEW.md SHA-256 60c1ffc2b0b79d023841cb30950eea85cf1a99fb2a502f2a6d2502d97f91cd56，ALLOWLIST.json SHA-256 df6bafe25d39989995802355b2fe844c487eec3e243ffcacb9a0b1c7ae337c12 |
| 全收据恒等式 | t17-u34-member/Part5OriginalH430OriginalReceiptMemberPullback.lean，行 135、140、178、211，SHA-256 172f06c06ccd609e6293abdff07c7401c81b5dc51ae734ccd48ac4273c013119 |
| 全部实际位置与拒收项 | t17-u34-member/Part5OriginalH430AllEmittedReceiptLanes.lean，行 43，SHA-256 3556efd3f056c7c08fa11bb681b141221a54f5a60bb8f7e916b4870bd4e3d389 |
| 根截点的等式与有向上界 | t19-w12-exceptions/net-successor/Part5OriginalH430ReceiptTwoBounds.lean，行 27、97，SHA-256 b3b19df41f420f16ad366d9dd9cb69f022a5cff76440442a38c5e3db7cac94ed |
| 普通双子窗口 | Part5OriginalH430PairOrdinaryCountPayment.lean，blob d415659231feb29f7f386edee4cb795e1b50367c，all_good_pair_count_means |
| 原正元组上筛 | t24-dist-positive-sieve/revision-02/REPORT.md SHA-256 c0e1087faea5e8a2e12b9d30f8212caecf918fe7ec26b47d65d1cbd1d8169574 |
| 原稿 | 手稿提交 9731290e8f53cffda44129906cde6a965eaa869b 的 paper/source/manuscript-body.tex，blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79，SHA-256 ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd。以本地 chen-imbalanced-semiprimes/paper/source/manuscript-body.tex 重算 SHA-256 一致，读取正文第 795–817 行。 |

## 本次对象读取例外

七源及其索引冻结后，在适用性核查中，我误把手稿提交号交给 Lean 源的部分克隆仓库。执行的是针对 goldbach-proof-github-sync-20261110.git 的只读 ls-tree 请求。因该仓库本地缺这个对象，客户端自动尝试 upload-pack 读取。工具输出两次 “remote error: upload-pack: not our ref 9731290e8f53cffda44129906cde6a965eaa869b”，最终为 “not a tree object”，退出码 1。该请求触发了远端协议，未返回所求手稿对象，不能作为手稿来源。此次调用未要求推送、修改远端引用或写入原工作树与 index。这里报告调用、应答及退出状态，未审计客户端的内部缓存日志。

我已向根报告这一例外。根随后明确要求本席停用全部 Git 工具与命令。此后的补件工作只读取现存文件，采用上述手稿配对哈希，并在 T23 独占补件目录写入文字。七源包原有 SOURCE_ONLY / uncompiled / kernel credit 0 的状态继续适用。
