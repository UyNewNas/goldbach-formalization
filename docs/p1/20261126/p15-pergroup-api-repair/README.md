# PerGroup 单源修复：保留 M / K / F / B 原验收

此入口只将未验收的 `ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward` 从 M 原像替换成 N 已发布的精确后像。入口自身尚未在云端执行；它不运行 Lean、Lake、kernel 或 readiness build，不产生新验收。

源码锚 N 为 `c47ea640bf40c22423aec7066c13e5b05956d349`。执行参数 `--source-commit` 应当指向随后原样发布本目录的 O，而非 N 或历史 M；脚本会要求自身原字节、manifest 以及 O 的全部 360 份源码与固定 N 输入吻合。

## 唯一源码变更

| 项目 | 精确绑定 |
| --- | --- |
| 失败源码 / 编译身份 | M `54c6e72732ce3a6d209960c396956f9cb2fe3f59`；`job_11072d40ef774d1abb6afb1c38b215b1`；`runs/attempt-00000` |
| 原像 | 9,091 bytes；SHA-256 `090fc6f2140dcb74a01865d25f7c8158364cf31d2b6300884cd6d35f870730d9` |
| 后像 | 9,093 bytes；SHA-256 `83ac50b41f5927c3e408611cb01cdc5d3712d730b49a507923179eba951606d6` |
| 唯一 splice | 原字节 `[7125,7175)` 中 `simp_rw [ih,mul_add,Finset.sum_add_distrib]` 改为 `simp only [ih,mul_add,Finset.sum_add_distrib]` |
| 全模块 probe | `job_61b286303db242948dfe69652fe8aba3`；实际 exit 0；无 `-o`、无 owner outputs；原 18 份失败记录、6 份 Licensed 回执、5 源码及 105 artifacts 均保全 |

N 中 `ACTUAL_M_METADATA.json`、`REPAIR_CANDIDATE.json`、`ACTUAL_PROBE_RESULT.json` 和 `LICENSED_M_PUBLIC_ACCEPTANCE.json` 的完整 pins 均在 `REPAIR_MANIFEST.json`。probe 是整模块 typecheck，不替代后续 normal/kernel/full-owned 验收。

## 原失败组与后续检查分开

原 M 的 RESULT / WORKER_RESULT 选择 **15** 个目标，实际只接受 Licensed，随后 PerGroup normal 失败；完整原始状态原样保留。更新器随后调用原 M 的完整 preflight 时选择 **14** 个目标，明确排除 Licensed。这两份选择列表独立固定，不能拿 14 项列表去改写原 15 项结果。

原 M 图给出 157 份 live 源码、143 个保留依赖、160 个监控模块，以及 15 个 current-owner 状态。Licensed 是其中唯一已接受的非选中依赖：按原 M `existing_owner` 和 `require_completed_existing_owner` 重新核对真实 normal / full-owned 回执，保留其 68 模块闭包、原 source-plus-five、全部 21 个 artifact、6 份回执及完整证据文件指纹。原计数为 33 owned / 33 public，audit 为 `43cb6e04e72ce50bfc8e`。Licensed 不进入 fresh 检查，也不重新编译。

其余验收身份继续固定为 Cutoff@K、HB@F、Support@B。代码分别保留 `FAILED=M` 与 `CUTOFF_SOURCE=K`；Cutoff 的 K/run0 与 PerGroup 的 M/run0 不共用来源常量。旧 13 个供应者和 126 个固定依赖仍经原 API 检查，历史回执不重绑到 N 或 O。

## 唯一失败 setup 的保留迁移

已实际检查的唯一现存失败 artifact 是：

`/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5PerGroupIntegerHBAtlasPushforward.setup.json`

它必须恰为 6,328,419 bytes / `c6fb3ebc059387bb4cbb2f009b23ed377a01a9f0e575767c1bda8ae3efe5d63a`，同一目标其余 20 项必须全部不存在。归档复用 M 更新器的四个原函数：先在本次独立证据目录独占保存全部原字节，flush/fsync 并保存绑定回执；核对原文件身份和全文指纹后，仅移除这一活跃 setup。未知文件、不同 hash 或不完整既有归档都会 HOLD。

归档后调用**真正且未改的原 M 完整 preflight(14)**，要求 Licensed 仍为原 M 已接受依赖、14 个选中目标均 fresh、所有保全对象一致。随后才调用原 `h.install_sources` 安装唯一 PerGroup 后像，并保存完整源码原像备份。安装后复核 157 源码图和 160 模块的全部原 artifacts / 回执 / runtime；另外 359 份发布源码完全不变。

## 执行与静态检查边界

O 发布后，由根代理从其固定 Git blob 保留脚本原字节到独立路径，再按顺序使用：

```text
python3 -B <O入口的独立保留文件> --source-commit <O完整提交> --check
python3 -B <O入口的独立保留文件> --source-commit <O完整提交> --apply
```

`--check` 不创建 attempt、不归档 setup、不安装源码。`--apply` 使用原 lane-0 serializer/guard，并保存 Git 前后状态；不更改原 checkout、runtime 配置或其他缓存。这里不调用 additive installer，也不再次安装此前源码集合。

作者已完成一次必要的本地静态验证：精确读取 M/N 的 360 行源码，只有单一已记录 splice；图计数、全部真实证据 pins、接受闭包不相交及 Python AST 均通过。四个归档函数及另 13 个旧函数与已发布 M 更新器逐字节相同。没有执行或 import updater / driver / API，没有 Lean 或云任务。最终独立只读审查结果记录在 `STATIC_REVIEW.json`；静态通过不等于云端修复或数学 owner 已验收。
