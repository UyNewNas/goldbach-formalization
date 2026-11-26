# Licensed `ContDiff` scope repair candidates

These are three source-only candidates for the fixed later-15 run at K
`237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e`. The actual first failure was
`ImbalancedChen.P5LicensedOriginalIntegerProfile` in
`job_05205bc1d3f7442da9444752ab8a9972`, K `runs/attempt-00001`.
Its normal command failed with 13 source diagnostics; the fixed normal log has
SHA256 `49325bcc9885453411976db0a2db759541b80bcd87b9332bed61186614c2cb77`.

## Exact correction

The pinned Mathlib commit is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Its `ContDiff` scope defines smooth
`∞` as `((⊤ : ℕ∞) : WithTop ℕ∞)`. The outer top `(⊤ : WithTop ℕ∞)` is the
analytic order `ω`. These candidates enable the official scope and preserve
every declaration and proof byte. They do not replace `∞` by outer `⊤`.

`REPAIR_CANDIDATES.json` records the three preimages, postimages, exact byte
intervals, the fixed official API sources, manuscript passages and the limited
same-cause search. `EXACT_DIFF.patch` contains the corresponding three changes.
The original files, including existing CRLF bytes, are retained under
`preimage/`; the repaired copies are under `candidate/`.

| Candidate | Bytes | SHA256 |
| --- | ---: | --- |
| P5LicensedOriginalIntegerProfile | 3763 | `675cea556d3f85f4ca5e4e4c197b95ddd11e2e60f85e86de52388fe9b2531679` |
| P1OriginalSingletonSmoothLicence | 4358 | `f74c3c51c0b1de7b493f9fe7e883d89a4b5c163624bb5be1f6901fbec3424011` |
| P5AdmissibleAllRankIntegerGeometricFamily | 6653 | `9f8d0ad201037d39ddff34f0a7619456a29eb8cc61ccd0e45011769247d3c01e` |

No canonical source, project cache, original runner, guard or configuration was
modified in preparing these candidates. No Lean command has been run locally.

## Bounded metadata and whole-module probe

`collect_and_probe_licensed_scope.py` is 24514 bytes, SHA256
`ece695e386fc08f74c9416b7a15e00a73b217d3f606943ac69df5efa00eefb27`.
Its arguments are `--probe <exact-whole-module-file>` and
`--cutoff-public <exact-CUTOFF_K_PUBLIC_ACCEPTANCE.json>`.

The probe file is byte-identical to the entire 3763-byte Licensed candidate,
including all original declarations. Its imports remain the accepted HB module
and Mathlib. The only Lean command is the original lane-0 serializer and guard
around `lake --no-build env lean <probe>`. It requests no output object. The
SmoothLicence and Geometric candidates are not probed with invented suppliers.

The script reads 18 fixed failure records, the three pending source preimages,
and 21 artifact paths each for Licensed, Cutoff and HB. It binds Cutoff to the
successful K `runs/attempt-00000`, and HB to the original F
`080d4178711ae042235104f7f4768649f51da2ab` partial group. Original accepted source
snapshots, all 42 accepted artifact paths and both six-receipt sets are checked
before and after the probe. The script does not repeat their full-owned audits.
Private type exports and archive contents remain on the compiler workspace.

The Cutoff public input is the existing 4286-byte summary with SHA256
`d7154414aa34e42a0b34e4e6cc7283b2b91fb55c114c0f44e9a9f7c4e582ed74`.
It records the actual 16 owned / 8 public declarations. Those counts are read
from the original acceptance, not predicted for Licensed.

The bounded output contains the metadata and probe result under schema
`p15_licensed_K_metadata_and_whole_module_probe_v1`; its limit is 32768 bytes.
Unknown failed-owner artifacts cause HOLD without probing. A nonzero probe exit
also causes HOLD. A successful no-output probe is not normal/kernel/full-owned
acceptance. Runtime/configuration, original receipts and the observed source and
artifact tables must remain unchanged.

The collector and candidate inputs have passed local syntax/byte verification
only. The root agent schedules the actual P1 execution and will place its real
bounded output under `docs/p1/20261126/p15-licensed-profile-first-compile-repair/`.
No future publication commit or successful probe result is assumed here.

## 实际整模块类型检查

任务 `job_f9f175857d0843b7b0ec7b5e8785378b` 实际 exit 0，运行 23.223 秒；19052 字节输出已完整读至 EOF，无截断。组合任务先只读绑定 K `attempt-00001` 的 18 份失败记录、三份待修源和 63 项 artifact，再通过原 serializer 与 guard 对完整 3763 字节 Licensed 候选执行一次 `lake --no-build env lean`。

结果 exit 0，编译器日志为空。没有请求或生成 owner 对象，没有重建任何已有模块。三份 live 源、63 项产物、Cutoff@K 与 HB@F 的原验收身份、runtime、配置和 Git 状态均保持。真实 metadata 为 `ACTUAL_K_METADATA.json`（19586 字节／`62a5e300abe1a1455283d98bbde2ad7008b5dc0ecd730d6275ddab1bca461365`），probe 结果为 `ACTUAL_PROBE_RESULT.json`（1492 字节／`0b3f9bb588d1cad385d0b8da8d0319892a3fddbdc801e7b96b40deb5b2274f29`）。

Licensed 仍须正式 normal/kernel/full-owned 验收；另两份同根因 scope 候选尚未编译。原 K 后十五项目标失败记录保持，不把此 probe 改写为整组成功。固定输入、终态与完整输出观测见 `COLLECTION_AND_PROBE_RECEIPT.json`。
