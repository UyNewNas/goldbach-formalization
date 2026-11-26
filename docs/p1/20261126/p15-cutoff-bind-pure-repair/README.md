# Cutoff: second compile, exact list-coercion repair

This candidate addresses the one remaining source error from I
`f21a8601d99ea33ec572223f5267415ca4ead8db`, compiler job
`job_dad68eb4d5fb48c588bd027157e85adf`.
The root's actual normal diagnostic reported that `rw [List.forall₂_map_right_iff]`
at line 31 could not find `List.map`: the coerced second list was still
`do let a ← ps; pure ↑a`. The other three expression repairs had passed this
normal run. This is a Lean coercion/API expression issue in the existing finite
supplier, with no change to the original mathematical contract.

## The sole source delta

Immediately before the existing `rw`, add:

```lean
  simp only [Lean.Internal.coeM, bind_pure_comp, List.map_eq_map] at hwin
```

The original `rw [List.forall₂_map_right_iff] at hwin`, complete induction,
`hsource`, seven theorem headers, imports, and all later proof bytes remain as in I.

The exact preimage is 12,670 bytes, SHA256
`d0fb57566d511f7ab4ef9270e71f53fb13b98d1b793feca0abacc24f2db02ccc`.
The candidate is 12,744 bytes, SHA256
`ceb0d90a99b41455124802c5446d16499e11207f1042b790f0646d4c19272b22`,
Git blob `02c6f6f263d058691225212ad8c9423f68563f96`.
The manifest and unified diff record the exact replacement of old bytes
`[1263, 1307)` by the new normalization line followed by that unchanged `rw` line.

## Why this matches the actual expression

The matching Lean 4.33.0-rc1 source `Init/Coe.lean` defines `Lean.Internal.coeM`
as exactly `bind` followed by `pure` composed with the same scalar coercion.
Explicitly unfolding this abbreviation avoids relying on the simplifier to
expose it while searching for a law. `Init/Control/Lawful/Basic.lean` supplies
`bind_pure_comp`, converting that expression into functor map.

In the fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
`Mathlib/Data/List/Monad.lean` defines List bind as `flatMap`, List map as
`List.map`, and proves `List.instLawfulMonad`. `List.map_eq_map` in
`Mathlib/Data/List/Basic.lean` exposes `List.map` by `rfl`.
The already used `List.forall₂_map_right_iff` then transfers the same relation
back to the natural-number list `ps`. Its original membership carrier and
`hsource` are retained. All these APIs are already on the existing import path;
there is no new import or arithmetic proof.

The fixed 1106 manuscript paragraph at coefficient-appendix.tex 513–520 still
supplies the same step: original dyadic windows and scale bounds ensure the
common rough cutoff is eventually below each original prime. This candidate
only repairs list normalization inside the already present finite supplier.
Precise official-source hashes and line intervals are in `REPAIR_CANDIDATE.json`.

## Exact real-lemma probe

`ActivePsiScaleEachProbe.lean` is the candidate's exact byte prefix through the
end of its first namespace: 1,790 bytes, 46 lines, SHA256
`1abe0939bb3a02bc04815946da63d96f18578cff64ed773de28454d618a03d0f`.
It keeps the actual `active_psi_scale_each` statement, local notation, `hwin`,
`hsource`, and complete proof. Its only import is the already accepted
`ImbalancedChen.P5OriginalPrimeChartHBWitnesses`; it does not import Cutoff.

The root owns any guarded isolated typecheck of this probe. No local Lean,
kernel, runner, updater, installer or cloud execution was performed here.
A successful probe would check this exact lemma and API mechanism; it would
not itself replace the subsequent full-owner normal/kernel/full-owned audit.

## Static checks

Forward and reverse splice reconstruction, all seven original statement
headers, imports, and the accepted HB source bytes were checked. `git diff
--check` returned exit 0. The original source-only records and all old receipt
identities remain unchanged. This candidate is not presented as Lean accepted.

## 实际首引理类型检查

P1 任务 `job_c600a527fa4f4d5097b149a409367447` 随后实际运行了这一逐字节首 namespace 前缀，`lake --no-build env lean` 经原 lane 0 serializer 与 guard 返回 exit 0。没有输出项目 owner 对象，也没有重编译已接受的 HB。HB 与 Cutoff 的全部21项产物、活跃源码、runtime 配置及 Git 状态前后相同。原样结果见 [ACTUAL_PROBE_RESULT.json](ACTUAL_PROBE_RESULT.json)，执行范围见 [COLLECTION_AND_PROBE_RECEIPT.json](COLLECTION_AND_PROBE_RECEIPT.json)。

日志唯一提示是 `Lean.Internal.coeM` 为 unused simp argument；保留已实测候选，不关闭 linter。该类型检查确认本次 bind/pure 表达问题已经解决，但不代替整个 Cutoff 模块的 normal、kernel 和完整 owned 验收。旧 I normal 失败记录保留在 [ACTUAL_I_METADATA.json](ACTUAL_I_METADATA.json)，只读收集未扫描未来157源，也未执行原 full audit。
