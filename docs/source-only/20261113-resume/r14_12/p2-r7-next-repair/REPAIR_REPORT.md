# Actual P2 r7 successor — two source-only proof repairs

**SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.** Two selected modules are
repaired here. Compiled modules: **0**. Kernel-verified modules: **0**. ROOT and
Astra03 must review the frozen source before ROOT selects any GitHub validation.

## Actual failure and exact source selection

The real run is `43412656063`, driver commit
`7686657050f460baefd28d3e4777aaec3a18aad8`. Step 16 compilation failed; steps
17/18 kernel/types were skipped. Cache11/407/root86 stock qualification does
not imply acceptance of the failed proof targets. Only the prior OuterMinimum
postimage is actually reported Built in the new source cone (`batch-build.log`,
line 419); no other new module is credited here.

ROOT's existing light ZIP was read without downloading again:
`p2-integer-mass-lightlogs-43412656063.zip`, 4836834 bytes, SHA256
`39ab0b1d6231724d0e8fba1e89b01320f510aeb1317b977833f2814a714c6c23`.
The full `batch-build.log` member is 39316 bytes, byte-identical to the extracted
`BATCH_BUILD_ACTUAL.log` supplied by ROOT. The complete relevant error contexts
at lines 437–462 and 507–552 were read alongside the full selected sources.

The committed actual root selection SHA256 is
`c7ca9e778fa6b21410a11cdf562df6afe9c3f8ada269fbaef28b476e268e1028`;
the actual manifest SHA256 is
`60570c426dd71db2615f490694baab131b4e94705328d9a913eab22dd0b6f459`.
Both were read from the exact r7 driver Git object. The selected sources were
independently matched to the ZIP's `VALIDATION_MANIFEST.json`,
`SOURCE_OBJECT_BINDINGS.json`, and `P2_STAGE_RECEIPT.json`.

| Selected module | Exact commit and origin path | Source bytes / Git blob |
| --- | --- | --- |
| `ActualThirdOriginalP4AOrdinaryRawFallbackAllOld` | `eb035a259f2f40853e9899f6d98af25852184fee:ImbalancedChen/ActualThirdOriginalP4AOrdinaryRawFallbackAllOld.lean` | 21224 / `5518240005699bc735c61965cc85e898374f6b28` |
| `ActualThirdOriginalP4ASymmetricPairRealRescue` | `680fc11a47a9fb081fbf108cd007820e45656ab2:docs/source-only/20261113-resume/r14_12/p2-two-module-repair/repaired/ImbalancedChen/ActualThirdOriginalP4ASymmetricPairRealRescue.lean` | 20345 / `f99d638d524e42b4fb1186e73bb19ff064e15c93` |

The historical independent 102-source allowlist still identifies the exact
RawFallbackAllOld baseline bytes. Its older PairRealRescue row is superseded
by the actual r7 selection above and was not used as that module's input.
Objects were read from `output/t-batch-20261110/publish.git`, using exact
commit/path pins, with no main-branch same-name guess.

## Root, residual and branch proof terms

The r7 errors at PairRealRescue:217 and :322 report an ordinary `match k` proof
of `hroot` where the bridge expects an extensionally identical dependent match
on `k` and the prior branch proof. Both original rise/fall root formulas are
identical on the two sides of the diagnostic. Each root transport now uses:

```lean
by cases k <;> simpa only [literalSymmetricRoot, ...] using hroot
```

The same explicit case split is also applied to the two immediately following
`hres` transport expressions, using `literalSymmetricResidual`. This is a
**structural continuation prevention**, not a claim that r7 reported an `hres`
failure: the real log stops at `hroot`. The bridge has the same ordinary versus
dependent-match issue for the residual argument. Astra03 directly agreed with
following the successful neighbor's full branch/root/residual transport
pattern, rather than leaving the next argument implicit.

The published neighbor
`686024b2:docs/source-only/20261112-resume/t02/p2-repair-r5-r1/repaired/ImbalancedChen/ActualThirdOriginalP4ASymmetricSafeChordDirection.lean:229`
and `ActualThirdOriginalP4ABalancedSymmetricLeaf.lean:345` already use `cases k`
for all three bridge arguments. R7 reports those exact neighboring modules
Replayed at log lines 408 and 412. The old selected `hbranch` repairs are
retained verbatim. No branch/root/residual test or selected side is changed.

## RawFallbackAllOld error localization

All locations in this table refer to the actual selected original source.

| Locations | Classification and evidence | Proof-expression repair |
| --- | --- | --- |
| :71, :210, :236, :255 | Formal sequencing: each diagnostic says `No goals to be solved` on the `ring` following `field_simp`. | Keep both original tactics, composing them as `field_simp [...] <;> ring`, as in the now truly Built OuterMinimum proof. |
| :91–92, derived normalization diagnostic at :81 | Formal elaboration: `linarith` sees an unresolved transitivity endpoint metavariable (`?m.67` / `?m.74`) instead of the concrete intended A/C inequality. | Explicitly rewrite only `v t` via `v_eq_min t`; use fully typed two-step `calc` chains through `A l` and `C u`. Each affine step runs `linarith only` on the original `hlt` or `htu`. |
| :136 | Formal cast normalization: `hh` has real denominator `↑(256 : ℤ)`, while `he` has `(256 : ℝ)`; the integer floor is the same original floor. | Derive `hh'` at the original floor/D and `B (realBox b 2)` endpoints; rewrite its right side with `← he`, then apply `simpa only [Int.cast_ofNat] using hh`. The final B monotonicity step states both endpoints with `show` before using the original `ht 2`. |
| :257 | Formal additive normalization: the diagnostic is `-1 + A` versus `A + -1`. | Add only `add_comm` to the existing `simpa only` set, matching the truly Built OuterMinimum fix. |

The two endpoint `calc` steps use the original affine definitions
`A t = (1+t)/2` and `C t = 57/64 - 3/2*t`. Their monotonic directions are exactly
those already intended by the original `hl.trans`/`hu.trans` proof. The fixed
endpoint types prevent metavariables from reaching `linarith`. No theorem
hypothesis is added and no estimate for the target is supplied as a premise.

The cast repair preserves **integer** division of `153*D₀-96*hi 2` by **256**
before the cast, then division by the same `D₀`. Neither the numerator nor the
floor operation is replaced with real division. `integer_floor_div_cast_le`,
`scale_pos`, the original identity `he`, and `ht` supply the entire argument.
All occurrences of `D₀ = 48000*2^24`, `T₀ = 481573208064`, the literal cap,
assertion `hi 0+hi 1 < sourceCapLower lo hi`, original integer readers and all
geometry/guard premises remain unchanged.

Searches of local published output sources and Git history did not locate a
same-module RawFallbackAllOld successor repair. Existing proof patterns were
reused where available, including the selected OuterMinimum and the neighboring
case-split bridge transports. These sites are classified as **formal expression**
issues. No omitted mathematical supplier or substantive mathematical gap was
identified at the reported errors; this remains a static source assessment.

## Frozen scope and limits

The 17 RawFallbackAllOld and 22 PairRealRescue declaration headers were extracted
by splitting at every top-level declaration start, stopping before `:=`, `where`,
or the first equation branch, then compared byte-for-byte with the exact inputs.
All 39 are unchanged. The diff changes only proof expressions; imports,
definitions, theorem statements/parameters, numeric and interval operands,
integer floors, source guards and hypotheses are retained. No `sorry`, `admit`,
new axiom, opaque target or target hypothesis is introduced.

`SOURCE_PINS_AND_STATIC_CHECKS.json` records exact input/output hashes and
artifact bindings. `TWO_MODULE_PROOF_ONLY.patch` is against these two selected
input objects. New postimages are:

- RawFallbackAllOld: 21702 bytes, SHA256
  `5d9ac43ab3688318a716c847b456149fa7477d291d3b58d73b7d4f0ba04fe573`.
- PairRealRescue: 20393 bytes, SHA256
  `0a291d039033087264df0687cdac2638e33bfbad99cce408fd7deac0b0d4fb2b`.

Only this successor directory was written. Prior P2/height freezes and the
protected dirty continuation HEAD/index/worktree were not changed. No local
Lean/Lake/LSP, environment/setup, project helper, proofguard, fixture, runtime
or certificate execution, Git/GitHub mutation, dispatch, quota check, or agent
spawn occurred. Static source/hash/JSON/read-only Git/ZIP work gives **0 compiled
and 0 kernel verified** modules. Independent review and ROOT's validation remain.
