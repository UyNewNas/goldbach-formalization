# P3 independent02: rough-universe / physical-weight lint triage

Base source: `dc6cb9c65fdc51f9694e93affd2766f3bfb4649a`.
Status: both minimal source repairs pending actual retry after exact-cache triage.
Compile credit = false; kernel credit = false; cache acceptance = false.

The complete P3 log reports `unnecessarySimpa` at
`RoughPrimeUniverse.lean` lines 87 and 95, and unused simp argument `mul_one`
at `PhysicalUpperWeightBridge.lean` line 41. The completed log is
`p3-independent-symbolic-02.log` in this directory, 24,961 bytes, SHA256
`fc454c5577fdbf20d7e8c87276f7d07377ae8dbbed7ed6f2d0424c070097edc0`.

## Exact existing-record check

Read only the two named top-level rows in the shared
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p2-records-619.json`.
Its 16,227,671 bytes / 619 records were checked against original SHA256
`ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`.
No archive was reopened and no CI audit was repeated.

Both rows have `cache_schema=2`, `exit_code=0`, `new_strict_compile=false`.

- **RoughPrimeUniverse initially preserved:** pre-repair source and old record both
  bind `3d716d89548e2e453e96c598481db2f62ae1c76e7f092a960e490a4b70688e58`.
  Old object SHA is
  `3f00715e0a01ef8f6318acd98a4d51eb3ca5b8cc7b62677322398da571c35136`.
  Its direct project dependency is `ImbalancedChen.RetainedModuli`.
  The complete-ancestry check then found
  `RoughPrimeUniverse → RetainedModuli → FirstExitTree`, whose old source
  `6ab5eeb136969f76afc8fcc83dfa211985e0b7ffe85e89dab0702f381ad42a6b`
  differs from current source
  `490490bf81eb411e7fae00805ee02464f5fccee040d621d33fd2ece73dc1c117`.
  Therefore the original exact-dependency migration cannot accept this old
  RoughPrimeUniverse object in the current closure despite its own source match.
  Root supplied the independently computed report
  `/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p3-independent02-six-record-source-closures.json`,
  SHA256 `ab5861ff62c9777cdff1d5491f9e6599b3c1dfe503ea86c6675a780e78fdb0c6`.
  That report's hash was checked; its graph analysis was not repeated.
  Root then authorized the two reported minimal lint repairs.
- **PhysicalUpperWeightBridge source mismatch:** old record source is
  `7c179a6733bd163f5b8e8410a718effa609baa8a10b64b266caa36bf656e77a3`;
  current pre-repair source is
  `6da497eafa6f192bcbc74d25b2c4d88fac4e4e7939e7d48f62fbd26c49163141`.
  The record therefore does not accept these current bytes.

## Minimal repair and static checks

`PhysicalUpperWeightBridge.lean` retains its single-line repair:

```lean
simp only [Finset.sum_const, nsmul_eq_mul]
```

This removes exactly the reported unused `mul_one`; all other file bytes
are unchanged. Its three theorem headers, four definitions, signed coefficient,
coprime correction, and distribution-error terms are unchanged.
RoughPrimeUniverse now replaces only the two reported `simpa ... using ...`
proofs with `simp [roughPrimeUniverse]`. Its 17 theorem headers and two complete
definition blocks remain byte-identical, including the literal endpoint
inequalities and decreasing prime order. The unreported `sortedGT` proof is
untouched. Across both files all 20 theorem headers and six complete definition
blocks remain byte-identical.
This is strict-linter / expression class (1), with no new mathematical step.

`git diff --check` passed. No lint suppression or prohibited proof token was
introduced. No Lean/Lake, cloud job, kernel replay, or commit was performed.

After SHA256, PhysicalUpperWeightBridge:
`eaf69cba7255976ff7fcfb7f5b3016239ecbb5699240ca926adce796e4ecd25c`.
After SHA256, RoughPrimeUniverse:
`21a97074546ea7433a327e7bc500180ec571670c0b47d067426146e6365ce9b0`.
