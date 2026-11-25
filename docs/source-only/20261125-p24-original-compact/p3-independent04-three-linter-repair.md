# P3 independent04: three strict-linter repairs

Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**, 2026-11-25.

The actual input is P3 job `6078d7b5c8ca4730829702dd91ba15cf` at source
`f51e91aad4a63fa5167d8a1377b988db633a817c`. Its log is
`p3-independent-symbolic-04.log`, 11,774 bytes, SHA-256
`41aeff4ba771d4412714a63545957056fed33f17eaad36d5412b6fb0bffa59f7`.

## Existing cache precheck reused

The existing `p2-current-symbolic-source-precheck.json`, SHA-256
`49cf58eea08c6a391883b5a26b844c45101f31b133d31cfe754794a4cdb1b2b4`,
already checks the current 319-module recursive project-source scope
against the original 619-record registry. It classifies:

- `CenterPrimeTail` and `ActualGridEnvelopes` as
  `directly_matching_but_ancestor_blocked_modules`.
- `FirstExitGenericModuli` in
  `direct_failure_groups.source_sha256_mismatch`.

Thus these current sources cannot reuse their old records through the
required exact recursive-source identity gate. This task did not re-extract
the registry, rewalk the graph, check physical objects, or award cache credit.

## Only the three actual diagnostics changed

| Original location | Minimal repair |
|---|---|
| `CenterPrimeTail.lean:112` | Sequence the existing `field_simp` and `ring` on the one goal; remove unnecessary `<;>`. |
| `ActualGridEnvelopes.lean:274` | Replace deprecated `push_neg at hnot` with the diagnostic's current `push Not at hnot`. |
| `FirstExitGenericModuli.lean:44` | Remove only the unused `evenListLength_cons` from the empty-prefix simp list. |

The prime correction identity, crossing-cell complement witness, selected
history parity, list order and all strict/weak boundaries are unchanged.
These are strict-linter/API expression repairs; no new mathematical
estimate, assumption, definition, or proof escape is introduced.

## Source bindings

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/CenterPrimeTail.lean` | `371000889add32a5e24e64784d1b63b4f3544915a20a728390c9ce1134c05073` | `9a00c9770ee599c0370609bf4829e6256997cfe120bff1adcb65ac7c86144847` |
| `ImbalancedChen/ActualGridEnvelopes.lean` | `f2171599b210583ee28b316da48b114c74f8742b564d0c1d3a30aaf073aaf528` | `e791b3990f9dc991471b3ef8c73163c347c5ae07e91bd582f4202df8cc309b4f` |
| `ImbalancedChen/FirstExitGenericModuli.lean` | `15495e6b937f4f94b817ff57a2cdce27d850c16c8c21a8874baef0998378556b` | `5c07ce076a21b4bea3d126e29c4b912292aebc49287d6d7910e7db4713c60620` |

Captured pre-edit text comparisons confirm all 56 theorem headers and all
16 computational declarations are byte-identical, as are imports. Per-file
header/definition counts are 17/2, 18/11 and 21/3. `git diff --check` passes.
No linter was disabled and no `sorry`, `admit`, new axiom, `native_decide`,
or `unsafe` was added. This task ran no compiler or cloud job and did not
stage or commit. The next actual Lean run belongs to root; no new compilation,
kernel, finite-evaluation or P2.4 completion credit is claimed here.
