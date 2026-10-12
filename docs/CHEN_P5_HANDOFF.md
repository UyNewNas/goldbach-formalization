# Part 5 handoff: eleven-term mean ledger and independent candidates

> **Round 2 update:** the actual Buchstab theorem, complete finite eleven-term
> ledger, lower-scale module, and actual InitialSource component have now
> passed strict trust-zero frontend
> compilation, bundled kernel replay, and the defining-module transitive
> axiom audit. See [CHEN_P5_ROUND2_HANDOFF.md](CHEN_P5_ROUND2_HANDOFF.md) for
> their actual receipts and the separately labelled first-row mean candidate,
> and [CHEN_P5_BUCHSTAB_HANDOFF.md](CHEN_P5_BUCHSTAB_HANDOFF.md) for the
> independent Part 2 delivery. The rest of this document records the fixed
> first-round status at the commits below; its unexecuted gates are
> historical and do not supersede the round-2 receipts.

## Fixed identity and delivery status (historical first round)

**This is a staged candidate delivery. The complete adopted-mask mean and
the final `hLower` are still open. No successful Lean elaboration, kernel
replay, or transitive axiom audit was obtained in this environment.**

| Item | Fixed value |
| --- | --- |
| Repository | `UyNewNas/goldbach-formalization` |
| Branch | `chatgpt/chen-p5-lower` |
| Proof-source commit | [`3857bfe99b6a7adbb0c3c0443b27b99d96a44f86`](https://github.com/UyNewNas/goldbach-formalization/commit/3857bfe99b6a7adbb0c3c0443b27b99d96a44f86) |
| Proof-source Git tree | `59e244baaf891c24a6b0feeded08ece705f8e431` |
| Parent / unchanged proof baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Source branch at the baseline | `codex/variable-envelope-boxes` |
| Frozen manuscript commit | `ba6ec11d800eccc54406490631895e174de85766` |
| Main-body Git blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| Current count constant | `currentC = 49044063 / 25000000` |
| Required common density constant | `currentK = 8452171 / 1250000` |

The proof-source commit adds seven files. This handoff is a subsequent
documentation-only addition; it does not change those proof sources.
The delivery receipt gives the branch's final full SHA. Both commits are
descendants of the user-specified baseline; no other Part was merged.

| Requested stage | Status at this source commit |
| --- | --- |
| Complete eleven-row requirements ledger | Written and statically checked against the frozen definitions and manuscript |
| Independent lemmas | Candidate proof sources for finite identities, exact error budgets, and a genuine Buchstab lower barrier |
| Complete actual adopted-mask mean | Open: actual policy, mask, integral certificates, and distribution estimates are not assembled |
| Final `hLower` with the common `c` | Open: no unconditional lower-count theorem is introduced |

## Files and complete theorem types

| File | Content and acceptance boundary |
| --- | --- |
| [CurrentChenMeanLedger.lean](../ImbalancedChen/CurrentChenMeanLedger.lean) | Exact complement-filter identities, all eleven actual prime-source sums, moving-cutoff Fubini, full signed identity, correctly oriented finite assembly, and a joint `U10 + U11` interface |
| [CurrentChenLowerScale.lean](../ImbalancedChen/CurrentChenLowerScale.lean) | Finite factor-four conversion and error allocation; no analytic mean supplier |
| [CurrentChenBuchstabRefinement.lean](../ImbalancedChen/CurrentChenBuchstabRefinement.lean) | Candidate proof for the actual pinned Buchstab function on the entire tail `s >= 7/3` |
| [CHEN_P5_MEAN_LEDGER.md](CHEN_P5_MEAN_LEDGER.md) | Every support, coefficient, cutoff, estimate direction, same-mask constraint, source binding, and remaining producer obligation |
| [CHEN_P5_DECLARATION_TYPES.txt](../verification/parts/p5/CHEN_P5_DECLARATION_TYPES.txt) | Complete source-extracted declaration signatures, including the private helper; explicitly not elaborator output |
| [ChenP5Audit.lean](../verification/parts/p5/ChenP5Audit.lean) | Defining-module inventory and complete elaborated types, with transitive axiom checks, when executed successfully |
| [chen-p5-source-review.json](../verification/parts/p5/chen-p5-source-review.json) | Source hashes, comment/string-aware prohibited-construct scan, and explicit unexecuted Lean gates |

These three new leaf-module names and the two Part 5 documents are
registered here for Part 0 integration. Auxiliary verification files live
under `verification/parts/p5/`. Existing modules, the shared root,
`CurrentMainTheorem.lean`, `CurrentNumericalTransfer.lean`, both workflows,
the toolchain, and both Lake configuration files are unchanged.

The source inventory contains 16 definitions and 43 theorem declarations,
including one private theorem. This is a source count, not a Lean
environment inventory or a measure of completion of the analytic task.

| Proof source | SHA-256 |
| --- | --- |
| `CurrentChenMeanLedger.lean` | `ab659310c2dca5400a6ffedc3790e1435187dc98b29e861cf273d95395005183` |
| `CurrentChenLowerScale.lean` | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` |
| `CurrentChenBuchstabRefinement.lean` | `8a9352e999496160e3093b38cd1e6472468b27deac1315f85752c9133d3c3e0b` |

### Principal finite identity

In `namespace ImbalancedChen`, the candidate theorem's complete type is:

```lean
theorem currentChenPairedPrimeSum_eq_upsilon (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
        currentChenUpsilon4 N + currentChenUpsilon5 N + currentChenUpsilon6 N E -
        2 * currentChenUpsilon7 N - currentChenUpsilon8 N - currentChenUpsilon9 N -
        currentChenUpsilon10 N - currentChenUpsilon11 N E
```

The six and eleven definitions use the complement of the same `E`, on
`(p1,p2)` and `(p3,p4)` respectively. Every outer sum uses
`chenAdditivePrimeCarrier N`. Reindexing preserves tuple multiplicities
and the literal natural quotient; it does not require squarefreeness.
The existing paired injection retains its own squarefree hypothesis.

### Independent analytic candidate

```lean
theorem currentChen_buchstab_eleven_twentieths {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

The proof uses the actual logarithmic formula on `[7/3,3]`, the delay
integral and the proved global `1/2` bound on `[3,10/3]`, then propagates
the barrier from a complete unit interval to the whole tail. It assumes
neither sampled values nor monotonicity of the Buchstab function. It can
be consumed by the paired-fibre soundness work after verification; it
does not certify the full numerical quadrature or the mean.

## Scale and signs to preserve during integration

For `W_N = currentChenPairedPrimeSum N (E N)` and
`H_N = singularNormalization N`, the unchanged baseline gives

\[
W_N\le 4D_{1,2}(N)+246\frac{N}{N^{417/5000}-1}+4.
\]

Its normalized error theorem is uniform over `E` after the large-`N`
threshold. Thus it applies to the actual `N`-dependent adopted mask.
The missing lower mean must have weight-scale coefficient

\[
4c=\frac{49044063}{6250000}=7.84705008.
\]

The signed vector is `(3,1,-1,-1,1,1,-2,-1,-1,-1,-1)`. Its absolute sum
is 14. Bounds below on rows 1, 2, 5, 6 and above on rows 3, 4, 7, 8, 9,
10, 11 give a loss of `14 * delta * H_N`. The joint last-row adapter uses
`(b1011 + 2*delta) * H_N`, preserving that same budget without inventing
independent numerical endpoints for rows 10 and 11.

After the actual oriented estimates have been proved, take
`delta = epsilon / 7`. The mean loses `2*epsilon*H_N`; the existing
count bridge can take another `2*epsilon*H_N`. Division by four then
gives exactly the requested count loss `epsilon*H_N`.

The finite budget lemma explicitly retains its displayed one-`N`
inequality premises. No theorem accepts the entire missing eventual
mean and presents itself as an unconditional `hLower` proof.

The adopted `7/3` refinement replaces the older `12/5` candidate. The
older gain is not added again. The exact scalar reserve check in the
ledger has a positive gap of about `4.906122464e-9`; this is rational
arithmetic, not a proof that the actual lower integral attains that gap.

## Read-only review of other Parts

Part 0's document-only commit
[`9fe1d6b8b68a97cad3a122410ad7fde1701eed35`](https://github.com/UyNewNas/goldbach-formalization/blob/9fe1d6b8b68a97cad3a122410ad7fde1701eed35/docs/CHEN_175_BASELINE_INTERFACES.md)
was read for interface alignment. It keeps the original proof baseline.
The user has not supplied a replacement proof baseline, so this delivery
continues to use the original full SHA.

Part 2 was reviewed at the fixed commit
[`195f19cfcedeaf7793ccce3f1d42d27fcfe4f815`](https://github.com/UyNewNas/goldbach-formalization/commit/195f19cfcedeaf7793ccce3f1d42d27fcfe4f815).
Its [PairedV2 source](https://github.com/UyNewNas/goldbach-formalization/blob/195f19cfcedeaf7793ccce3f1d42d27fcfe4f815/ImbalancedChen/Certificates/PairedV2.lean)
provides the first E0 cell, ordinal zero, indices `(422,510)`, with the
candidate real-integral bounds

```lean
-- In namespace ImbalancedChen.Certificates.PairedV2:
theorem firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤ firstIntegral ∧
      firstIntegral ≤ (31704 / 1000000000000 : ℝ)
```

That integral is genuinely defined by an iterated integral and already
contains `K/80`: it is in Chen-quarter units. Its coordinate dictionary
is `(t,u,z,w) = (log_N p4, log_N p3, log_N p2, log_N p1)`. Accordingly
its outer pair matches this ledger's `E (p3,p4)`. The local functional
comparison with the restrictable parent and the joint negative terms
must still be proved before this contribution enters the full mean.

The first cell is not the full mask. The complete `6091 + 11481 = 17572`
cells, their Lean aggregation, saved-floor payments, and the complete
global lower certificate were not provided by that Part 2 commit. Its
source is also awaiting successful execution: the observed dedicated
[run 38193423556](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193423556)
failed without reported executed steps. This Part 5 branch does not
import or merge those unverified Part 2 files.

## Remaining producers and receivers

| Producer -> receiver | Exact remaining obligation |
| --- | --- |
| Part 1 -> Part 5, Part 2 | Actual current lower policies at `a` and `h`; historical joint supports and integrals; inherited legality, own-cube bounds, restoration, and finite feedback semantics |
| Part 2 -> Part 5, Part 0 | Full adopted `E0/E1` data and log pullback; complete retained/removed region checks; real-integral certificates, H430/H248/h248 semantics, same-mask-v2 gain and discarded-floor budget |
| Part 3 -> Part 5 | Actual prime/selected-quotient distribution estimates for the licensed physical signed families, with common intervals, phases, moving residues, complete moduli, and all-even thresholds |
| Part 4-A -> Part 5, Part 3 | The same actual `rho` construction, pointwise majorant, support and coefficient controls, and the density theorem with `K = 8452171/1250000` |
| Part 5 using Part 4-A + Part 3 -> Part 5 mean | General positive switched-family upper bridge, with actual marked-product masses and the same `rho`; density `K` alone does not give rows 7-11 |
| Part 5 pure definitions -> Part 2 lower certificate | Freeze the complete actual continuous lower functional once the actual Part 1 policy/integral data are fixed; the current finite-row definitions are not a substitute for that integral functional |
| Part 5 -> Part 0 | Prove every oriented actual row estimate, or the stated joint last-row estimate; assemble the full adopted-mask mean at weight coefficient `4*c`; derive final `hLower` |

The final missing export is exactly the following target, which is not
declared as a theorem in this delivery:

```lean
theorem current_D12_lower :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

Part 5 has no dependency on Part 4-B's `hUpper`. After receiving Part 4-A,
the actual positive-family insertion and remaining row estimates still
need proof before the shared constant can be closed.

## Executed verification and unexecuted gates

| Check | Observed result |
| --- | --- |
| Baseline provenance | All 303 original files were checked against the fixed Git blob tree |
| Scope and tree | Seven additive files only at the proof-source commit; local staged tree equals the remote Git tree exactly |
| Source review | No `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, or `skip` tokens in the three proof modules after removing comments and strings; no whitespace errors in `git diff --cached --check` |
| Mathematical review | All eleven supports/signs, tuple cutoffs, same-mask mapping, factor four, joint last-row budget, rational reserves, and the Buchstab argument were statically reviewed |
| Local compiler | Exact pinned Lean 4.33.0-rc1 and dependencies acquired; compiler startup fails with `error: failed to locate application`, before elaboration |
| Local diagnosis | Pinned runtime uses `/proc/<pid>/exe`; reading that own-process path was denied in this environment. No permission mechanism was bypassed |
| Lean module elaboration | Not completed; candidate status retained |
| Kernel replay | Not executed |
| Transitive axiom audit | Not executed; source scan is not a substitute |

The exact proof-source commit has these observed GitHub Actions results:

| Workflow | Run | Job | Conclusion and execution evidence |
| --- | --- | --- | --- |
| Lean core verification | [38194422260](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194422260) | `114633858607` | `failure`; API returned `steps: null`, `logs_url: null` |
| Variable envelope verification | [38194422273](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194422273) | `114633858591` | `failure`; API returned `steps: null`, `logs_url: null` |

These failures do not identify a specific infrastructure cause or show
a Lean diagnostic. The shared aggregate entry point is unchanged and
does not import the new modules. Even a successful inherited aggregate
run would therefore not establish verification of these candidates.

Part 0 should run the explicit targets with the unchanged pins:

```sh
lake --wfail build ImbalancedChen.CurrentChenMeanLedger ImbalancedChen.CurrentChenLowerScale ImbalancedChen.CurrentChenBuchstabRefinement
lake env lean verification/parts/p5/ChenP5Audit.lean
lake env leanchecker --verbose ImbalancedChen.CurrentChenMeanLedger
lake env leanchecker --verbose ImbalancedChen.CurrentChenLowerScale
lake env leanchecker --verbose ImbalancedChen.CurrentChenBuchstabRefinement
```

The audit enumerates defining-module declarations, including private and
generated declarations, prints their complete elaborated types, and
rejects unsafe declarations, axiom declarations, or transitive axioms
outside `propext`, `Classical.choice`, and `Quot.sound`. It must actually
run successfully before any axiom-clean claim is accepted.

After these gates pass, Part 0 can integrate the three explicit imports
and execute the canonical full build, kernel replay, and axiom audit.
This handoff neither changes those gates nor records them as passed.
