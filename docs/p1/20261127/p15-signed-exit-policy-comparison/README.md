# Signed policy comparison on the actual common tree

## Source and current evidence

This packet continues `ImbalancedChen.P1SignedExitPolicyComparison` with its
**original, unchanged 17,805-byte source**:

`c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f`.

Its only direct import is `ImbalancedChen.P1SignedExitPartition`. The actual
project dependency closure has 41 existing modules; including this new target
gives 42 source modules. Existing dependencies keep their original objects and
acceptance identities.

The exact original source passed the guarded, serialized **no-output probe**
`job_fa097654baec4780b96c1831b24d3c85`. The original result is 8,510 bytes with
SHA256 `9420f76c53b13340ecac36526629bec81f5a843f6745cfdfbcd57879061c052a`.
Its Lean command, outer command, and finished lane all have exit code 0. The
source is unchanged, no output object was requested, no dependency was built,
and the original before/after protection and Git records agree. The 17 original
raw probe files remain the evidence for that probe.

**Formal owner acceptance, owned/public/private counts, and the full-owned
axiom census remain pending the actual normal/kernel/audit results.** The probe
itself grants zero formal owner credit. `POLICY_PUBLICATION_SCOPE_PINS.json`
binds the source, full interface extraction, surrounding source references, and
the original probe records used by this description.

## The exact finite identity

For arbitrary Boolean policies `oldPolicy`, `newPolicy`, arbitrary real local
weights `h`, and a common incoming prefix/sign/mass/carrier, the common policy is

```lean
p1CommonAdmissionPolicy oldPolicy newPolicy positive pre =
  (oldPolicy positive pre && newPolicy positive pre)
```

Let `E` be the original `p1SignedExitStates` list for that common policy, and let
`R_P(s)` denote `firstExitRetainedPolynomial P h` started from the recorded
`s.selectedPrefix`, `s.positive`, `s.mass`, and **`s.remaining`**. Then
`p1_policy_sub_eq_first_different_admissions` proves the exact identity

\[
 F_{\mathrm{new}}-F_{\mathrm{old}}
 =\sum_{\substack{s\in E\\\mathrm{new}(s)=\mathrm{true}\\\mathrm{old}(s)=\mathrm{false}}}
       R_{\mathrm{new}}(s)
  -\sum_{\substack{s\in E\\\mathrm{old}(s)=\mathrm{true}\\\mathrm{new}(s)=\mathrm{false}}}
       R_{\mathrm{old}}(s).
\]

These are sums over occurrences in the original list. The Boolean filters do
not deduplicate exits or replace their remaining carriers. The common tree
follows a selected branch while both policies retain it; at the first rejected
common test, each admitting side supplies its own full continuation. Tests
rejected by both policies contribute zero. The skip branch is counted once at
each recursive stage.

The orientation is always **new minus old**. New-only states include selections
restored after rejection by the old policy; old-only states supply the
subtracted continuations removed by the new policy. Both continuations retain
their actual signs and masses. No policy monotonicity, nonnegative continuation,
or positivity assumption on the real weights is needed for this equality.

`p1_correction_sub_eq_first_different_admissions` gives the same identity for
`firstExitCorrection`: the two root Euler-product terms cancel because the
incoming data and carrier are the same. At each charged state,
`p1_admission_continuation_eq_signed_product_add_exit_sum` further expands the
continuation into its incoming `signedTreeCoefficient` times the Euler product
over **that state's remaining list**, plus its own signed exit sum. The latter
uses the original `p1SignedExitValue`, including its original minus sign.

## Rank support and historical specializations

The source gives the following support statements, with their hypotheses kept:

- If every policy disagreement occurs at selected-prefix length `k`, an
  admission-only state has length exactly `k`.
- If the two policies agree at every prefix of length at most `k`, an
  admission-only state has length strictly greater than `k`. This applies to
  two replacements below the same `firstExitDepthSplicePolicy` parent.
- `fourthCappedUpperPolicy` and `fifthCappedUpperPolicy`, with the same base and
  `Q3`, agree through rank four. Therefore either direction of their first
  different admission has **rank greater than four**. The theorem does not
  assert that the rank is exactly five.

Three final theorems specialize the signed correction identity to the original
third-to-fourth, third-to-fifth, and fourth-to-fifth policies. All three use

```lean
h := fun p : ℕ => 1 / ((p : ℝ) - 1)
pre := []
positive := true
mass := 1
carrier := roughPrimeUniverse N cap 0 z
```

The lower endpoint is literally **0** in these specializations. The carrier is
the decreasing, target-deleted list of primes satisfying `p < cap`, `p ∤ N`,
`0 ≤ (p : ℝ)`, and `(p : ℝ) < z`. The explicit enumeration cap remains present;
this file does not silently remove it or substitute a different rough cutoff.
Each continuation uses the actual unprocessed tail produced by that scan.

The identities are universal in the supplied base policy and level functions
`Q3`, `Q4`, and `Q5`; the rank-four agreement follows from the existing splice
definitions. Arithmetic or analytic admissibility of a chosen level function
is a separate question.

## Position in the original finite chain

| Layer | Mathematical role | Status attributable to this packet |
| --- | --- | --- |
| `P1SignedExitPartition` | Enumerates actual rejected selections with their signed incoming mass and remaining list; identifies correction with the signed exit sum. | Existing accepted prerequisite at its original `7296…` identity. |
| `P1SignedExitPolicyComparison` | Resolves the exact new-minus-old tree/correction difference into both directions of the first different admission, with each side's own continuation. | Exact source probe passed; formal owner audit pending. |
| `P1SignedExitCoefficientDifference` | Introduces one fixed new-minus-old integer Möbius coefficient on the union of retained modulus supports; cancels their intersection, proves the unit bound, and transfers this same first-admission identity to the modulus sum. The prime/Nodup hypotheses remain where the tree-to-modulus transfer requires them. | Downstream source; no acceptance is granted here. |
| `P1HistoricalBoundaryPolicyDifferenceSupport` | From a nonzero fixed coefficient, follows an actual one-sided retained selection to a common-tree first disagreement. Its selected history reverses to a sublist of the same carrier, and its primes belong to that same modulus's `primeFactors`. Boundary-owner restrictions require the stated agreement-away-from-boundary hypothesis. | Downstream source; no acceptance is granted here. |

The present file supplies a signed finite equality. The assertion that **each
nonzero modulus coefficient** has a prime-factor first-disagreement witness is
provided by the subsequent coefficient/boundary layers, not by a new premise
inserted into this equality.

For the actual physical medium coefficient, the accepted historical Dictionary
and the separate source-only `P1OriginalHistoricalFirstDisagreement` bridge are
the further connection: an actual nonzero `trueDDeltaRho` gives a changed rough
factor `b` in the same complete factorization `a * b = d`, while preserving the
original small Rosser attachment and fresh-minus-old order. The bridge lifts
the selected history's primes to the **complete `d`**. That bridge and the
downstream finite sources retain their separate acceptance obligations.

Completing the actual-medium route still requires the same signed physical
coefficient, complete-modulus support, whole-atom grouping, and the relevant
physical/free collision and uniform medium estimates to be connected and
proved. Neither this finite equality nor its rank support supplies those
analytic estimates. The original small-factor sign is not exchanged when a
rough policy changes.

## Source interface and retained acceptance identities

The **lexical source count** is 17 declarations: 3 public `def` declarations and
14 `theorem` declarations, of which 13 are public and one is private. Thus 16
source declarations are non-private. These numbers describe source text only;
they are **not** counts of environment-owned exports, private generated
declarations, or kernel-accepted owners. The complete original declaration
headers, including the `let states` expressions, are recorded in
`POLICY_ORIGINAL_INTERFACE.json`. Whole-file equality to `c6099285…` remains the
source rule; interface extraction authorizes no proof or comment edits.

| Existing owner/context | Original acceptance identity |
| --- | --- |
| Historical coefficient Dictionary | `040d46058821746c69c5183b3f6c22792287c4ba` |
| Prime Mellin profile Variation | `f7e9219f4860a819758d52752c5a9309dd14a8c7` |
| Signed exit Partition, the direct import | `7296a9659fbf34773ec03f437860c14073b3a638` |
| Group-log Abel Variation, a separately accepted owner | `ce08ba304bafb7732c8fd9f27553822f87cfb7d0` |

Only Partition is a direct import of this Policy source. The table preserves
the existing acceptance/context identities; it does not add imports or rebind
any old acceptance to this publication. The two-owner evidence publication at
`19f493948737f6f5f7bc5e858d5266b41f976b22` records Partition and GroupLog under
those original identities.

The source's historical comment calling Partition a source-only sibling is
preserved as part of the unchanged original file. Current prerequisite status
comes from the original accepted Partition receipts, rather than a comment
rewrite.

The original fixed registry stays **18 accepted out of 21 registered**. Existing
additional owners remain separate. This source publication and its no-output
probe do not add a formal owner; subsequent actual owner/audit evidence must
establish that separately. The ShiftedTau repair and the actual coefficient
first-disagreement bridge remain source-only. **The complete P1.5 goal remains
OPEN.**
