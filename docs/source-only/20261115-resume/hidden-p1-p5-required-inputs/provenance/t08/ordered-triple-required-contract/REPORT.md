# Ordered W1 triple: original source located, interface audit only

The exact required PhaseB4 source exists locally. It is not an alias or a new proof:

`goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261028-Certificate-Sol6-Intervals-PhaseB4/P2EnhancedW1OrderedPositiveTripleWord.lean`

Its 13,894 bytes have SHA-256 `2acb72eea087664d8dbc8bb5d24f69e489327b9a12acefb3b4c1a148313e6547`, exactly the direct-import pin in the already published caller's `certificate_triple/REGISTRY.json`. The computed Git blob is `df52b937741c469d9793a764de282e4c9a50ac3f`; this is a content identity, not a claim that the source has been published at a remote commit. The prior locator miss came from searches that skipped hidden/ignored `.lake`. This is an additive correction to the prior P5 validation-selection freeze, which is not changed.

The caller registry itself is bound in `31cce275...` at `docs/source-only/20261028-resume-30/certificate_triple/REGISTRY.json`, blob `10117d9b4bcd4f609fc9590871d3593f446b993f`. Its caller source is blob `26793930dad97e8e14662418ae03867336a55152`, 10,687 bytes, SHA `85db30c268302059456c316c423c7f6b22dcbf47f13852c9e7db68a2001268e2`.

## Exact family and required types

All names below belong to `ImbalancedChen.P2EnhancedW1OrderedPositiveTripleWord`. These are excerpts of the existing source, not newly implemented declarations.

`TripleLabel = (ℕ × ℕ) × ℕ`. Write its slots as q1, q2, q3; B = old.prod; n = (N−ell)/B; and tail = n/(q1*q2*q3). The actual ambient set is `(P.product P).product P`, with `P = eligiblePrimes N ell Q old i j`. Each eligible prime is a prime divisor of n in `[cutoff Q B (W1Anchor j), cutoff Q B (W1Target i))`, coprime to B*N.

The source's `positiveTripleWords` filters that literal product by all of:

- ell belongs to `historyCarrier N B E (cutoff Q B (W1Anchor j))`, preserving the original mask B*N and E B ell;
- ell < N, q1 < q2 < q3, and q1*q2*q3 divides n;
- every prime factor of the exact quotient tail is at least q2.

`repeatedResidual` means a prime r squares into the tail, or divides both the selected triple product and the tail. It concerns the selected triple plus its residual tail; it is not a theorem that every repetition involving the old prefix has been identified. Distinct ordered labels remain separate; no division by 3! or product-only reindexing occurs.

```lean
def repeatedTripleWords (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) : Finset TripleLabel :=
  (positiveTripleWords N ell Q old i j E).filter
    (repeatedResidual N ell old)

theorem repeatedTripleWords_mem_squareEvent {N ell : ℕ} {Q eta : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ repeatedTripleWords N ell Q old i j E)
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)

theorem repeatedTripleWords_card_le_cube (N ell : ℕ) (Q : ℝ)
    (old : List ℕ) (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) :
    (repeatedTripleWords N ell Q old i j E).card ≤
      (eligiblePrimes N ell Q old i j).card^3
```

The event is the existing exact finite set
`(historyCarrier N B E y).filter (fun ell => ell < N ∧ ∃ p, p.Prime ∧ z ≤ (p : ℝ) ∧ p^2 ∣ (N-ell)/B)`.
The membership theorem requires only the displayed membership and physical cutoff premises; it does not add eta positivity, a new Member assumption, or a count estimate. The cube bound has no analytic premise: the source is a subset of the literal triple product.

The existing proof first uses the quotient identity `tripleProduct * tail = n`. A square in the tail then squares into n. A repeated selected prime must be q2 or q3, since q1 < q2 and the tail is q2-rough; it also squares into n. The witness is at least q2 and hence at least the same parent cutoff. This is the intended finite arithmetic argument, and it matches the caller's precise use at lines 61 and 104.

## Caller, sigma and manuscript binding

The global caller sums the cardinal of this same repeated-label fibre over the complete old parent `historyCarrier`. The membership lemma makes each fibre zero outside the same squareEvent. The cube bound combines with the existing eligible-prime bound to give `(1/eta)^3 * card squareEvent`; that eligible-prime bound uses a true positive quotient, parentWindow, eta > 0 and the physical cutoff.

Only after this finite statement does the caller sum with the original nonnegative sigma(B). It requires `old(B).prod = B`, the true parentWindow at each B, and the same physical cutoff, E, Q and action pair `(i(B),j(B))`. The three labels belong to one parent action, not three successive feedback edges. Sigma is deliberately absent from the three primitive declarations and stays unchanged in the caller. Different B receivers need not be disjoint; their original weighted multiplicity remains.

For the asymptotic repeated-residual payment, eta and epsilon are fixed first; the threshold precedes N, Q, chi, D, sigma, E, old and the action maps. Its additional `1 < Q/B ≤ N` premise belongs to the existing Theta payment. The graph caller supplies the physical exponent `(gamma/101^depth)/5` from the actual word/Q-aligned finite parent and positive residual. None of these facts makes all positive switched triples pass every computed History.step or full/selected square gate.

The frozen manuscript was reread: `manuscript-body.tex` 795–817 gives the same positive marked sigma, common Q, exact C(BN)/(phi(B) log(Q/B)), and full/selected/physical-ceiling inheritance. `same-new-level-double-sieve-route.tex` 93–105 has the strictly ordered positive triple and repeated-prime exception; 147–165 gives the exact product B*q1*q2*q3*n and q2-rough tail. Their SHA values remain `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` and `9f8668d74d1af41846dded12f08fd5c96c34e4c4ba37364a52dde8a5e6650fa6`.

## Actual review and readiness status

The source header says SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. The caller's historical registry says manual source/mathematical review only, `compiled=false`, `ready_to_install=false`, `formal_credit=0`. The PhaseB4 directory contains only the Lean file; no separate independent peer AL or compilation receipt was located in the inspected records. The caller's exact dependency pin is real provenance, but is not an independent acceptance AL.

There is one static expression concern to retain for a later authorized compiler/reviewer: in `repeatedTripleWords_square_oldQuotient`, line 150 splits the disjunction with `obtain ... hsquare | ⟨hselected, htail⟩`. The shared `hdata`, `hqprod`, and `hrough` facts are introduced at lines 151–154 before the two bullets, and the second branch later uses them. Ordinary tactic goal scoping may leave those local facts only in the first branch. This is an unexecuted source-reading concern, not a compiler diagnostic or a mathematical counterexample. No source is repaired here. The finite mathematical argument above needs no new hypothesis if the common facts need to be scoped again.

Thus the requested classification is: exact locator resolved; actual source present with full definitions/proof text; interface and same-family intent match; no newly established mathematical gap; possible tactic-expression repair plus unperformed elaboration; no independent ready/acceptance status. There is no basis to synthesize a replacement contract, axiom, stub or new desired assumption.

## Minimal archival proposal

`ARCHIVE_PROPOSAL.json` proposes preserving two previously unlocated Lean sources, without copying or publishing them now:

1. PhaseB4 OrderedPositiveTripleWord, 13,894 bytes, `2acb72ee...`.
2. Its direct PhaseB3 IntegerPrimeGraphStep dependency, 8,635 bytes, `9db8da9b1192afc1b9714ec81ed6cb831e3dab035431c5a43a900e70fb248716`, computed blob `a86e39a5693a0157ab15052b83b7b160b5a72a52`. The existing frozen copy matches; its ready-registry also explicitly has `ready_to_install=false`.

The two PhaseB3 provenance documents should accompany that proposal. The caller registry/report are already committed and can be referenced. Phase9 SquareExceptionPower and the PhaseB2/Phase10/R2 source dependencies already have exact published identities at `19c7759d...`; reference those original bytes instead of making new versions. This is a minimum newly recovered source/provenance proposal, not a new full recursive closure or install plan. No full 451-node graph, MathlibNt locator list or BoxTheta cone was rerun.

Neither source has an explicit license/SPDX declaration in its header. No project-root LICENSE was found in the inspected local root or the current Git tree; the unrelated external-Weil LICENSE does not license these files. Preserve the original task/file provenance and do not invent an Apache or other license declaration.

No source, import, pin or old freeze was changed; no proof/helper/certificate was executed, no remote identity created, and no artifact acquired. Whole ordinary rejectedChild counts remain whole ordinary counts. Root receipt remains the literal if/else with no reverse iff. Full h34, PP, positive K licence and 430/441 realization remain outside this result.
