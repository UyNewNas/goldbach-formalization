# Actual W1 strict complete-product support

Status: **SOURCE_ONLY_UNCOMPILED_PENDING_INDEPENDENT_REVIEW**. One new lemma is proposed for the original integer carrier; no old source is changed. The complete type is stored in `SOURCE_CONTRACT.json` and in the Lean file:

```lean
theorem actual_product_lt
    {N d a1 a2 a3 r : ℕ} {z w : ℝ}
    (ht : (a1, a2, a3) ∈ orderedTriples (primeWindow (d * N) z w))
    (hr : r ∈ roughNumbers
      ((N : ℝ) / ((d * a1 * a2 * a3 : ℕ) : ℝ)) (a2 : ℝ)) :
    d * a1 * a2 * a3 * r < N
```

This is exactly the actual tuple and rough-tail membership interface used in `Part5OriginalH430W1PhysicalRoughDictionary.integerMass` and `Part5OriginalH430BankAfterW1PrimeRestriction.primeRestriction` at19c7759. No alternate chenTriplesCoprime function or carrier is invented: that name was not found in the inspected fixed Wu/project sources. The task's permitted actual-family route uses the real orderedTriples/primeWindow definitions. Original selected/history labels p/l, old word d and their weights are unchanged because the statement applies to each same original labelled member; no set, sum or coefficient is replaced.

The scoped dedup found only an existing inclusive non-strict product gate, not this exact W1 strict terminal. T08 independently confirmed the five original W1 sources plus the bottom-level interfaces have no such terminal in its inspected scope; unsynchronized remote heads are not exhausted. `DEDUP_SEARCH.json` records the scope and distinguishes unrelated U7/other rough carriers. `InclusiveRoughUniform.nonunit_gate_iff` is reused rather than re-proving a generic natural/real product bound.

The source argument extracts a1.Prime and a1.Coprime(d*N) from the first triple coordinate, hence a1.Coprime N. Let D=d*a1*a2*a3. If D=0, the local non-strict bound D*r≤N is immediate. Otherwise locally derived D>0 permits the existing exact gate to convert the original roughNumbers upper bound into D*r≤N. The first prime divides D*r, so equality D*r=N contradicts Nat.Prime.coprime_iff_not_dvd. The two elementary order facts give strictness. The only public premises are the two original memberships: neither F≤N nor F≠N, hd/hN positivity, a receiver test, a nonempty/success condition or an estimate is added.

All unit tails remain: r=1 is not removed and has the original exact one_mem_roughNumbers gate. No squarefree, prime or distinct-factor hypothesis is imposed on r; allowed repeated tail factors remain. Strict order of a1/a2/a3 and their half-open original windows are retained inside ht. Physical N, parent d and the middle-prime cutoff a2 are literal. At N=0, the original primeWindow(d*N,...) has no prime coprime0, so membership is impossible. At d=0 the same mask argument applies, and roughNumbers(N/0,a2) itself has no positive member. The proof covers D=0 locally and needs no new external positivity gate.

All original interface identities and source paths are in `PROVENANCE.json`. FiniteWeights/GoldbachWeights/BuchstabCount have the T08-confirmed fixed09b97 pins. The added InclusiveRoughProduct module is3117B with SHA93769dc…/blob3c3404d…, but **only local exact bytes have been authenticated**: its fixed remote commit:path is not authenticated by the old source selections. This is an explicit dependency-binding HOLD for ROOT, not a fabricated09b97 tree claim. The source-only lemma can receive mathematical/expression review, while full source/physical closure and compatibility remain separate.

The original manuscript mapping is PP256–356, positive-product514–558 and W1 price/unit819–855. The original statement m<N and the retained unit surfaces are consistent with this finite support derivation. No same-rho Delta estimate, admitted-family atlas mapping, PP/h34, true-price transport, near-N collar mass, ordinary predecessor debt, full root receipt,430/441 realization or positive-J/spectral supply follows. Existing old freezes and statuses remain untouched.

Only source text, JSON and hashes were processed; the new Lean file has not been parsed/elaborated/compiled/kernel checked or independently accepted. One theorem, no definitions/axioms, autoImplicit=false and no sorry/admit/native_decide were verified as raw text. NEW_SOURCE.patch is the full addition. No local Lean/Lake/LSP, candidate/helper/stage/setup/guard/fixture, Git/GitHub, artifact acquisition, quota or spawn occurred. ready_to_install=false and formal_credit=0.
