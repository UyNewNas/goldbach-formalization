import ImbalancedChen.Part5OriginalH430PrimeChildAdmission

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Both original Buchstab directions, at one unchanged physical Q and one
unchanged labelled parent word. The production integer carrier has a
strict ceiling; LocalDomain has a weak ceiling. Their exact difference
is retained as a finite prime fibre, not discarded as a Lebesgue null set.

This file does not supply incomingAllowed/cellMember or a full Program
Member realization. The small upper-parent guard 1 <= argument remains
explicit because it is present in singleDomain but not in LocalDomain.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabCeilingDictionary

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PrimeChildAdmission

/-- The physical local carrier, before imposing the strict integer ceiling. -/
def closedChildren (up : Bool) (N : ℕ) (old : List ℕ) (p : PhysicalNode) :
    Finset (Fin (N+1)) :=
  (primeCandidates N old).filter (fun q =>
    LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q.val))

def ceilingChildren (up : Bool) (N : ℕ) (old : List ℕ) (p : PhysicalNode) :
    Finset (Fin (N+1)) :=
  (closedChildren up N old p).filter (fun q => physicalPrime N q.val = p.ceiling)

theorem mem_closedChildren {up : Bool} {N : ℕ} {old : List ℕ}
    {p : PhysicalNode} {q : Fin (N+1)} :
    q ∈ closedChildren up N old p ↔
      (q.val.Prime ∧ q.val.Coprime (N*parentProduct old)) ∧
      LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q.val) := by
  simp only [closedChildren, primeCandidates, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_ceilingChildren {up : Bool} {N : ℕ} {old : List ℕ}
    {p : PhysicalNode} {q : Fin (N+1)} :
    q ∈ ceilingChildren up N old p ↔
      q ∈ closedChildren up N old p ∧ physicalPrime N q.val = p.ceiling := by
  simp only [ceilingChildren, Finset.mem_filter]

/-- Includes the lower s=2 and square-equality cases. -/
theorem local_geometry {up : Bool} {N q : ℕ} {p : PhysicalNode}
    (h : LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q)) :
    0 < physicalPrime N q ∧ physicalPrime N q ≤ p.ceiling ∧
      2*physicalPrime N q ≤ residual p ∧ residual p/6 ≤ physicalPrime N q := by
  have hg : OneGate p (physicalPrime N q) := by
    cases up
    · exact h.2.2.1
    · exact h.2.1
  have hw : P2EnhancedLowerPhysicalTransition.buchstabArgument p
      (singleCoordinates N q) ≤ 5 := by
    cases up
    · exact h.2.2.2.2
    · exact h.2.2.2
  have hw' : residual p / physicalPrime N q - 1 ≤ 5 := hw
  have hquot : residual p / physicalPrime N q ≤ 6 := by linarith
  have hmul := (div_le_iff₀ hg.1).mp hquot
  exact ⟨hg.1, hg.2.1, hg.2.2, by linarith⟩

/-- Product support follows already for a natural coordinate, before imposing
any finite enumeration cap. -/
theorem local_product_lt_nat {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hlocal : LocalDomain p (singleShape (.buchstab up p.argument))
      (singleCoordinates N q)) :
    ((parentProduct old*q : ℕ) : ℝ) < Q := by
  obtain ⟨hx, _, hsquare, _⟩ := local_geometry hlocal
  have hxL : physicalPrime N q < physicalLevel N Q old := by
    rw [← hL]
    linarith
  have hlogs := parentWindow_logs hw
  have hlog : Real.log (q : ℝ) < Real.log (residualLevel Q old) := by
    exact (div_lt_div_iff_of_pos_right hlogs.1).mp hxL
  have hqR : (q : ℝ) < residualLevel Q old := by
    by_contra h
    have hm := Real.log_le_log (zero_lt_one.trans hlogs.2.1) (le_of_not_gt h)
    exact (not_le_of_gt hlog) hm
  have hB : (0 : ℝ) < parentProduct old := by exact_mod_cast hw.2.1
  have hm := (lt_div_iff₀ hB).mp hqR
  simpa only [Nat.cast_mul, mul_comm] using hm

/-- The finite N+1 enumeration loses no natural local prime. -/
theorem local_prime_le_target {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hlocal : LocalDomain p (singleShape (.buchstab up p.argument))
      (singleCoordinates N q)) : q ≤ N := by
  have hprod : parentProduct old*q ≤ N := by
    have h := (local_product_lt_nat hw hL hlocal).trans_le hw.2.2.2.1
    exact_mod_cast h.le
  have hB : 1 ≤ parentProduct old := hw.2.1
  have hq : q ≤ parentProduct old*q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q hB
  exact hq.trans hprod

theorem natural_local_iff_closedChildren {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) :
    ((q.Prime ∧ q.Coprime (N*parentProduct old)) ∧
      LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q)) ↔
    ∃ r : Fin (N+1), r.val = q ∧ r ∈ closedChildren up N old p := by
  constructor
  · rintro ⟨hq, hlocal⟩
    have hcap := local_prime_le_target hw hL hlocal
    exact ⟨⟨q, by omega⟩, rfl, mem_closedChildren.mpr ⟨hq, hlocal⟩⟩
  · rintro ⟨r, rfl, hr⟩
    exact mem_closedChildren.mp hr

/-- The product support of a weak-ceiling child is derived, not assumed. -/
theorem local_product_lt {up : Bool} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {q : Fin (N+1)}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hq : q ∈ closedChildren up N old p) :
    ((parentProduct old*q.val : ℕ) : ℝ) < Q :=
  local_product_lt_nat hw hL (mem_closedChildren.mp hq).2

/-- Actual native coordinates give a uniform positive prime floor. -/
def primeFloor (N : ℕ) (Q : ℝ) (old : List ℕ) : ℝ :=
  (N : ℝ) ^ (physicalLevel N Q old / 6)

theorem primeFloor_le {up : Bool} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {q : Fin (N+1)}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hq : q ∈ closedChildren up N old p) : primeFloor N Q old ≤ (q.val : ℝ) := by
  obtain ⟨hprime, hlocal⟩ := mem_closedChildren.mp hq
  have hN : (1 : ℝ) < N := by exact_mod_cast hw.1
  have hq0 : (0 : ℝ) < q.val := by exact_mod_cast hprime.1.pos
  have hpow : (N : ℝ) ^ physicalPrime N q.val = (q.val : ℝ) := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hN) hq0).mp
    exact div_mul_cancel₀ _ (Real.log_pos hN).ne'
  have hx := (local_geometry hlocal).2.2.2
  rw [hL] at hx
  rw [primeFloor, ← hpow]
  exact (Real.rpow_le_rpow_left_iff hN).mpr hx

/-- Converse to R14, with exactly the strict ceiling that R14 cannot add. -/
theorem mem_singleChildren_iff {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} {q : Fin (N+1)}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) :
    q ∈ singleChildren (.buchstab up p.argument) N Q old chi ↔
      q ∈ closedChildren up N old p ∧ physicalPrime N q.val < p.ceiling := by
  constructor
  · intro hq
    have h := mem_singleChildren.mp hq
    refine ⟨mem_closedChildren.mpr ⟨h.1, ?_⟩, ?_⟩
    · exact singleChild_LocalDomain hq hL hC rfl
    · simpa only [hC] using h.2.2.2.1
  · rintro ⟨hq, hceil⟩
    obtain ⟨hprime, hlocal⟩ := mem_closedChildren.mp hq
    have hquery := actual_buchstab_argument hw hprime.1 hL
    have hd : singleDomain (.buchstab up p.argument) Q old q.val := by
      cases up
      · change 2 ≤ p.argument ∧
          P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈
            buchstabLowerDomain p.argument
        exact ⟨hlocal.2.1, by simpa only [← hquery] using hlocal.2.2.2⟩
      · change 1 ≤ p.argument ∧
          P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈
            buchstabUpperDomain p.argument
        exact ⟨hs, by simpa only [← hquery] using hlocal.2.2⟩
    exact mem_singleChildren.mpr ⟨hprime, hw, hd, by simpa only [hC] using hceil,
      local_product_lt hw hL hq⟩

theorem closedChildren_eq_union {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) :
    closedChildren up N old p =
      singleChildren (.buchstab up p.argument) N Q old chi ∪ ceilingChildren up N old p := by
  ext q
  rw [Finset.mem_union, mem_singleChildren_iff hw hL hC hs, mem_ceilingChildren]
  constructor
  · intro hq
    have hx := (local_geometry (mem_closedChildren.mp hq).2).2.1
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact Or.inl ⟨hq, hlt⟩
    · exact Or.inr ⟨hq, heq⟩
  · rintro (h | h) <;> exact h.1

theorem strict_disjoint_ceiling {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} (hC : p.ceiling = chi) :
    Disjoint (singleChildren (.buchstab up p.argument) N Q old chi)
      (ceilingChildren up N old p) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have hlt := (mem_singleChildren.mp hq).2.2.2.1
  have heq := (mem_ceilingChildren.mp hc).2
  rw [hC] at heq
  exact (ne_of_lt hlt) heq

/-- Arbitrary signed weights, including weights depending on the whole history. -/
theorem closedChildren_sum {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (F : Fin (N+1) → ℝ) :
    (∑ q ∈ closedChildren up N old p, F q) =
      (∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi, F q) +
      ∑ q ∈ ceilingChildren up N old p, F q := by
  rw [closedChildren_eq_union hw hL hC hs]
  exact Finset.sum_union (strict_disjoint_ceiling hC)

/-- A fixed parent has at most one ceiling prime. It need not have none. -/
theorem ceilingChildren_card_le_one {up : Bool} {N : ℕ} {old : List ℕ}
    {p : PhysicalNode} (hN : 1 < N) : (ceilingChildren up N old p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  have hq' := mem_ceilingChildren.mp hq
  have hr' := mem_ceilingChildren.mp hr
  have hqp := (mem_closedChildren.mp hq'.1).1.1
  have hrp := (mem_closedChildren.mp hr'.1).1.1
  have heq : physicalPrime N q.val = physicalPrime N r.val := hq'.2.trans hr'.2.symm
  apply Fin.ext
  rcases lt_trichotomy q.val r.val with hlt | he | hlt
  · exact False.elim ((ne_of_lt (physicalPrime_strictMono hN hqp hlt)) heq)
  · exact he
  · exact False.elim ((ne_of_lt (physicalPrime_strictMono hN hrp hlt)) heq.symm)

end
end ImbalancedChen.Part5OriginalH430BuchstabCeilingDictionary
