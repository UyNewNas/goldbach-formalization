import ImbalancedChen.P1HistoricalFifthInheritedGateWalls

/-!
# Paying actual historical fifth boundary atoms

The single 18-row strip family contains the actual ten mesh faces, six
historical parent rows and both fifth own-cube caps. Its prime carrier
retains target deletion. A fixed positive strip width is chosen before
the common target threshold. Continuous nullity is never used to delete
an arithmetic boundary atom. Weighted residual replacement requires an
explicit bound for both residual profiles.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators
open P1HistoricalFifthPhysicalGates P1HistoricalFifthAffineWallBoundary
open P1HistoricalFifthInheritedGateWalls

namespace P1HistoricalFifthArithmeticWallPayment

/-- Ten coordinate rows, two separate own-cube rows, then the six actual
parent rows. The root and effective third-ancestor bounds stay distinct. -/
def wallForms : Fin 18 → (Fin 5 → ℝ) →L[ℝ] ℝ :=
  primeIcoBoxGateForms
    (primeOwnCubeGateForms (primeOwnCubeGateForms ordinaryUpperFiveGateForms))

def wallBounds (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Fin 18 → ℝ :=
  primeIcoBoxGateBounds (logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j)
    (logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j)
    (primeOwnCubeGateBounds (D.old5 j : ℝ)
      (primeOwnCubeGateBounds (D.cap5 j : ℝ) (D.fifthParentGateBounds j)))

theorem wallForms_ne_zero : ∀ r, wallForms r ≠ 0 := by
  exact primeIcoBoxGateForms_ne_zero _ (primeOwnCubeGateForms_ne_zero _
    (primeOwnCubeGateForms_ne_zero _ ordinaryUpperFiveGateForms_ne_zero))

theorem complete_walls_subset_strip (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) {delta : ℝ} (hd : 0 ≤ delta) :
    fullBoundaryWalls D j (D.old5 j : ℝ) ∪ fullBoundaryWalls D j (D.cap5 j : ℝ) ⊆
      primeAffineWallStrip wallForms (wallBounds D j) delta := by
  intro t ht
  by_contra hn
  have hne : ∀ r, wallForms r t ≠ wallBounds D j r := by
    intro r heq
    apply hn
    refine ⟨r, ?_⟩
    rw [heq, sub_self, abs_zero]
    exact hd
  have hh : (∀ i, t i ≠ logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j i) ∧
      (∀ i, t i ≠ logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i) ∧
      (∀ r : Fin 8,
        primeOwnCubeGateForms (primeOwnCubeGateForms ordinaryUpperFiveGateForms) r t ≠
          primeOwnCubeGateBounds (D.old5 j : ℝ)
            (primeOwnCubeGateBounds (D.cap5 j : ℝ) (D.fifthParentGateBounds j)) r) := by
    simpa only [wallForms, wallBounds, primeIcoBoxGateForms, primeIcoBoxGateBounds,
      Fin.forall_fin_add, Fin.append_left, Fin.append_right, neg_apply,
      ContinuousLinearMap.proj_apply, ne_eq, neg_inj] using hne
  rcases hh with ⟨hlo, hhi, hrest⟩
  have ho : primeTupleOwnCubeForm t ≠ (D.old5 j : ℝ) := by
    simpa only [primeOwnCubeGateForms, primeOwnCubeGateBounds, Fin.cons_zero,
      primeOwnCubeLinearForm_apply] using hrest 0
  have hn' : primeTupleOwnCubeForm t ≠ (D.cap5 j : ℝ) := by
    simpa only [primeOwnCubeGateForms, primeOwnCubeGateBounds, Fin.cons_succ, Fin.cons_zero,
      primeOwnCubeLinearForm_apply] using hrest (0 : Fin 7).succ
  have hp : ∀ r, ordinaryUpperFiveGateForms r t ≠ D.fifthParentGateBounds j r := by
    intro r
    simpa only [primeOwnCubeGateForms, primeOwnCubeGateBounds, Fin.cons_succ] using
      hrest r.succ.succ
  have hpm : t ∉ parentMeshWalls D j := by
    rintro (⟨i, hi | hi⟩ | ⟨r, hr⟩)
    · exact hlo i hi
    · exact hhi i hi
    · exact hp r hr
  rcases ht with (h | h)
  · rcases h with h | h
    · exact hpm h
    · exact ho h
  · rcases h with h | h
    · exact hpm h
    · exact hn' h

def frontier (D : HistoricalPrefixCapData) (N cap : ℕ) : Finset (Fin 5 → ℕ) :=
  firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))

def replacementDomain (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  (fullClosedPhysicalRegion D j (D.old5 j : ℝ) \ physicalRegion D j (D.old5 j : ℝ)) ∪
    (fullClosedPhysicalRegion D j (D.cap5 j : ℝ) \ physicalRegion D j (D.cap5 j : ℝ))

def discrepancyTuples (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ) : Finset (Fin 5 → ℕ) :=
  (frontier D N cap).filter (fun p => actualPrimeTupleLog N p ∈ replacementDomain D j)

def discrepancyMass (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ) : ℝ :=
  ∑ p ∈ discrepancyTuples D j N cap, ∏ i, 1 / ((p i : ℝ) - 1)

/-- Closing the owner does not lose the global positive lower endpoint.
The upper endpoint comes from the ORIGINAL strict rough-prime carrier. -/
theorem frontier_closedMesh_mem_actualBox (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (hp : p ∈ frontier D N cap)
    (hx : actualPrimeTupleLog N p ∈ closedMeshCell D j) :
    p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) := by
  have hg := (mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4
    (D.upperThirdPolicy (N : ℝ)) N cap 0 _ hcap p).mp hp
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ i, 0 < p i := fun i => (hg.2.1 i).1.pos
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  refine ⟨(hg.2.1 i).1, (hg.2.1 i).2.1, ?_, (hg.2.1 i).2.2.2⟩
  rw [← actualPrimeTupleLog_rpow hN p hpos i]
  apply (Real.rpow_le_rpow_left_iff hNr).mpr
  exact (logPrimeMeshLoHi_bounds (by exact_mod_cast hab) D.m j i).1.trans (hx i).1

theorem discrepancyTuples_subset_strip_carrier (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    {delta : ℝ} (hd : 0 ≤ delta) :
    discrepancyTuples D j N cap ⊆
      (actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ primeAffineWallStrip wallForms (wallBounds D j) delta) := by
  intro p hp
  obtain ⟨hpf, hx⟩ := Finset.mem_filter.mp hp
  have hmesh : actualPrimeTupleLog N p ∈ closedMeshCell D j := by
    rcases hx with h | h
    · exact h.1.1.1
    · exact h.1.1.1
  have hw : actualPrimeTupleLog N p ∈
      fullBoundaryWalls D j (D.old5 j : ℝ) ∪ fullBoundaryWalls D j (D.cap5 j : ℝ) := by
    rcases hx with h | h
    · exact Or.inl (fullClosedPhysicalRegion_diff_subset_walls D j _ h)
    · exact Or.inr (fullClosedPhysicalRegion_diff_subset_walls D j _ h)
  exact Finset.mem_filter.mpr
    ⟨frontier_closedMesh_mem_actualBox D hab j N cap hN hcap p hpf hmesh,
      complete_walls_subset_strip D j hd hw⟩

theorem discrepancyMass_le_stripMass (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    {delta : ℝ} (hd : 0 ≤ delta) :
    discrepancyMass D j N cap ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) wallForms (wallBounds D j) delta := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (discrepancyTuples_subset_strip_carrier D hab j N cap hN hcap hd)
  intro p hp _
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- One width for all 18 rows, both caps and every later target/carrier
cap. The actual prime factor exclusion is inherited from the supplier. -/
theorem exists_discrepancyMass_lt (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        actualPrimeAffineWallStripMass N (fun _ : Fin 5 => (D.a : ℝ))
            (fun _ => (D.b : ℝ)) wallForms (wallBounds D j) delta < epsilon ∧
          discrepancyMass D j N cap < epsilon := by
  obtain ⟨delta, hd, N₀, hN₀, hpay⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by exact_mod_cast ha) (by exact_mod_cast hab) wallForms (wallBounds D j)
    wallForms_ne_zero epsilon he
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N cap hN hc
  exact ⟨hpay N hN,
    (discrepancyMass_le_stripMass D hab j N cap (by omega) hc hd.le).trans_lt (hpay N hN)⟩

private theorem frontierWeight_nonneg (D : HistoricalPrefixCapData)
    (N cap : ℕ) {p : Fin 5 → ℕ} (hp : p ∈ frontier D N cap) :
    0 ≤ ∏ i, 1 / ((p i : ℝ) - 1) := by
  have hg := (mem_actualPrimeFrontierTuples_iff 4 (D.upperThirdPolicy (N : ℝ))
    N cap 0 ((N : ℝ) ^ (D.b : ℝ)) p).mp hp
  apply Finset.prod_nonneg
  intro i _
  have hpi : (1 : ℝ) < p i := by exact_mod_cast (hg.2.1 i).2.1.one_lt
  exact (one_div_pos.mpr (sub_pos.mpr hpi)).le

theorem discrepancyMass_nonneg (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ) :
    0 ≤ discrepancyMass D j N cap := by
  apply Finset.sum_nonneg
  intro p hp
  exact frontierWeight_nonneg D N cap (Finset.mem_filter.mp hp).1

private theorem indicator_change_eq_diff (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda value : ℝ) (t : Fin 5 → ℝ) :
    (if t ∈ fullClosedPhysicalRegion D j lambda then value else 0) -
        (if t ∈ physicalRegion D j lambda then value else 0) =
      if t ∈ fullClosedPhysicalRegion D j lambda \ physicalRegion D j lambda then value else 0 := by
  by_cases hs : t ∈ physicalRegion D j lambda
  · have hc := physicalRegion_subset_fullClosed D j lambda hs
    simp [hs, hc]
  · by_cases hc : t ∈ fullClosedPhysicalRegion D j lambda <;> simp [hs, hc]

def strictProfileSum (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ frontier D N cap, (∏ i, 1 / ((p i : ℝ) - 1)) *
    ((if actualPrimeTupleLog N p ∈ physicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0) -
      (if actualPrimeTupleLog N p ∈ physicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0))

def closedProfileSum (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ frontier D N cap, (∏ i, 1 / ((p i : ℝ) - 1)) *
    ((if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0) -
      (if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0))

def pointReplacementError (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) (p : Fin 5 → ℕ) : ℝ :=
  (if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.cap5 j : ℝ) \
    physicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0) -
  (if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.old5 j : ℝ) \
    physicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0)

theorem pointReplacementError_outside (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) (p : Fin 5 → ℕ)
    (hp : actualPrimeTupleLog N p ∉ replacementDomain D j) :
    pointReplacementError D j N oldProfile newProfile p = 0 := by
  have ho : actualPrimeTupleLog N p ∉ fullClosedPhysicalRegion D j (D.old5 j : ℝ) \
      physicalRegion D j (D.old5 j : ℝ) := fun h => hp (Or.inl h)
  have hn : actualPrimeTupleLog N p ∉ fullClosedPhysicalRegion D j (D.cap5 j : ℝ) \
      physicalRegion D j (D.cap5 j : ℝ) := fun h => hp (Or.inr h)
  simp only [pointReplacementError, if_neg hn, if_neg ho, sub_self]

/-- Exact finite reindexing of the signed strict/closed replacement.
No discrete wall is removed; its contribution is isolated explicitly. -/
theorem profileSum_difference_eq_discrepancy_sum (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) :
    closedProfileSum D j N cap oldProfile newProfile -
        strictProfileSum D j N cap oldProfile newProfile =
      ∑ p ∈ discrepancyTuples D j N cap, (∏ i, 1 / ((p i : ℝ) - 1)) *
        pointReplacementError D j N oldProfile newProfile p := by
  unfold closedProfileSum strictProfileSum
  rw [← Finset.sum_sub_distrib]
  unfold discrepancyTuples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  have ho := indicator_change_eq_diff D j (D.old5 j : ℝ) (oldProfile p) (actualPrimeTupleLog N p)
  have hn := indicator_change_eq_diff D j (D.cap5 j : ℝ) (newProfile p) (actualPrimeTupleLog N p)
  have heq :
      (∏ i, 1 / ((p i : ℝ) - 1)) *
          ((if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0) -
            (if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0)) -
      (∏ i, 1 / ((p i : ℝ) - 1)) *
          ((if actualPrimeTupleLog N p ∈ physicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0) -
            (if actualPrimeTupleLog N p ∈ physicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0)) =
        (∏ i, 1 / ((p i : ℝ) - 1)) * pointReplacementError D j N oldProfile newProfile p := by
    unfold pointReplacementError
    rw [← hn, ← ho]
    ring
  rw [heq]
  by_cases hx : actualPrimeTupleLog N p ∈ replacementDomain D j
  · rw [if_pos hx]
  · rw [if_neg hx, pointReplacementError_outside D j N oldProfile newProfile p hx, mul_zero]

theorem pointReplacementError_abs_le (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) (p : Fin 5 → ℕ)
    (B : ℝ) (hB : 0 ≤ B) (ho : |oldProfile p| ≤ B) (hn : |newProfile p| ≤ B) :
    |pointReplacementError D j N oldProfile newProfile p| ≤ 2 * B := by
  unfold pointReplacementError
  have htriangle (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le x 0 y)
  apply (htriangle _ _).trans
  have h1 : |if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.cap5 j : ℝ) \
      physicalRegion D j (D.cap5 j : ℝ) then newProfile p else 0| ≤ B := by
    split_ifs
    · exact hn
    · simpa only [abs_zero] using hB
  have h2 : |if actualPrimeTupleLog N p ∈ fullClosedPhysicalRegion D j (D.old5 j : ℝ) \
      physicalRegion D j (D.old5 j : ℝ) then oldProfile p else 0| ≤ B := by
    split_ifs
    · exact ho
    · simpa only [abs_zero] using hB
  linarith

/-- A real residual coefficient bound is a separate displayed premise.
Unbounded coefficients cannot be paid merely by a small boundary mass. -/
theorem profileSum_difference_abs_le_mass (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ)
    (oldProfile newProfile : (Fin 5 → ℕ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ho : ∀ p ∈ frontier D N cap, |oldProfile p| ≤ B)
    (hn : ∀ p ∈ frontier D N cap, |newProfile p| ≤ B) :
    |closedProfileSum D j N cap oldProfile newProfile - strictProfileSum D j N cap oldProfile newProfile| ≤
      (2 * B) * discrepancyMass D j N cap := by
  rw [profileSum_difference_eq_discrepancy_sum]
  calc
    _ ≤ ∑ p ∈ discrepancyTuples D j N cap,
        |(∏ i, 1 / ((p i : ℝ) - 1)) * pointReplacementError D j N oldProfile newProfile p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ discrepancyTuples D j N cap, (∏ i, 1 / ((p i : ℝ) - 1)) * (2 * B) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpf := (Finset.mem_filter.mp hp).1
      have hw := frontierWeight_nonneg D N cap hpf
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left
        (pointReplacementError_abs_le D j N oldProfile newProfile p B hB (ho p hpf) (hn p hpf)) hw
    _ = (2 * B) * discrepancyMass D j N cap := by
      unfold discrepancyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- The same fixed delta/N0 pays the actual 18-row strip AND every
strict/closed profile replacement with the supplied uniform bound B. -/
theorem exists_profile_replacement_payment (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (B : ℝ) (hB : 0 ≤ B) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        actualPrimeAffineWallStripMass N (fun _ : Fin 5 => (D.a : ℝ))
          (fun _ => (D.b : ℝ)) wallForms (wallBounds D j) delta < epsilon / (2 * B + 1) ∧
        ∀ oldProfile newProfile : (Fin 5 → ℕ) → ℝ,
          (∀ p ∈ frontier D N cap, |oldProfile p| ≤ B) →
          (∀ p ∈ frontier D N cap, |newProfile p| ≤ B) →
          |closedProfileSum D j N cap oldProfile newProfile -
            strictProfileSum D j N cap oldProfile newProfile| < epsilon := by
  have hd : 0 < 2 * B + 1 := by positivity
  obtain ⟨delta, hdelta, N₀, hN₀, hpay⟩ := exists_discrepancyMass_lt D ha hab j
    (epsilon / (2 * B + 1)) (div_pos he hd)
  refine ⟨delta, hdelta, N₀, hN₀, ?_⟩
  intro N cap hN hc
  obtain ⟨hs, hm⟩ := hpay N cap hN hc
  refine ⟨hs, ?_⟩
  intro oldProfile newProfile ho hn
  have hb := profileSum_difference_abs_le_mass D j N cap oldProfile newProfile B hB ho hn
  have hm0 := discrepancyMass_nonneg D j N cap
  have hscaled := (lt_div_iff₀ hd).mp hm
  nlinarith

/-- The strict profile aggregate really is the literal arithmetic
old/new residual difference on the same historical joint cell. -/
theorem strict_actual_profileSum_eq_residual_sum (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ) (hN : 1 < N) :
    strictProfileSum D j N cap
        (actualUngatedResidual N cap (D.old5 j : ℝ))
        (actualUngatedResidual N cap (D.cap5 j : ℝ)) =
      ∑ p ∈ frontier D N cap, (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ jointCell D j then
          actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p else 0) := by
  unfold strictProfileSum
  apply Finset.sum_congr rfl
  intro p hp
  have hg := (mem_actualPrimeFrontierTuples_iff 4 (D.upperThirdPolicy (N : ℝ))
    N cap 0 ((N : ℝ) ^ (D.b : ℝ)) p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hg.2.1 i).2.1.pos
  apply congrArg (fun v : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * v)
  simpa only [physicalDifference, Set.indicator] using
    (actual_residual_difference_gate_dictionary D j N cap hN p hpos).symm

/-- Literal old/new physical residual coefficients from the first draft.
Their uniform bounds are intentionally required, rather than inferred
from the nullity of any continuous boundary. -/
theorem exists_actual_residual_replacement_payment (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (B : ℝ) (hB : 0 ≤ B) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        actualPrimeAffineWallStripMass N (fun _ : Fin 5 => (D.a : ℝ))
          (fun _ => (D.b : ℝ)) wallForms (wallBounds D j) delta < epsilon / (2 * B + 1) ∧
        ((∀ p ∈ frontier D N cap, |actualUngatedResidual N cap (D.old5 j : ℝ) p| ≤ B) →
         (∀ p ∈ frontier D N cap, |actualUngatedResidual N cap (D.cap5 j : ℝ) p| ≤ B) →
          |closedProfileSum D j N cap
              (actualUngatedResidual N cap (D.old5 j : ℝ))
              (actualUngatedResidual N cap (D.cap5 j : ℝ)) -
            strictProfileSum D j N cap
              (actualUngatedResidual N cap (D.old5 j : ℝ))
              (actualUngatedResidual N cap (D.cap5 j : ℝ))| < epsilon) := by
  obtain ⟨delta, hd, N₀, hN₀, hp⟩ := exists_profile_replacement_payment D ha hab j B hB epsilon he
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N cap hN hc
  obtain ⟨hs, heq⟩ := hp N cap hN hc
  exact ⟨hs, heq _ _⟩

end P1HistoricalFifthArithmeticWallPayment

end

end ImbalancedChen
