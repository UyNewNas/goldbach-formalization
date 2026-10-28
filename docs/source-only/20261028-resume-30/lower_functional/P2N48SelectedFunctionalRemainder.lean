import ImbalancedChen.P2N48ActualSelectedRhoCoefficient

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The literal n48 geometric key, rather than the source ordinal, determines
one half-open logarithmic parent. Different keys have disjoint selected
parents: the low U10 band is unmasked and the high U11 band retains the
original adopted paired complement. This gives exact finite additivity
for a key-injective family of original archive rows.

The cost on the UNcovered part of the true joint domain is retained in
all full-functional identities. In particular, a bound for selected rows
alone is never promoted to an upper bound for the whole negative term.
The actual archive's key-injectivity and the missing complement's upper
certificate are not asserted or computed in this file.
-/

namespace ImbalancedChen.P2N48SelectedFunctionalRemainder

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalSixteenU10Geometry
open P5Z.U1011OriginalJointHarmonic

/-- The original box key excludes method, floor and source ordinal.
Two records with different ordinals can still encode the same box. -/
def rowKey (r : SourceRow) : Fin 2 × Fin 48 × Fin 48 × Fin 48 × Fin 48 :=
  (r.term, r.ix, r.iy, r.iz, r.iw)

def actualMask : Set (ℝ × ℝ) :=
  Certificates.PairedV2.FullMask.P1E0E1.pairRegion

def actualDomain : Set LogFour := domain10 ∪ originalDomain actualMask

def actualKernel : LogFour → ℝ :=
  P5Z.U1011OriginalJointHarmonic.weighted

/-- An exact discrete ownership obligation. This is not implied by
NoDup ordinals or by a saved numerical total. -/
def DistinctGeometricKeys (S : Finset SourceRow) : Prop :=
  ∀ r ∈ S, ∀ s ∈ S, rowKey r = rowKey s → r = s

private theorem affine_bin_separation (a d i j : ℕ) (hij : i < j) :
    ((a + d * i + d : ℕ) : ℝ) / 240000 ≤
      ((a + d * j : ℕ) : ℝ) / 240000 := by
  have hstep : i + 1 ≤ j := by omega
  have hmul := Nat.mul_le_mul_left d hstep
  have hnat : a + d * i + d ≤ a + d * j := by nlinarith only [hmul]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by norm_num)

/-- Half-open endpoints give uniqueness even on grid walls. -/
private theorem affine_bin_unique (a d : ℕ) (i j : Fin 48) (x : ℝ)
    (hi : ((a + d * i.val : ℕ) : ℝ) / 240000 ≤ x ∧
      x < ((a + d * i.val + d : ℕ) : ℝ) / 240000)
    (hj : ((a + d * j.val : ℕ) : ℝ) / 240000 ≤ x ∧
      x < ((a + d * j.val + d : ℕ) : ℝ) / 240000) : i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (not_lt_of_ge (hj.1.trans' (affine_bin_separation a d _ _ hlt))) hi.2
  · exact (not_lt_of_ge (hi.1.trans' (affine_bin_separation a d _ _ hgt))) hj.2

/-- A point in two actual selected parents has the same original box key.
The term comparison uses the true low/high domains; no rectangular
surrogate is substituted for the ordered simplex. -/
theorem rowKey_eq_of_mem_selectedParent {r s : SourceRow} {v : LogFour}
    (hr : v ∈ selectedParent r actualMask)
    (hs : v ∈ selectedParent s actualMask) : rowKey r = rowKey s := by
  have hzero : r.term.val = 0 ↔ s.term.val = 0 := by
    constructor
    · intro hr0
      by_contra hs0
      have h10 : v ∈ domain10 := by
        exact (show v ∈ nativeBox r ∩ domain10 by
          simpa [selectedParent, hr0] using hr).2
      have h11 : v ∈ originalDomain actualMask := by
        exact (show v ∈ nativeBox s ∩ originalDomain actualMask by
          simpa [selectedParent, hs0] using hs).2
      exact (Set.disjoint_left.mp (domain10_disjoint_originalDomain actualMask)) h10 h11
    · intro hs0
      by_contra hr0
      have h10 : v ∈ domain10 := by
        exact (show v ∈ nativeBox s ∩ domain10 by
          simpa [selectedParent, hs0] using hs).2
      have h11 : v ∈ originalDomain actualMask := by
        exact (show v ∈ nativeBox r ∩ originalDomain actualMask by
          simpa [selectedParent, hr0] using hr).2
      exact (Set.disjoint_left.mp (domain10_disjoint_originalDomain actualMask)) h10 h11
  have ht : r.term = s.term := by
    apply Fin.ext
    have hrlt := r.term.isLt
    have hslt := s.term.isLt
    by_cases hr0 : r.term.val = 0
    · have hs0 := hzero.mp hr0
      omega
    · have hs0 : s.term.val ≠ 0 := fun h => hr0 (hzero.mpr h)
      omega
  have hrBox : ∀ j : Fin 4,
      (leftEnd r j : ℝ) / 240000 ≤ v j ∧
        v j < (rightEnd r j : ℝ) / 240000 := by
    exact mem_logPrimeBox.mp hr.1
  have hsBox : ∀ j : Fin 4,
      (leftEnd s j : ℝ) / 240000 ≤ v j ∧
        v j < (rightEnd s j : ℝ) / 240000 := by
    exact mem_logPrimeBox.mp hs.1
  have hix : r.ix = s.ix := by
    by_cases hr0 : r.term.val = 0
    · have hs0 := hzero.mp hr0
      apply affine_bin_unique (417 * 48) 343 r.ix s.ix (v 0)
      · simpa [leftEnd, rightEnd, width, lowLo, highLo, hr0] using hrBox 0
      · simpa [leftEnd, rightEnd, width, lowLo, highLo, hs0] using hsBox 0
    · have hs0 : s.term.val ≠ 0 := fun h => hr0 (hzero.mpr h)
      have hr1 : r.term.val = 1 := by have := r.term.isLt; omega
      have hs1 : s.term.val = 1 := by have := s.term.isLt; omega
      apply affine_bin_unique (760 * 48) 420 r.ix s.ix (v 0)
      · simpa [leftEnd, rightEnd, width, lowLo, highLo, hr0, hr1] using hrBox 0
      · simpa [leftEnd, rightEnd, width, lowLo, highLo, hs0, hs1] using hsBox 0
  have hiy : r.iy = s.iy := by
    apply affine_bin_unique (417 * 48) 343 r.iy s.iy (v 1)
    · simpa [leftEnd, rightEnd, width, lowLo] using hrBox 1
    · simpa [leftEnd, rightEnd, width, lowLo] using hsBox 1
  have hiz : r.iz = s.iz := by
    apply affine_bin_unique (417 * 48) 343 r.iz s.iz (v 2)
    · simpa [leftEnd, rightEnd, width, lowLo] using hrBox 2
    · simpa [leftEnd, rightEnd, width, lowLo] using hsBox 2
  have hiw : r.iw = s.iw := by
    apply affine_bin_unique (417 * 48) 343 r.iw s.iw (v 3)
    · simpa [leftEnd, rightEnd, width, lowLo] using hrBox 3
    · simpa [leftEnd, rightEnd, width, lowLo] using hsBox 3
  simp only [rowKey, ht, hix, hiy, hiz, hiw]

theorem selectedParent_disjoint_of_rowKey_ne {r s : SourceRow}
    (hkey : rowKey r ≠ rowKey s) :
    Disjoint (selectedParent r actualMask) (selectedParent s actualMask) := by
  apply Set.disjoint_left.mpr
  intro v hr hs
  exact hkey (rowKey_eq_of_mem_selectedParent hr hs)

private theorem measurableSet_actualMask : MeasurableSet actualMask := by
  change MeasurableSet Certificates.PairedV2.FullMask.P1E0E1.pairRegion
  rw [← P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_all]
  exact Finset.measurableSet_biUnion _ (fun r _ =>
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const))))

theorem measurableSet_actualDomain : MeasurableSet actualDomain :=
  measurableSet_domain10.union (measurableSet_originalDomain _ measurableSet_actualMask)

theorem measurableSet_selectedParent (r : SourceRow) :
    MeasurableSet (selectedParent r actualMask) := by
  by_cases ht : r.term.val = 0
  · simpa [selectedParent, ht] using
      (measurableSet_logPrimeBox _ _).inter measurableSet_domain10
  · simpa [selectedParent, ht] using
      (measurableSet_logPrimeBox _ _).inter
        (measurableSet_originalDomain _ measurableSet_actualMask)

theorem selectedParent_subset_actualDomain (r : SourceRow) :
    selectedParent r actualMask ⊆ actualDomain := by
  intro v hv
  by_cases ht : r.term.val = 0
  · exact Or.inl ((show v ∈ nativeBox r ∩ domain10 by
      simpa [selectedParent, ht] using hv).2)
  · exact Or.inr ((show v ∈ nativeBox r ∩ originalDomain actualMask by
      simpa [selectedParent, ht] using hv).2)

theorem integrable_actualKernel : IntegrableOn actualKernel actualDomain :=
  integrableOn_weighted_D10.union (integrableOn_weighted_D11 actualMask)

/-- The retained selected rows need not cover the full joint functional. -/
def selectedUnion (S : Finset SourceRow) : Set LogFour :=
  ⋃ r ∈ S, selectedParent r actualMask

def uncoveredDomain (S : Finset SourceRow) : Set LogFour :=
  actualDomain \ selectedUnion S

def uncoveredCost (S : Finset SourceRow) : ℝ :=
  ∫ v in uncoveredDomain S, actualKernel v

theorem measurableSet_selectedUnion (S : Finset SourceRow) :
    MeasurableSet (selectedUnion S) :=
  Finset.measurableSet_biUnion S (fun r _ => measurableSet_selectedParent r)

theorem selectedUnion_subset_actualDomain (S : Finset SourceRow) :
    selectedUnion S ⊆ actualDomain := by
  intro v hv
  obtain ⟨r, hr⟩ := mem_iUnion.mp hv
  obtain ⟨_, hrv⟩ := mem_iUnion.mp hr
  exact selectedParent_subset_actualDomain r hrv

/-- Finite additivity is justified by actual cell geometry plus a
separate discrete key check, not by summing the per-row <= theorem. -/
theorem integral_selectedUnion_eq_sum (S : Finset SourceRow)
    (hkeys : DistinctGeometricKeys S) :
    (∫ v in selectedUnion S, actualKernel v) =
      ∑ r ∈ S, parentCost ImbalancedChen.currentK (selectedParent r actualMask) := by
  revert hkeys
  induction S using Finset.induction_on with
  | empty =>
      intro hkeys
      simp [selectedUnion]
  | @insert r S hrS ih =>
      intro hkeys
      have hkeysS : DistinctGeometricKeys S := by
        intro a ha b hb hab
        exact hkeys a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
      have hdisj : Disjoint (selectedParent r actualMask) (selectedUnion S) := by
        apply Set.disjoint_left.mpr
        intro v hrv hvS
        obtain ⟨s, hs⟩ := mem_iUnion.mp hvS
        obtain ⟨hsS, hsv⟩ := mem_iUnion.mp hs
        have hrs := hkeys r (Finset.mem_insert_self _ _) s
          (Finset.mem_insert_of_mem hsS) (rowKey_eq_of_mem_selectedParent hrv hsv)
        exact hrS (hrs.symm ▸ hsS)
      have hunion : selectedUnion (insert r S) =
          selectedParent r actualMask ∪ selectedUnion S := by
        ext v
        simp [selectedUnion]
      have hiR := integrable_actualKernel.mono_set (selectedParent_subset_actualDomain r)
      have hiS := integrable_actualKernel.mono_set (selectedUnion_subset_actualDomain S)
      rw [hunion, setIntegral_union hdisj (measurableSet_selectedUnion S) hiR hiS,
        ih hkeysS, Finset.sum_insert hrS]
      congr 1
      exact (P2N48ActualSelectedRhoCoefficient.row_selected_cost_eq_actual_kernel r).symm

/-- Exact whole-domain decomposition, with the same actual nonlinear
original-sixteen kernel and the same adopted high-band mask. -/
theorem actualSelectedCoefficient_eq_rows_add_uncovered (S : Finset SourceRow)
    (hkeys : DistinctGeometricKeys S) :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient =
      (∑ r ∈ S, parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
        uncoveredCost S := by
  have hsub := selectedUnion_subset_actualDomain S
  have hdisj : Disjoint (selectedUnion S) (uncoveredDomain S) := by
    apply Set.disjoint_left.mpr
    intro v hS hU
    exact hU.2 hS
  have hcover : selectedUnion S ∪ uncoveredDomain S = actualDomain := by
    ext v
    simp only [mem_union, uncoveredDomain, mem_diff]
    constructor
    · rintro (hS | hU)
      · exact hsub hS
      · exact hU.1
    · intro hD
      by_cases hS : v ∈ selectedUnion S
      · exact Or.inl hS
      · exact Or.inr ⟨hD, hS⟩
  have hU := measurableSet_actualDomain.diff (measurableSet_selectedUnion S)
  have hiS := integrable_actualKernel.mono_set hsub
  have hiU := integrable_actualKernel.mono_set
    (show uncoveredDomain S ⊆ actualDomain from fun _ h => h.1)
  have hsplit := setIntegral_union hdisj hU hiS hiU
  rw [hcover, integral_selectedUnion_eq_sum S hkeys] at hsplit
  change (∫ v in jointDomain (Finset.univ : Finset
    Certificates.PairedV2.FullMask.Row), P5Z.U1011OriginalJointHarmonic.weighted v) = _
  rw [jointDomain, P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_all]
  exact hsplit

/-- The actual signed native harmonic supplier reaches this exact
row/remainder decomposition. The mask is fixed before N, all U10 labels
remain unmasked, and the adopted E0+E1 complement is used only on U11.
There is no supplied cell-mean or final lower-functional premise. -/
theorem tendsto_negative_nativeJoint_rows_uncovered (S : Finset SourceRow)
    (hkeys : DistinctGeometricKeys S) :
    Tendsto (fun N : ℕ =>
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
        (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
        P5Z.U1011OriginalJointHarmonic.actualMinimum)) atTop
      (𝓝 (-(∑ r ∈ S,
        parentCost ImbalancedChen.currentK (selectedParent r actualMask)) -
          uncoveredCost S)) := by
  have ht := P5Z.U1011OriginalJointHarmonic.tendsto_nativeJoint_actual_adopted_mask.neg
  have hlim :
      -(jointIntegral (Finset.univ : Finset Certificates.PairedV2.FullMask.Row)) =
        -(∑ r ∈ S, parentCost ImbalancedChen.currentK (selectedParent r actualMask)) -
          uncoveredCost S := by
    change -P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient = _
    rw [actualSelectedCoefficient_eq_rows_add_uncovered S hkeys]
    ring
  rw [hlim] at ht
  exact ht

/-- The original method-zero/Q80 recost now feeds a bound on the WHOLE
same-rho coefficient with an explicit uncovered-cost term. No incomplete
selected cover is silently promoted to the full negative upper bound. -/
theorem actual_selected_functional_upper_with_remainder
    (hkeys : DistinctGeometricKeys actualRetainedRows)
    (hMass : ∀ r ∈ actualRetainedRows,
      massLower r ≤ parentUnweightedMass (fullParent r))
    (hOld : ∀ r ∈ actualRetainedRows,
      r.method = 0 → r.ordinal ∉ OriginalPairedN48ArchiveData.rawPriorityOrdinals.toFinset →
        anchorK * parentSwitchedMass (fullParent r) ≤
          savedParent r (parentUnweightedMass (fullParent r))) :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient ≤
      (∑ r ∈ actualRetainedRows,
        savedParent r (parentUnweightedMass (fullParent r))) -
      (∑ r ∈ actualRetainedRows, rowGainLower r) + uncoveredCost actualRetainedRows := by
  rw [actualSelectedCoefficient_eq_rows_add_uncovered actualRetainedRows hkeys]
  exact add_le_add_right (actual_archived_selected_rows_current_cost hMass hOld) _

end
end ImbalancedChen.P2N48SelectedFunctionalRemainder
