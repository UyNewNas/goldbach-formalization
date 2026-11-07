import ImbalancedChen.P1OriginalVariableFourthSourceLimit

/-!
Finite exact row-wall refinement of the original variable fourth source.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Every closed producer-box face is a proper affine wall. A Boolean sign
pattern owns each face in its weak branch, while its other branch is
strict. The resulting finite atoms partition every point exactly, including
prime atoms on faces. Eligibility is constant on each atom. Continuous
extensions are used separately on atoms; no global continuity is claimed.
-/

namespace ImbalancedChen.P1OriginalVariableFourthEligibilityPartition
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P1OriginalVariableFourthCellTestLimit
open P1OriginalCoarseContinuation P1OriginalFourthLimit P1OriginalFourthIntegral
open P1FourthFullCellIntegral
open HistoricalThirdCoarse.P1OriginalFourth

abbrev WallKey (rows : Finset ProducerRow) := {r // r ∈ rows} × (Fin 4 × Bool)
abbrev Pattern (rows : Finset ProducerRow) := WallKey rows → Bool

def wallForm {rows : Finset ProducerRow} (k : WallKey rows) : Point →L[ℝ] ℝ :=
  if k.2.2 then ContinuousLinearMap.proj k.2.1 else -ContinuousLinearMap.proj k.2.1

def wallBound {rows : Finset ProducerRow} (k : WallKey rows) : ℝ :=
  if k.2.2 then (k.1.val.upper k.2.1 : ℝ) else -(k.1.val.lower k.2.1 : ℝ)

theorem wallForm_ne_zero {rows : Finset ProducerRow} (k : WallKey rows) : wallForm k ≠ 0 := by
  have hp : (ContinuousLinearMap.proj k.2.1 : Point →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (fun F : Point →L[ℝ] ℝ => F (fun _ => 1)) h
    simp at hh
  cases h : k.2.2 <;> simp only [wallForm, h, Bool.false_eq_true, if_false, if_true]
  · exact neg_ne_zero.mpr hp
  · exact hp

/-- True owns the weak side, including equality. False owns the strict
complement. The licensing proposition is fixed independently of t. -/
def wallAtom (rows : Finset ProducerRow) (s : Pattern rows) : Set Point :=
  {t | ∀ k, if s k then wallForm k t ≤ wallBound k else wallBound k < wallForm k t}

def actualPattern (rows : Finset ProducerRow) (t : Point) : Pattern rows :=
  fun k => decide (wallForm k t ≤ wallBound k)

theorem mem_actual_wallAtom (rows : Finset ProducerRow) (t : Point) :
    t ∈ wallAtom rows (actualPattern rows t) := by
  intro k
  by_cases h : wallForm k t ≤ wallBound k
  · simp [actualPattern, h]
  · simp [actualPattern, h, lt_of_not_ge h]

theorem wallAtom_compare_iff {rows : Finset ProducerRow} {s : Pattern rows}
    {t : Point} (ht : t ∈ wallAtom rows s) (k : WallKey rows) :
    wallForm k t ≤ wallBound k ↔ s k = true := by
  have hk := ht k
  cases h : s k
  · simp only [h, Bool.false_eq_true, if_false] at hk
    simp only [h, Bool.false_eq_true, iff_false]
    exact not_le.mpr hk
  · simp only [h, if_true] at hk
    simpa [h] using hk

theorem wallAtom_unique {rows : Finset ProducerRow} {s u : Pattern rows}
    {t : Point} (hs : t ∈ wallAtom rows s) (hu : t ∈ wallAtom rows u) : s = u := by
  funext k
  have hk : (s k = true ↔ u k = true) :=
    (wallAtom_compare_iff hs k).symm.trans (wallAtom_compare_iff hu k)
  cases hsk : s k <;> cases huk : u k <;> simp_all

theorem measurableSet_wallAtom (rows : Finset ProducerRow) (s : Pattern rows) :
    MeasurableSet (wallAtom rows s) := by
  simp only [wallAtom, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  cases h : s k
  · simpa only [h, Bool.false_eq_true, if_false] using
      (isOpen_lt (continuous_const : Continuous (fun _ : Point => wallBound k))
        (wallForm k).continuous).measurableSet
  · simpa only [h, if_true] using
      (isClosed_le (wallForm k).continuous
        (continuous_const : Continuous (fun _ : Point => wallBound k))).measurableSet

/-- Finite measurable disjoint refinement of ANY source, with exact face
ownership. Restriction to a positive cube needs no extra assumptions. -/
theorem source_partition (rows : Finset ProducerRow) (R : Set Point) :
    (∀ t ∈ R, ∃ s : Pattern rows, t ∈ R ∩ wallAtom rows s) ∧
    (∀ s u : Pattern rows, s ≠ u → Disjoint (R ∩ wallAtom rows s) (R ∩ wallAtom rows u)) := by
  constructor
  · intro t ht
    exact ⟨actualPattern rows t, ht, mem_actual_wallAtom rows t⟩
  · intro s u hsu
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact hsu (wallAtom_unique ht.2 hu.2)

/-- All rows passing BOTH coordinate face tests, including every overlap.
A row's membership proof is immaterial by proof irrelevance. -/
def eligibleRows (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (s : Pattern rows) : Finset ProducerRow :=
  rows.filter (fun r => licensed r ∧ ∀ (hr : r ∈ rows) (i : Fin 4),
    s (⟨r, hr⟩, (i, false)) = true ∧ s (⟨r, hr⟩, (i, true)) = true)

theorem row_box_iff_signs {rows : Finset ProducerRow} {s : Pattern rows}
    {t : Point} (ht : t ∈ wallAtom rows s) (r : ProducerRow) (hr : r ∈ rows) :
    t ∈ r.box ↔ ∀ i : Fin 4,
      s (⟨r, hr⟩, (i, false)) = true ∧ s (⟨r, hr⟩, (i, true)) = true := by
  have hlo (i : Fin 4) := wallAtom_compare_iff ht (⟨r, hr⟩, (i, false))
  have hhi (i : Fin 4) := wallAtom_compare_iff ht (⟨r, hr⟩, (i, true))
  simp only [wallForm, wallBound, Bool.false_eq_true, if_false, if_true,
    neg_apply, ContinuousLinearMap.proj_apply, neg_le_neg_iff] at hlo hhi
  constructor
  · intro h i
    exact ⟨(hlo i).mp (h.1 i), (hhi i).mp (h.2 i)⟩
  · intro h
    exact ⟨fun i => (hlo i).mpr (h i).1, fun i => (hhi i).mpr (h i).2⟩

/-- Fixed eligibility is CONSTRUCTED on every atom. It is not a user premise. -/
theorem eligibility_fixed_on_atom (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (s : Pattern rows) :
    ∀ r ∈ rows, ∀ t ∈ wallAtom rows s,
      producerEligible licensed r t ↔ r ∈ eligibleRows rows licensed s := by
  intro r hr t ht
  rw [eligibleRows, Finset.mem_filter]
  constructor
  · rintro ⟨hl, hb⟩
    exact ⟨hr, hl, fun hmem i => (row_box_iff_signs ht r hmem).mp hb i⟩
  · rintro ⟨_, hl, hb⟩
    exact ⟨hl, (row_box_iff_signs ht r hr).mpr (hb hr)⟩

theorem producerProfile_eq_fixed_on_atom (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) {t : Point}
    (ht : t ∈ wallAtom rows s) :
    producerProfile4 e rows licensed seed t =
      fixedCellExponent e rows (eligibleRows rows licensed s) seed t := by
  exact producerProfile4_eq_fixedCellExponent_on_source e rows licensed _ seed _
    (eligibility_fixed_on_atom rows licensed s) ht

/-- Each finite max attains either the inherited rawQ3 seed or an ACTUALLY
eligible row. The seed branch is retained even when every candidate loses. -/
theorem producerProfile_seed_or_eligible_row (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e rows licensed seed t = seed ∨
      ∃ r ∈ rows, producerEligible licensed r t ∧
        producerProfile4 e rows licensed seed t = r.bufferedCandidate e t := by
  have hmem := Finset.max'_mem
    (finiteValues rows (fun r => producerEligible licensed r t) (fun r => r.bufferedCandidate e t) seed)
    (finiteValues_nonempty rows _ _ seed)
  change producerProfile4 e rows licensed seed t ∈
    insert seed ((rows.filter (fun r => producerEligible licensed r t)).image
      (fun r => r.bufferedCandidate e t)) at hmem
  rcases Finset.mem_insert.mp hmem with hs | hr
  · exact Or.inl hs
  · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hr
    exact Or.inr ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2, heq.symm⟩

/-- Pointwise finite indicator decomposition; no global continuous profile
is substituted across box walls. This also retains boundary prime atoms. -/
theorem source_test_eq_sum_atom_tests (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (R : Set Point) (t : Point) :
    R.indicator (fun t => extendedProfile seed t -
      extendedProfile (producerProfile4 e rows licensed seed t) t) t =
    ∑ s : Pattern rows, (R ∩ wallAtom rows s).indicator
      (fixedCellTest e rows (eligibleRows rows licensed s) seed) t := by
  classical
  rw [Finset.sum_eq_single (actualPattern rows t)]
  · by_cases ht : t ∈ R
    · simp only [indicator_of_mem ht, indicator_of_mem
        (show t ∈ R ∩ wallAtom rows (actualPattern rows t) from ⟨ht, mem_actual_wallAtom rows t⟩),
        fixedCellTest, producerProfile_eq_fixed_on_atom e seed rows licensed _ (mem_actual_wallAtom rows t)]
    · simp only [indicator_of_not_mem ht,
        indicator_of_not_mem (show t ∉ R ∩ wallAtom rows (actualPattern rows t) from fun h => ht h.1)]
  · intro s _hs hne
    apply indicator_of_not_mem
    intro ht
    exact hne (wallAtom_unique ht.2 (mem_actual_wallAtom rows t))
  · simp

/-- Finite-type version of the proved mixed-affine-gate prime supplier. -/
theorem tendsto_test_finite_mixed_gates {d : ℕ} {κ : Type*} [Fintype κ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (L : κ → (Fin d → ℝ) →L[ℝ] ℝ) (c : κ → ℝ) (hL : ∀ k, L k ≠ 0)
    (R : Set (Fin d → ℝ)) (hR : MeasurableSet R)
    (hlo : ∀ t, (∀ k, L k t < c k) → t ∈ R)
    (hhi : ∀ t ∈ R, ∀ k, L k t ≤ c k)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (univ.pi (fun _ : Fin d => Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      (R.indicator f)) atTop
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ R,
        f t * ∏ i, 1 / t i)) := by
  let eqv := Fintype.equivFin κ
  apply tendsto_actualPrimeBoxTestSum_cube_affineSandwich ha hab
    (fun j => L (eqv.symm j)) (fun j => c (eqv.symm j)) (fun j => hL _) R hR
  · intro t ht
    apply hlo t
    intro k
    simpa only [Equiv.symm_apply_apply] using ht (eqv k)
  · intro t ht j
    exact hhi t ht (eqv.symm j)
  · exact hf

/-- Oriented walls turn each exact weak/strict atom into a mixed affine
sandwich. The original source gates can be joined through a disjoint sum. -/
theorem tendsto_test_source_wallAtom {κ : Type*} [Fintype κ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (L : κ → Point →L[ℝ] ℝ) (c : κ → ℝ) (hL : ∀ k, L k ≠ 0)
    (R : Set Point) (hR : MeasurableSet R)
    (hlo : ∀ t, (∀ k, L k t < c k) → t ∈ R)
    (hhi : ∀ t ∈ R, ∀ k, L k t ≤ c k)
    (rows : Finset ProducerRow) (s : Pattern rows)
    (f : Point → ℝ) (hf : ContinuousOn f (univ.pi (fun _ : Fin 4 => Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
      ((R ∩ wallAtom rows s).indicator f)) atTop
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin 4 => a) (fun _ => b) ∩ (R ∩ wallAtom rows s),
        f t * ∏ i, 1 / t i)) := by
  let O : WallKey rows → Point →L[ℝ] ℝ := fun k => if s k then wallForm k else -wallForm k
  let d : WallKey rows → ℝ := fun k => if s k then wallBound k else -wallBound k
  apply tendsto_test_finite_mixed_gates a b ha hab
    (Sum.elim L O) (Sum.elim c d) ?_ (R ∩ wallAtom rows s)
    (hR.inter (measurableSet_wallAtom rows s)) ?_ ?_ f hf
  · intro k
    cases k with
    | inl k => exact hL k
    | inr k =>
      cases h : s k <;> simp only [Sum.elim_inr, O, h, Bool.false_eq_true, if_false, if_true]
      · exact neg_ne_zero.mpr (wallForm_ne_zero k)
      · exact wallForm_ne_zero k
  · intro t ht
    refine ⟨hlo t (fun k => ht (Sum.inl k)), ?_⟩
    intro k
    have hk := ht (Sum.inr k)
    cases h : s k
    · simpa only [Sum.elim_inr, O, d, h, Bool.false_eq_true, if_false,
        neg_apply, neg_lt_neg_iff] using hk
    · have hk' : wallForm k t < wallBound k := by
        simpa only [Sum.elim_inr, O, d, h, if_true] using hk
      simpa only [h, if_true] using hk'.le
  · intro t ht k
    cases k with
    | inl k => exact hhi t ht.1 k
    | inr k =>
      have hk := ht.2 k
      cases h : s k
      · have hk' : wallBound k < wallForm k t := by
          simpa only [h, Bool.false_eq_true, if_false] using hk
        simpa only [Sum.elim_inr, O, d, h, Bool.false_eq_true, if_false,
          neg_apply, neg_le_neg_iff] using hk'.le
      · simpa only [Sum.elim_inr, O, d, h, if_true] using hk

/-- The actual original firstStop/rawQ3 source admits every finite row-wall
refinement. Empty firstStop cells stay empty. No arithmetic wall premise is
assumed; the mixed-gate supplier pays all exact wall atoms. -/
theorem tendsto_test_original_source_wallAtom
    (e : ℚ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2)
    (rows : Finset ProducerRow) (s : Pattern rows)
    (f : Point → ℝ) (hf : ContinuousOn f (univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j ∩ wallAtom rows s).indicator f)) atTop
      (𝓝 (∫ t in truncatedCell e m omega a j ∩ wallAtom rows s,
        f t * ∏ i, 1 / t i)) := by
  rw [truncatedCell_eq_inter_sourceRegion, inter_assoc]
  rw [sourceRegion_eq_if e m omega j hwhole]
  by_cases hs : HistoricalThirdCoarse.P1OriginalFourth.firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
    let lo := logPrimeMeshLo 0 (19 / 96) m j
    let hi := logPrimeMeshHi 0 (19 / 96) m j
    let L := HistoricalThirdCoarse.P1OriginalFourth.gateForms
    let c := HistoricalThirdCoarse.P1OriginalFourth.gateBounds (HistoricalThirdCoarse.initial (e : ℝ))
      (HistoricalThirdCoarse.levelExponent (e : ℝ) (HistoricalThirdCoarse.box m (prefix3 j)))
    apply tendsto_test_source_wallAtom a (19 / 96) ha haRho
      (primeIcoBoxGateForms L) (primeIcoBoxGateBounds lo hi c)
      (primeIcoBoxGateForms_ne_zero L HistoricalThirdCoarse.P1OriginalFourth.gateForms_ne_zero)
      (logPrimeMeshCell 0 (19 / 96) m j ∩ primeAffineGateRegion L c)
      ((measurableSet_logPrimeBox lo hi).inter (measurableSet_primeAffineGateRegion L c))
      ?_ ?_ rows s f hf
    · intro t ht
      obtain ⟨hb, hg⟩ := (mem_primeIcoBoxStrictGateRegion lo hi L c t).mp ht
      exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩), hg⟩
    · intro t ht
      simp only [primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
        Fin.append_left, Fin.append_right, neg_apply,
        ContinuousLinearMap.proj_apply, neg_le_neg_iff]
      exact ⟨fun i => (mem_logPrimeBox.mp ht.1 i).1,
        fun i => (mem_logPrimeBox.mp ht.1 i).2.le, fun k => (ht.2 k).le⟩
  · simp only [if_neg hs, empty_inter, inter_empty, indicator_empty,
      actualPrimeBoxTestSum, Pi.zero_apply, mul_zero, Finset.sum_const_zero, integral_empty]
    exact tendsto_const_nhds

/-- Refined continuous tests now have a proved source limit without an
external fixed-eligibility premise. The seed is the actual selected rawQ3
cell exponent; all eligible rows remain in its finite max. -/
theorem tendsto_refined_variable_cell_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (s : Pattern rows) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j ∩ wallAtom rows s).indicator
        (fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s) (oldExponent e m j)))) atTop
      (𝓝 (∫ t in truncatedCell e m omega a j ∩ wallAtom rows s,
        fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s) (oldExponent e m j) t * ∏ i, 1 / t i)) := by
  exact tendsto_test_original_source_wallAtom e m omega a ha haRho j
    (selected_whole_active e chi m omega J4 j hj) rows s _
    (continuousOn_fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
      (oldExponent e m j) a (19 / 96) ha)

/-- Exact finite prime-sum decomposition; a tuple on a producer face is
assigned to its unique weak-side atom before any limit is taken. -/
theorem original_variable_test_eq_sum_refined
    (e seed : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (R : Set Point) (N : ℕ) (a b : ℝ) :
    actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
      (R.indicator (fun t => extendedProfile seed t -
        extendedProfile (producerProfile4 e rows licensed seed t) t)) =
    ∑ s : Pattern rows, actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
      ((R ∩ wallAtom rows s).indicator
        (fixedCellTest e rows (eligibleRows rows licensed s) seed)) := by
  unfold actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [source_test_eq_sum_atom_tests e seed rows licensed R (actualPrimeTupleLog N p), Finset.mul_sum]

/-- Eligibility-free original-source continuous-test limit, expressed as
the finite sum of its genuine wall-refined integrals. This is the replacement
for a false continuity assertion across all producer-box faces. -/
theorem tendsto_original_variable_cell_test_refinedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j).indicator (fun t => extendedProfile (oldExponent e m j) t -
        extendedProfile (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t))) atTop
      (𝓝 (∑ s : Pattern rows, ∫ t in truncatedCell e m omega a j ∩ wallAtom rows s,
        fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s) (oldExponent e m j) t * ∏ i, 1 / t i)) := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Pattern rows)) (fun s _ =>
    tendsto_refined_variable_cell_test e chi m omega a ha haRho J4 j hj rows licensed s)
  apply hlim.congr'
  exact Eventually.of_forall (fun N => (original_variable_test_eq_sum_refined (e : ℝ)
    (oldExponent e m j) rows licensed (sourceRegion e m omega j) N a (19 / 96)).symm)

end
end ImbalancedChen.P1OriginalVariableFourthEligibilityPartition



