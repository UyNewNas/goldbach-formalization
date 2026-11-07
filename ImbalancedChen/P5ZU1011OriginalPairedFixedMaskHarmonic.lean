import ImbalancedChen.P5ZU1011OriginalPairedRowPrimeTests

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The ORIGINAL fixed adopted paired-v2 outer mask, including its half-open
walls, has the actual full16 nonlinear harmonic mean. No arbitrary moving
or merely measurable mask is given a PNT limit. A static finite subfamily
of the actual17572 rows is chosen before N. Their proved unique ownership
permits exact subtraction, with no replacement first-failure partition.
All common-state and row sums are finite symbolic sums; no numerical
producer, endpoint check or certificate replay is executed.
-/
namespace ImbalancedChen.P5Z.U1011OriginalPairedFixedMaskHarmonic

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenAffineState U1011OriginalPairedRowPrimeTests
open U1011OriginalSixteenNativeHarmonic
open Certificates.PairedV2

abbrev State := U1011OriginalSixteenAffineState.State
def actualMinimum : LogFour → ℝ := U1011OriginalSixteenStateKernel.actualMinimum
def domain : Set LogFour := originalDomain ∅
def box : Set LogFour := logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
  (fun _ => (59 / 250 : ℝ))
def weighted (v : LogFour) : ℝ := actualMinimum v * harmonicDensity v

def rowDomain (r : Row) : Set LogFour := domain ∩ rowRegion r
def rowPiece (r : Row) (s : State) : Set LogFour := originalCell ∅ s ∩ rowRegion r

theorem measurableSet_rowDomain (r : Row) : MeasurableSet (rowDomain r) :=
  (measurableSet_originalDomain ∅ measurableSet_empty).inter (measurableSet_rowRegion r)

theorem measurableSet_rowPiece (r : Row) (s : State) : MeasurableSet (rowPiece r s) :=
  (measurableSet_originalCell ∅ measurableSet_empty s).inter (measurableSet_rowRegion r)

theorem integrableOn_weighted : IntegrableOn weighted domain :=
  U1011OriginalSixteenFullHarmonic.integrableOn_actual_weighted

theorem sum_rowPiece_indicator (r : Row) (f : LogFour → ℝ) (v : LogFour) :
    (∑ s : State, (rowPiece r s).indicator f v) = (rowDomain r).indicator f v := by
  by_cases hd : v ∈ domain
  · let s₀ := U1011OriginalSixteenAffineState.chosenState v
    have hs₀ : v ∈ commonCell s₀ := chosenState_mem v
      ((originalDomain_denominators_pos ∅ v hd).1)
    by_cases hr : v ∈ rowRegion r
    · rw [Finset.sum_eq_single s₀]
      · exact (indicator_of_mem ⟨⟨hd, hs₀⟩, hr⟩ _).trans
          (indicator_of_mem ⟨hd, hr⟩ _).symm
      · intro s _ hne
        exact indicator_of_notMem (fun hs => hne (commonCell_unique hs.1.2 hs₀)) _
      · intro h
        exact (h (Finset.mem_univ s₀)).elim
    · rw [indicator_of_notMem (fun h => hr h.2)]
      apply Finset.sum_eq_zero
      intro s _
      exact indicator_of_notMem (fun h => hr h.2) _
  · rw [indicator_of_notMem (fun h => hd h.1)]
    apply Finset.sum_eq_zero
    intro s _
    exact indicator_of_notMem (fun h => hd h.1.1) _

def rowMean (r : Row) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  ((rowDomain r).indicator actualMinimum)
def rowStateMean (r : Row) (s : State) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  ((rowPiece r s).indicator actualMinimum)
def rowIntegral (r : Row) : ℝ := ∫ v in rowDomain r, weighted v

theorem rowMean_eq_state_sum (r : Row) (N : ℕ) :
    rowMean r N = ∑ s : State, rowStateMean r s N := by
  unfold rowMean rowStateMean actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum, sum_rowPiece_indicator]

theorem rowIntegral_eq_state_sum (r : Row) :
    rowIntegral r = ∑ s : State, ∫ v in box ∩ rowPiece r s,
      actualMinimum v * ∏ i, 1 / v i := by
  have hi (s : State) : IntegrableOn ((rowPiece r s).indicator weighted) box := by
    apply (integrable_indicator_iff (measurableSet_rowPiece r s)).2
    have hh := integrableOn_weighted.mono_set
      (show box ∩ rowPiece r s ⊆ domain from fun v hv => hv.2.1.1)
    simpa only [IntegrableOn, Measure.restrict_restrict (measurableSet_rowPiece r s),
      inter_comm] using hh
  have hsub : rowDomain r ⊆ box := fun v hv =>
    U1011OriginalSixteenFullHarmonic.domain_subset_box hv.1
  calc
    rowIntegral r = ∫ v in box, (rowDomain r).indicator weighted v := by
      rw [setIntegral_indicator (measurableSet_rowDomain r), inter_eq_right.mpr hsub]
      rfl
    _ = ∫ v in box, ∑ s : State, (rowPiece r s).indicator weighted v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => (sum_rowPiece_indicator r weighted v).symm)
    _ = ∑ s : State, ∫ v in box, (rowPiece r s).indicator weighted v := by
      exact integral_finsetSum _ (fun s _ => hi s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [setIntegral_indicator (measurableSet_rowPiece r s)]
      apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter (measurableSet_rowPiece r s))
      intro v _
      rw [weighted, U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]

/-- Every actual fixed row receives the FULL16 nonlinear mean, with all
common-state limits supplied by proved affine-row PNT theorems. -/
theorem tendsto_rowMean (r : Row) : Tendsto (rowMean r) atTop (𝓝 (rowIntegral r)) := by
  rw [rowIntegral_eq_state_sum]
  have ht := tendsto_finsetSum (Finset.univ : Finset State)
    (fun s _ => tendsto_actual_commonCell_row s r)
  have ht' : Tendsto (fun N : ℕ => ∑ s : State, rowStateMean r s N) atTop
      (𝓝 (∑ s : State, ∫ v in box ∩ rowPiece r s, actualMinimum v * ∏ i, 1 / v i)) := by
    simpa only [rowStateMean, rowPiece, box, actualMinimum] using ht
  have heq : rowMean r = fun N => ∑ s : State, rowStateMean r s N := by
    funext N
    exact rowMean_eq_state_sum r N
  rw [heq]
  exact ht'

def outerUnion (S : Finset Row) : Set (ℝ × ℝ) :=
  ⋃ r ∈ S, FullMask.P1E0E1.pairCell r
def removedRegion (S : Finset Row) : Set LogFour := ⋃ r ∈ S, rowRegion r
def keptDomain (S : Finset Row) : Set LogFour := domain \ removedRegion S

theorem measurableSet_removedRegion (S : Finset Row) : MeasurableSet (removedRegion S) :=
  Finset.measurableSet_biUnion S (fun r _ => measurableSet_rowRegion r)
theorem measurableSet_keptDomain (S : Finset Row) : MeasurableSet (keptDomain S) :=
  (measurableSet_originalDomain ∅ measurableSet_empty).diff (measurableSet_removedRegion S)

theorem originalDomain_outerUnion (S : Finset Row) : originalDomain (outerUnion S) = keptDomain S := by
  ext v
  rw [originalDomain_mask_iff]
  simp only [outerUnion, removedRegion, keptDomain, rowRegion, mem_preimage,
    mem_iUnion, mem_diff, domain]

/-- The finite actual row mask has a unique owner. Consequently its
complement is obtained by exact subtraction, with every endpoint retained. -/
theorem kept_indicator_split (S : Finset Row) (f : LogFour → ℝ) (v : LogFour) :
    domain.indicator f v = (keptDomain S).indicator f v +
      ∑ r ∈ S, (rowDomain r).indicator f v := by
  by_cases hd : v ∈ domain
  · by_cases hex : ∃ r ∈ S, v ∈ rowRegion r
    · obtain ⟨r, hrS, hrv⟩ := hex
      have hremoved : v ∈ removedRegion S := mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hrS, hrv⟩⟩
      rw [indicator_of_mem hd, indicator_of_notMem (fun h => h.2 hremoved), zero_add]
      symm
      calc
        _ = (rowDomain r).indicator f v := by
          apply Finset.sum_eq_single r
          · intro t _ htr
            exact indicator_of_notMem (fun ht => htr (rowRegions_unique_owner ht.2 hrv)) _
          · intro hn
            exact (hn hrS).elim
        _ = f v := indicator_of_mem ⟨hd, hrv⟩ _
    · have hnot : v ∉ removedRegion S := by
        intro hremoved
        obtain ⟨r, hr⟩ := mem_iUnion.mp hremoved
        obtain ⟨hrS, hrv⟩ := mem_iUnion.mp hr
        exact hex ⟨r, hrS, hrv⟩
      rw [indicator_of_mem hd, indicator_of_mem ⟨hd, hnot⟩]
      have hzero : (∑ r ∈ S, (rowDomain r).indicator f v) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        exact indicator_of_notMem (fun h => hex ⟨r, hr, h.2⟩) _
      rw [hzero, add_zero]
  · rw [indicator_of_notMem hd, indicator_of_notMem (fun h => hd h.1)]
    have hzero : (∑ r ∈ S, (rowDomain r).indicator f v) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      exact indicator_of_notMem (fun h => hd h.1) _
    rw [hzero, add_zero]

def keptMean (S : Finset Row) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  ((keptDomain S).indicator actualMinimum)
def keptIntegral (S : Finset Row) : ℝ := ∫ v in keptDomain S, weighted v

theorem keptMean_eq_difference (S : Finset Row) (N : ℕ) :
    keptMean S N = U1011OriginalSixteenFullHarmonic.primeMean N - ∑ r ∈ S, rowMean r N := by
  have hsplit : U1011OriginalSixteenFullHarmonic.primeMean N =
      keptMean S N + ∑ r ∈ S, rowMean r N := by
    unfold U1011OriginalSixteenFullHarmonic.primeMean keptMean rowMean actualPrimeBoxTestSum
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.mul_sum, ← mul_add, ← kept_indicator_split]
  linarith only [hsplit]

theorem keptIntegral_eq_difference (S : Finset Row) :
    keptIntegral S = (∫ v in domain, weighted v) - ∑ r ∈ S, rowIntegral r := by
  have hiD : IntegrableOn (domain.indicator weighted) box := by
    apply (integrable_indicator_iff (measurableSet_originalDomain ∅ measurableSet_empty)).2
    have hh := integrableOn_weighted.mono_set (show box ∩ domain ⊆ domain from inter_subset_right)
    simpa only [IntegrableOn, Measure.restrict_restrict
      (measurableSet_originalDomain ∅ measurableSet_empty), inter_comm] using hh
  have hiK : IntegrableOn ((keptDomain S).indicator weighted) box := by
    apply (integrable_indicator_iff (measurableSet_keptDomain S)).2
    have hh := integrableOn_weighted.mono_set
      (show box ∩ keptDomain S ⊆ domain from fun v hv => hv.2.1)
    simpa only [IntegrableOn, Measure.restrict_restrict (measurableSet_keptDomain S), inter_comm] using hh
  have hiR (r : Row) : IntegrableOn ((rowDomain r).indicator weighted) box := by
    apply (integrable_indicator_iff (measurableSet_rowDomain r)).2
    have hh := integrableOn_weighted.mono_set
      (show box ∩ rowDomain r ⊆ domain from fun v hv => hv.2.1)
    simpa only [IntegrableOn, Measure.restrict_restrict (measurableSet_rowDomain r), inter_comm] using hh
  have hsplit : (∫ v in domain, weighted v) = keptIntegral S + ∑ r ∈ S, rowIntegral r := by
    have hboxD : box ∩ domain = domain := inter_eq_right.mpr
      U1011OriginalSixteenFullHarmonic.domain_subset_box
    have hboxK : box ∩ keptDomain S = keptDomain S := inter_eq_right.mpr
      (fun v hv => U1011OriginalSixteenFullHarmonic.domain_subset_box hv.1)
    have hboxR (r : Row) : box ∩ rowDomain r = rowDomain r := inter_eq_right.mpr
      (fun v hv => U1011OriginalSixteenFullHarmonic.domain_subset_box hv.1)
    calc
      _ = ∫ v in box, domain.indicator weighted v := by
        rw [setIntegral_indicator (measurableSet_originalDomain ∅ measurableSet_empty), hboxD]
      _ = ∫ v in box, (keptDomain S).indicator weighted v +
          ∑ r ∈ S, (rowDomain r).indicator weighted v := by
        apply integral_congr_ae
        exact Eventually.of_forall (kept_indicator_split S weighted)
      _ = (∫ v in box, (keptDomain S).indicator weighted v) +
          ∑ r ∈ S, ∫ v in box, (rowDomain r).indicator weighted v := by
        rw [integral_add hiK (integrable_finsetSum S (fun r _ => hiR r)),
          integral_finsetSum S (fun r _ => hiR r)]
      _ = _ := by
        rw [setIntegral_indicator (measurableSet_keptDomain S), hboxK]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        rw [setIntegral_indicator (measurableSet_rowDomain r), hboxR]
        rfl
  linarith only [hsplit]

/-- The retained complement of a STATIC actual row family has its true
full16 nonlinear mean. All individual means are proved suppliers above. -/
theorem tendsto_keptMean (S : Finset Row) :
    Tendsto (keptMean S) atTop (𝓝 (keptIntegral S)) := by
  have hrows := tendsto_finsetSum S (fun r _ => tendsto_rowMean r)
  have ht := U1011OriginalSixteenFullHarmonic.tendsto_actual_original_full_sixteen_mean.sub hrows
  rw [keptIntegral_eq_difference]
  have heq : keptMean S = fun N => U1011OriginalSixteenFullHarmonic.primeMean N -
      ∑ r ∈ S, rowMean r N := by
    funext N
    exact keptMean_eq_difference S N
  rw [heq]
  exact ht

/-- Native carrier version with the original ascending last pair read in
the already adopted decreasing-coordinate mask, exactly once. -/
theorem tendsto_native_staticRows (S : Finset Row) :
    Tendsto (fun N : ℕ => nativeHarmonicSum N (nativeMask (outerUnion S) N) actualMinimum)
      atTop (𝓝 (∫ v in originalDomain (outerUnion S), weighted v)) := by
  have heq : keptMean S =ᶠ[atTop]
      (fun N : ℕ => nativeHarmonicSum N (nativeMask (outerUnion S) N) actualMinimum) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    rw [nativeHarmonicSum_eq_fixedMask_box hN, originalDomain_outerUnion]
    rfl
  rw [originalDomain_outerUnion]
  exact (tendsto_keptMean S).congr' heq

theorem outerUnion_all : outerUnion (Finset.univ : Finset Row) = FullMask.P1E0E1.pairRegion := by
  ext q
  simp [outerUnion, FullMask.P1E0E1.pairRegion]

/-- The literal original adopted E0+E1 deletion mask, not a substitute
row family, now has the native full16 nonlinear harmonic main term. -/
theorem tendsto_native_actual_adopted_mask :
    Tendsto (fun N : ℕ => nativeHarmonicSum N
      (FullMask.P1E0E1.deletionMask (N : ℝ)) actualMinimum) atTop
      (𝓝 (∫ v in originalDomain FullMask.P1E0E1.pairRegion, weighted v)) := by
  simpa only [outerUnion_all, nativeMask_actual_adopted] using
    tendsto_native_staticRows (Finset.univ : Finset Row)

def e0Rows : Finset Row := Finset.univ.filter FullMask.P1E0E1.IsE0
def e1Rows : Finset Row := Finset.univ.filter FullMask.P1E0E1.IsE1

theorem outerUnion_e0 : outerUnion e0Rows = FullMask.P1E0E1.e0PairRegion := by
  ext q
  simp [outerUnion, e0Rows, FullMask.P1E0E1.e0PairRegion]

theorem outerUnion_e1 : outerUnion e1Rows = FullMask.P1E0E1.e1PairRegion := by
  ext q
  simp [outerUnion, e1Rows, FullMask.P1E0E1.e1PairRegion]

theorem tendsto_native_actual_e0_mask :
    Tendsto (fun N : ℕ => nativeHarmonicSum N
      (FullMask.P1E0E1.e0DeletionMask (N : ℝ)) actualMinimum) atTop
      (𝓝 (∫ v in originalDomain FullMask.P1E0E1.e0PairRegion, weighted v)) := by
  simpa only [outerUnion_e0, nativeMask, FullMask.P1E0E1.e0DeletionMask] using
    tendsto_native_staticRows e0Rows

theorem tendsto_native_actual_e1_mask :
    Tendsto (fun N : ℕ => nativeHarmonicSum N
      (FullMask.P1E0E1.e1DeletionMask (N : ℝ)) actualMinimum) atTop
      (𝓝 (∫ v in originalDomain FullMask.P1E0E1.e1PairRegion, weighted v)) := by
  simpa only [outerUnion_e1, nativeMask, FullMask.P1E0E1.e1DeletionMask] using
    tendsto_native_staticRows e1Rows

end
end ImbalancedChen.P5Z.U1011OriginalPairedFixedMaskHarmonic
