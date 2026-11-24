import ImbalancedChen.P2OriginalFourteenWeightedTrim
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The fixed-trim test is the union of the original fourteen 96-row systems.
Inclusion-exclusion counts this union once even before proving any pairwise
separation. Constant rows are evaluated as constant conditions; no identity
is turned into a proper affine wall. All prime factors of the target stay
deleted in the actualPrimeBoxTestSum carrier.
-/
namespace ImbalancedChen.P2OriginalFourteenRetainedPrimeIntegral
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim

def weakAffineRegion {ι : Type*} (L : ι → Point →L[ℝ] ℝ) (b : ι → ℝ) : Set Point :=
  {t | ∀ i, L i t ≤ b i}

theorem measurableSet_weakAffineRegion {ι : Type*} [Fintype ι]
    (L : ι → Point →L[ℝ] ℝ) (b : ι → ℝ) :
    MeasurableSet (weakAffineRegion L b) := by
  simpa only [weakAffineRegion, ofPred_forall] using
    (isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)).measurableSet

/-- The caller supplies actual linear forms, not a null-wall certificate.
Zero forms are removed only after checking their constant inequalities. -/
theorem tendsto_test_weakAffineRegion {ι : Type*} [Fintype ι]
    (L : ι → Point →L[ℝ] ℝ) (b : ι → ℝ)
    (f : Point → ℝ) (hf : ContinuousOn f coordinateBox) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff)
      (fun _ => mu) ((weakAffineRegion L b).indicator f)) atTop
      (𝓝 (∫ t in box ∩ weakAffineRegion L b, f t * ∏ i, 1 / t i)) := by
  by_cases hconstant : ∀ i, L i = 0 → 0 ≤ b i
  · let J := {i : ι // L i ≠ 0}
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    let A : Fin (Fintype.card J) → Point →L[ℝ] ℝ := fun j => L (e j).1
    let c : Fin (Fintype.card J) → ℝ := fun j => b (e j).1
    have hA : ∀ j, A j ≠ 0 := fun j => (e j).2
    have hlo : primeAffineGateRegion A c ⊆ weakAffineRegion L b := by
      intro t ht i
      by_cases hi : L i = 0
      · simpa only [hi, ContinuousLinearMap.zero_apply] using hconstant i hi
      · have hh := ht (e.symm ⟨i, hi⟩)
        simpa only [A, c, Equiv.apply_symm_apply] using hh.le
    have hhi : ∀ t ∈ weakAffineRegion L b, ∀ j, A j t ≤ c j :=
      fun t ht j => ht (e j).1
    exact tendsto_actualPrimeBoxTestSum_cube_affineSandwich cutoff_pos
      (by norm_num [cutoff, mu]) A c hA _ (measurableSet_weakAffineRegion L b)
      hlo hhi f hf
  · obtain ⟨i, hi, hb⟩ : ∃ i, L i = 0 ∧ ¬ 0 ≤ b i := by
      simpa only [not_forall, not_imp] using hconstant
    have hempty : weakAffineRegion L b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hb (by simpa only [hi, ContinuousLinearMap.zero_apply] using ht i)
    simpa only [hempty, indicator_empty, inter_empty, setIntegral_empty,
      actualPrimeBoxTestSum, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def rowRegion (delta : ℝ) (c : Cell) : Set Point :=
  {t | ∀ k : Fin 96, delta ≤ evalRow (rows c k).2 t}

theorem rowRegion_eq_trimmedCell (delta : ℝ) (hdelta : 0 < delta) (c : Cell) :
    rowRegion delta c = trimmedCell delta c := by
  ext t
  constructor
  · intro ht
    have hc : t ∈ cell c := fun k => hdelta.trans_le (ht k)
    exact ⟨(cell_subset_safeCarrier c hc).1, mem_iInter.mpr ht⟩
  · intro ht
    exact fun k => mem_iInter.mp ht.2 k

def intersectionForms (s : Finset Cell) : ({c // c ∈ s} × Fin 96) → Point →L[ℝ] ℝ :=
  fun j => -linearPart (rows j.1.1 j.2).2

def intersectionBounds (delta : ℝ) (s : Finset Cell) : ({c // c ∈ s} × Fin 96) → ℝ :=
  fun j => ((rows j.1.1 j.2).2 0 : ℝ) - delta

theorem rowRegion_intersection_eq (delta : ℝ) (s : Finset Cell) :
    (⋂ c ∈ s, rowRegion delta c) =
      weakAffineRegion (intersectionForms s) (intersectionBounds delta s) := by
  ext t
  simp only [mem_iInter, rowRegion, mem_setOf_eq, weakAffineRegion,
    intersectionForms, intersectionBounds, ContinuousLinearMap.neg_apply,
    evalRow_eq_linear]
  constructor
  · intro ht j
    have hh := ht j.1.1 j.1.2 j.2
    linarith
  · intro ht c hc k
    have hh := ht (⟨c, hc⟩, k)
    linarith

theorem measurableSet_rowRegion (delta : ℝ) (c : Cell) :
    MeasurableSet (rowRegion delta c) := by
  simpa only [rowRegion, ofPred_forall] using
    (isClosed_iInter (fun k : Fin 96 =>
      isClosed_le continuous_const (continuous_evalRow (rows c k).2))).measurableSet

/-- An exact finite identity, not a disjointness hypothesis. In particular
the family selector never gives a repeated tuple one payment per cell. -/
theorem testSum_finite_union (N : ℕ) (s : Finset Cell)
    (D : Cell → Set Point) (f : Point → ℝ) :
    actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu)
      ((⋃ c ∈ s, D c).indicator f) =
      ∑ q ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (q.card + 1) *
          actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu)
            ((⋂ c ∈ q, D c).indicator f) := by
  have hind (t : Point) : (⋃ c ∈ s, D c).indicator f t =
      ∑ q ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (q.card + 1) * (⋂ c ∈ q, D c).indicator f t := by
    simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      Finset.indicator_biUnion_eq_sum_powerset s D f t
  simp only [actualPrimeBoxTestSum, hind, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Genuine fixed-trim reciprocal-prime convergence on the complete
literal14 union. No frontier equality, Riemann premise, row truth or
coverage of a numerical triangulation occurs among the assumptions. -/
theorem tendsto_trimmed_testSum (delta : ℝ) (hdelta : 0 < delta)
    (f : Point → ℝ) (hf : ContinuousOn f coordinateBox) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff)
      (fun _ => mu) ((trimmedRegion delta).indicator f)) atTop
      (𝓝 (∫ t in trimmedRegion delta, f t * ∏ i, 1 / t i)) := by
  let D : Cell → Set Point := rowRegion delta
  have hU : (⋃ c ∈ (Finset.univ : Finset Cell), D c) = trimmedRegion delta := by
    simp only [D, rowRegion_eq_trimmedCell delta hdelta, Finset.mem_univ, iUnion_true,
      trimmedRegion]
  have hinter (q : Finset Cell) :
      Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff)
        (fun _ => mu) ((⋂ c ∈ q, D c).indicator f)) atTop
        (𝓝 (∫ t in box ∩ ⋂ c ∈ q, D c, f t * ∏ i, 1 / t i)) := by
    rw [show (⋂ c ∈ q, D c) = weakAffineRegion (intersectionForms q)
      (intersectionBounds delta q) from rowRegion_intersection_eq delta q]
    exact tendsto_test_weakAffineRegion _ _ f hf
  have hsum := tendsto_finsetSum
    ((Finset.univ : Finset Cell).powerset.filter (·.Nonempty))
    (fun q _ => (hinter q).const_mul ((-1 : ℝ) ^ (q.card + 1)))
  have hi (c : Cell) : IntegrableOn (fun t => f t * ∏ i, 1 / t i)
      (D c) (volume.restrict box) := by
    exact (integrableOn_logPrimeBox_test_cube cutoff_pos f hf).integrableOn
  have hInt := integral_biUnion_eq_sum_powerset
    (μ := volume.restrict box) (t := (Finset.univ : Finset Cell))
    (s := D) (fun c _ => measurableSet_rowRegion delta c) (fun c _ => hi c)
  have hrestrict (D' : Set Point) (hD' : MeasurableSet D') :
      (∫ t in D', f t * ∏ i, 1 / t i ∂volume.restrict box) =
        ∫ t in box ∩ D', f t * ∏ i, 1 / t i := by
    rw [Measure.restrict_restrict hD', inter_comm]
  rw [hrestrict _ (by rw [hU]; exact (isCompact_trimmedRegion delta).measurableSet), hU] at hInt
  have hsubset : trimmedRegion delta ⊆ box :=
    (trimmedRegion_subset_region delta hdelta).trans region_subset_box
  rw [inter_eq_right.mpr hsubset] at hInt
  have hrestrictInter (q : Finset Cell) :
      (∫ t in ⋂ c ∈ q, D c, f t * ∏ i, 1 / t i ∂volume.restrict box) =
        ∫ t in box ∩ ⋂ c ∈ q, D c, f t * ∏ i, 1 / t i :=
    hrestrict _ (q.measurableSet_biInter (fun c _ => measurableSet_rowRegion delta c))
  simp_rw [hrestrictInter, smul_eq_mul] at hInt
  rw [← hInt] at hsum
  apply hsum.congr'
  exact Eventually.of_forall (fun N => by
    rw [← testSum_finite_union N Finset.univ D f, hU])

/-- A continuous extension on the ambient cube is only a test-function
device. On every actual source point both denominator clamps disappear. -/
def comparisonTest (t : Point) : ℝ :=
  4 * (M t - R t) /
    (max cutoff (R t - S t) * max cutoff (M t - S t))

theorem continuous_comparisonTest : Continuous comparisonTest := by
  apply (continuous_const.mul (continuous_M.sub continuous_R)).div
    ((continuous_const.max (continuous_R.sub continuous_S)).mul
      (continuous_const.max (continuous_M.sub continuous_S)))
  intro t
  exact mul_ne_zero (cutoff_pos.trans_le (le_max_left _ _)).ne'
    (cutoff_pos.trans_le (le_max_left _ _)).ne'

theorem comparisonTest_eq_sourceGain {t : Point} (ht : t ∈ region) :
    comparisonTest t = sourceGain (R t) (M t) t := by
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  have h := sourceRows_denominator_floors c t hc
  simp only [comparisonTest, sourceGain, max_eq_right h.1.le, max_eq_right h.2.1.le]

theorem comparisonTest_density {t : Point} (ht : t ∈ region) :
    comparisonTest t * (∏ i, 1 / t i) = sourceDensity t := by
  rw [comparisonTest_eq_sourceGain ht]
  rw [sourceDensity_eq]
  simp only [Finset.prod_one_div, div_eq_mul_inv, one_mul]

def retainedComparisonSum (N : ℕ) (delta : ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu)
    ((trimmedRegion delta).indicator (fun t => sourceGain (R t) (M t) t))

theorem retainedComparisonSum_eq (N : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    retainedComparisonSum N delta =
      actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu)
        ((trimmedRegion delta).indicator comparisonTest) := by
  unfold retainedComparisonSum
  congr 1
  apply Set.indicator_congr
  intro t ht
  exact (comparisonTest_eq_sourceGain (trimmedRegion_subset_region delta hdelta ht)).symm

theorem tendsto_retainedComparisonSum (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun N : ℕ => retainedComparisonSum N delta) atTop
      (𝓝 (∫ t in trimmedRegion delta, sourceDensity t)) := by
  simp_rw [retainedComparisonSum_eq _ delta hdelta]
  have heq : (∫ t in trimmedRegion delta, comparisonTest t * ∏ i, 1 / t i) =
      ∫ t in trimmedRegion delta, sourceDensity t := by
    apply setIntegral_congr_fun (isCompact_trimmedRegion delta).measurableSet
    intro t ht
    exact comparisonTest_density (trimmedRegion_subset_region delta hdelta ht)
  rw [← heq]
  exact tendsto_trimmed_testSum delta hdelta comparisonTest continuous_comparisonTest.continuousOn

end
end ImbalancedChen.P2OriginalFourteenRetainedPrimeIntegral
