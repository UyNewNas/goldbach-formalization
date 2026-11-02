import ImbalancedChen.P2FullMaskN48DeletedDisintegration
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests
import ImbalancedChen.P5ZU1011OriginalSixteenNativeHarmonic
import ImbalancedChen.P5ZU1011OriginalPairedRowPrimeTests

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original four-prime U11 carrier supplies the actual same17572
omega-minus-half harmonic gain. Its prime exclusions, labelled order,
complete reciprocal totient and Chen quarter are retained. The seven
literal fibre walls form a fixed mixed-affine prime test. No mean,
approximation estimate, parent licence or Chen endpoint is a premise.

The archived intersection identity at the end additionally consumes G's
UNEVALUATED archive-incidence proposals. The native convergence argument
uses the original fibre geometry and production prime-test theorem only;
it does not use those finite archive decisions.
-/

namespace ImbalancedChen.P2FullMaskActualNativeGain

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.PairedV2.FullMask.P2AdoptedUnion
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
open Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError
open Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve
open P2ActualSameMaskFloorFibreAccounting
open P2FullMaskN48DeletedOwner P2FullMaskN48DeletedDisintegration
open P5Z.U11Integral
open P5Z.U1011OriginalSixteenEligibilityState
open P5Z.U1011OriginalSixteenMixedGatePrimeTests
open P5Z.U1011OriginalSixteenArithmeticProducts
open P5Z.U1011OriginalSixteenNativeHarmonic

/-- Prime harmonic sums already supply one reciprocal factor for each
of t,u,z,w. The remaining z denominator and K/4 occur here once. -/
def gainProfile (x : Fin 4 → ℝ) : ℝ := ((K : ℝ) / 4) * gain x / x 2

theorem gainProfile_weighted (x : Fin 4 → ℝ) :
    gainProfile x * (∏ i, 1 / x i) = semanticKernel x := by
  simp only [gainProfile, semanticKernel, weight,
    Certificates.P2HistoricalFibreBinding.pairedChenQuarterWeight,
    Fin.prod_univ_succ, Finset.prod_empty, mul_one, div_eq_mul_inv,
    mul_inv_rev, pow_two]
  ring

theorem continuousOn_gainProfile : ContinuousOn gainProfile box :=
  (continuousOn_const.mul continuousOn_gain).div
    (continuous_apply 2).continuousOn (fun x hx => (coordinates_pos hx 2).ne')

theorem continuousOn_gainProfile_primeCube : ContinuousOn gainProfile
    (univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
  apply continuousOn_gainProfile.mono
  intro x hx
  change (fun _ => (a : ℝ)) ≤ x ∧ x ≤ (fun _ => (d : ℝ))
  constructor
  · intro i
    simpa only [Certificates.PairedV2.a, Rat.cast_div, Rat.cast_ofNat] using
      (hx i (mem_univ i)).1
  · intro i
    simpa only [Certificates.PairedV2.d, Rat.cast_div, Rat.cast_ofNat] using
      (hx i (mem_univ i)).2

/-- Exactly the original seven strict walls, including w+delta<z.
The finite row and delta are fixed before the target N. -/
def fibreGates (r : Row) (δ : ℝ) : Fin 7 → MixedGate :=
  ![⟨-ContinuousLinearMap.proj 0, -((tLower (indices r).1 : ℝ) + δ), true⟩,
    ⟨ContinuousLinearMap.proj 0, (tUpper (indices r).1 : ℝ) - δ, true⟩,
    ⟨-ContinuousLinearMap.proj 1, -((uLower (indices r).2 : ℝ) + δ), true⟩,
    ⟨ContinuousLinearMap.proj 1, (uUpper (indices r).2 : ℝ) - δ, true⟩,
    ⟨-ContinuousLinearMap.proj 3, -((a : ℝ) + δ), true⟩,
    ⟨ContinuousLinearMap.proj 3 - ContinuousLinearMap.proj 2, -δ, true⟩,
    ⟨ContinuousLinearMap.proj 2, (cutoff r : ℝ) - δ, true⟩]

theorem shrunkSupport_eq_mixed (r : Row) (δ : ℝ) :
    shrunkSupport r δ = mixedRegion (fibreGates r δ) := by
  ext x
  rw [mem_shrunkSupport_iff]
  change (∀ i : Fin 7, δ < wallMargin r x i) ↔
    ∀ i : Fin 7, (fibreGates r δ i).Holds x
  constructor
  · intro h i
    have hi := h i
    fin_cases i <;> dsimp [fibreGates, MixedGate.Holds, wallMargin] at * <;> linarith
  · intro h i
    have hi := h i
    fin_cases i <;> dsimp [fibreGates, MixedGate.Holds, wallMargin] at * <;> linarith

theorem shrunkSupport_subset_original (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    shrunkSupport r δ ⊆ originalDomain ∅ :=
  fun _ hx => fibre_mem_full_high_domain (shrunkSupport_subset_support r hδ hx)

theorem shrunkRegion_subset_original {δ : ℝ} (hδ : 0 ≤ δ) :
    shrunkRegion δ ⊆ originalDomain ∅ := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact shrunkSupport_subset_original r hδ hr

theorem shrunkRegion_disjoint_retained {δ : ℝ} (hδ : 0 ≤ δ) :
    Disjoint (shrunkRegion δ)
      (originalDomain P2N48SelectedFunctionalRemainder.actualMask) := by
  apply Set.disjoint_left.mpr
  intro x hx hd
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  obtain ⟨_ha, _hwz, _hzu, _huh, _hht, _htd, hnot⟩ := hd
  exact hnot (fibre_pair_in_deleted_mask (shrunkSupport_subset_support r hδ hr))

theorem shrunkSupport_subset_primeBox (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    shrunkSupport r δ ⊆ logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) :=
  (shrunkSupport_subset_original r hδ).trans
    P5Z.U1011OriginalSixteenFullHarmonic.domain_subset_box

def rowPrimeGain (δ : ℝ) (r : Row) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  ((shrunkSupport r δ).indicator gainProfile)

/-- A genuine mean for each actual original fibre, including every
strict equality-wall convention; no row-mean hypothesis is supplied. -/
theorem tendsto_rowPrimeGain (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (rowPrimeGain δ r) atTop
      (𝓝 (∫ x in shrunkSupport r δ, semanticKernel x)) := by
  have ht := tendsto_actualPrimeBox_mixedRegion (fibreGates r δ) gainProfile
    continuousOn_gainProfile_primeCube
  rw [← shrunkSupport_eq_mixed r δ,
    inter_eq_right.mpr (shrunkSupport_subset_primeBox r hδ)] at ht
  simpa only [rowPrimeGain, gainProfile_weighted] using ht

theorem shrunkSupports_disjoint {δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (fun r q : Row => Disjoint (shrunkSupport r δ) (shrunkSupport q δ)) := by
  intro r q hrq
  exact (FullMask.supports_pairwise_disjoint hrq).mono
    (shrunkSupport_subset_support r hδ) (shrunkSupport_subset_support q hδ)

/-- A reusable exact indicator identity. It preserves zero pieces and
is pointwise, so it also applies on arithmetic grid walls. -/
theorem sum_disjoint_indicator {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin 4 → ℝ))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    (∑ i, (S i).indicator f x) = (⋃ i, S i).indicator f x := by
  by_cases hx : x ∈ ⋃ i, S i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [indicator_of_mem hx, Finset.sum_eq_single i]
    · exact indicator_of_mem hi f
    · intro j _ hji
      exact indicator_of_notMem
        (fun hj => Set.disjoint_left.mp (hd hji) hj hi) f
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim
  · rw [indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)) f

def unionPrimeGain (δ : ℝ) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  ((shrunkRegion δ).indicator gainProfile)

theorem unionPrimeGain_eq_row_sum {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    unionPrimeGain δ N = ∑ r : Row, rowPrimeGain δ r N := by
  unfold unionPrimeGain rowPrimeGain actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum,
    sum_disjoint_indicator (fun r => shrunkSupport r δ)
      (shrunkSupports_disjoint hδ) gainProfile]
  rfl

theorem retainedGain_eq_row_sum {δ : ℝ} (hδ : 0 ≤ δ) :
    retainedGain (shrunkRegion δ) =
      ∑ r : Row, ∫ x in shrunkSupport r δ, semanticKernel x := by
  unfold retainedGain shrunkRegion
  exact integral_iUnion_fintype (fun r => (shrunkSupport_isOpen r δ).measurableSet)
    (shrunkSupports_disjoint hδ) (fun r =>
      (integrableOn_semanticKernel_support r).mono_set
        (shrunkSupport_subset_support r hδ))

theorem tendsto_unionPrimeGain {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (unionPrimeGain δ) atTop (𝓝 (retainedGain (shrunkRegion δ))) := by
  rw [retainedGain_eq_row_sum hδ]
  have ht := tendsto_finsetSum (Finset.univ : Finset Row)
    (fun r _ => tendsto_rowPrimeGain r hδ)
  exact ht.congr' (Eventually.of_forall (fun N => (unionPrimeGain_eq_row_sum hδ N).symm))

/-- Independently defined on the production U11Adaptive.source, with
the complete original four-prime totient. The inner fibre is selected
by its actual coordinates, not by a saved-floor or archive ordinal. -/
def nativeGain (δ : ℝ) (N : ℕ) : ℝ :=
  nativeHarmonicSum N (fun _ => False) ((shrunkRegion δ).indicator gainProfile)

theorem nativeGain_eq_literal_source (δ : ℝ) (N : ℕ) :
    nativeGain δ N = ∑ t ∈ P5Z.U11Adaptive.source N (fun _ => False),
      (shrunkRegion δ).indicator gainProfile (coordinates N t) /
        (Nat.totient (t.1.1 * t.1.2 * t.2.1 * t.2.2) : ℝ) :=
  nativeHarmonicSum_eq_literal_four_product N (fun _ => False) _

theorem nativeGain_eq_unionPrimeGain {δ : ℝ} (hδ : 0 ≤ δ) {N : ℕ} (hN : 1 < N) :
    nativeGain δ N = unionPrimeGain δ N := by
  rw [nativeGain, nativeHarmonicSum_eq_actualPrimeBox hN]
  have hind : (originalDomain ∅).indicator ((shrunkRegion δ).indicator gainProfile) =
      (shrunkRegion δ).indicator gainProfile := by
    funext x
    by_cases hx : x ∈ shrunkRegion δ
    · rw [indicator_of_mem (shrunkRegion_subset_original hδ hx)]
    · by_cases hd : x ∈ originalDomain ∅ <;> simp [hx, hd]
  rw [hind]
  rfl

/-- The same gain has zero contribution on the original RETAINED
complement. This is source separation, not a vanishing Y6 count. -/
theorem nativeGain_on_retained_source_zero {δ : ℝ} (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 1 < N) :
    nativeHarmonicSum N
      (P5Z.U1011OriginalPairedRowPrimeTests.nativeMask
        P2N48SelectedFunctionalRemainder.actualMask N)
      ((shrunkRegion δ).indicator gainProfile) = 0 := by
  rw [P5Z.U1011OriginalPairedRowPrimeTests.nativeHarmonicSum_eq_fixedMask_box hN]
  have hind :
      (originalDomain P2N48SelectedFunctionalRemainder.actualMask).indicator
        ((shrunkRegion δ).indicator gainProfile) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hd : x ∈ originalDomain P2N48SelectedFunctionalRemainder.actualMask
    · have hx : x ∉ shrunkRegion δ := fun hx =>
        Set.disjoint_left.mp (shrunkRegion_disjoint_retained hδ) hx hd
      simp only [indicator_of_mem hd, indicator_of_notMem hx]
    · exact indicator_of_notMem hd _
  rw [hind]
  simp only [actualPrimeBoxTestSum, mul_zero, Finset.sum_const_zero]

/-- The full labelled original carrier, not a rational ledger, has the
true same-mask retained semantic integral as its harmonic limit. -/
theorem tendsto_nativeGain {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (nativeGain δ) atTop (𝓝 (retainedGain (shrunkRegion δ))) := by
  apply (tendsto_unionPrimeGain hδ).congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (nativeGain_eq_unionPrimeGain hδ hN).symm

theorem tendsto_nativeGain_full :
    Tendsto (nativeGain 0) atTop (𝓝 actualExtraFibreGain) := by
  simpa only [shrunkRegion_zero, retainedGain, actualExtraFibreGain,
    unionSemanticIntegral] using tendsto_nativeGain (δ := 0) le_rfl

def nativeArchivedPieceGain (δ : ℝ) (r : Row) (s : ArchivedRow) (N : ℕ) : ℝ :=
  nativeHarmonicSum N (fun _ => False)
    ((collaredArchivedPiece δ r s).indicator gainProfile)

theorem sum_archived_indicators {δ : ℝ} (hδ : 0 ≤ δ) (x : Fin 4 → ℝ) :
    (∑ r : Row, ∑ s : ArchivedRow,
      (collaredArchivedPiece δ r s).indicator gainProfile x) =
        (shrunkRegion δ).indicator gainProfile x := by
  calc
    _ = ∑ r : Row, (shrunkSupport r δ).indicator gainProfile x := by
      apply Finset.sum_congr rfl
      intro r _
      rw [sum_disjoint_indicator (collaredArchivedPiece δ r)
        (collaredArchivedPieces_pairwise_disjoint δ r),
        ← shrunk_support_eq_archived_union r hδ]
    _ = _ := sum_disjoint_indicator (fun r => shrunkSupport r δ)
      (shrunkSupports_disjoint hδ) gainProfile x

theorem nativeHarmonicSum_fintypeSum {ι : Type*} [Fintype ι]
    (N : ℕ) (f : ι → (Fin 4 → ℝ) → ℝ) :
    nativeHarmonicSum N (fun _ => False) (fun x => ∑ i, f i x) =
      ∑ i, nativeHarmonicSum N (fun _ => False) (f i) := by
  unfold nativeHarmonicSum
  simp_rw [Finset.sum_div]
  exact Finset.sum_comm

/-- Actual finite-source disintegration, before taking a limit. Distinct
fine/coarse producer domains are intersected, never identified. This
leaf inherits G's unexecuted original archive incidence decisions. -/
theorem nativeGain_eq_archived_sum {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    nativeGain δ N = ∑ r : Row, ∑ s : ArchivedRow, nativeArchivedPieceGain δ r s N := by
  have hind : (shrunkRegion δ).indicator gainProfile = fun x =>
      ∑ r : Row, ∑ s : ArchivedRow,
        (collaredArchivedPiece δ r s).indicator gainProfile x := by
    funext x
    exact (sum_archived_indicators hδ x).symm
  rw [nativeGain, hind, nativeHarmonicSum_fintypeSum]
  apply Finset.sum_congr rfl
  intro r _
  exact nativeHarmonicSum_fintypeSum N _

end

end ImbalancedChen.P2FullMaskActualNativeGain
