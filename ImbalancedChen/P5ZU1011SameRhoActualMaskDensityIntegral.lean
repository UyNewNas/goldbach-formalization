import ImbalancedChen.P5ZU1011SameRhoFixedCellPolyhedralIntegral
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic

/-!
# Same physical native density: actual fixed-row geometric integral

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Choose a STATIC finite subfamily S of the original adopted outer rows,
then the finite mesh and positive rational eta, and only then let N grow.
U10's low band remains entirely unmasked. U11 uses the literal native
pullback of the same row union, with all half-open endpoints retained.

Direct mixed-gate PNT supplies the fixed-cell ordinary-F regional limits.
The proved unique row ownership gives exact subtraction for the retained
high band. The actual native source and full natural phi weights are
attached before taking a limit. Finally the uniformly vanishing density
error is added back, yielding the integral of the ordinary-F step kernel
for the SAME native sigma. No arbitrary moving-mask integral theorem,
strong PP licence, enhanced H248 comparison or currentK bound is asserted.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoActualMaskDensityIntegral

noncomputable section

open Set MeasureTheory Classical Filter Topology
open scoped BigOperators
open U11Integral U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenNativeHarmonic
open U1011OriginalPairedRowPrimeTests
open U1011OriginalPairedFixedMaskHarmonic (outerUnion keptDomain rowDomain)
open U1011SameRhoDensityErrorZero U1011SameRhoFixedCellPolyhedralIntegral
open Certificates.PairedV2

abbrev Row := FullMask.Row

/-- The ORIGINAL six high-band support tests, independent of any policy
state or table. Weak lower walls and strict upper walls are literal. -/
def highGates : Fin 6 → MixedGate :=
  ![⟨-ContinuousLinearMap.proj 3, -(417 / 5000 : ℝ), false⟩,
    ⟨ContinuousLinearMap.proj 3 - ContinuousLinearMap.proj 2, 0, true⟩,
    ⟨ContinuousLinearMap.proj 2 - ContinuousLinearMap.proj 1, 0, true⟩,
    ⟨ContinuousLinearMap.proj 1, 19 / 125, true⟩,
    ⟨-ContinuousLinearMap.proj 0, -(19 / 125 : ℝ), false⟩,
    ⟨ContinuousLinearMap.proj 0, 59 / 250, true⟩]

theorem original_high_eq_mixed : originalDomain ∅ = mixedRegion highGates := by
  ext v
  simp [originalDomain, mixedRegion, highGates, MixedGate.Holds,
    Fin.forall_fin_succ, neg_le_neg_iff, sub_lt_zero] <;> tauto

def joinedGates {ι κ : Type*} (g : ι → MixedGate) (h : κ → MixedGate) : ι ⊕ κ → MixedGate
  | .inl i => g i
  | .inr k => h k

theorem joined_region {ι κ : Type*} (g : ι → MixedGate) (h : κ → MixedGate) :
    mixedRegion (joinedGates g h) = mixedRegion g ∩ mixedRegion h := by
  ext v
  constructor
  · intro hv
    exact ⟨fun i => hv (.inl i), fun k => hv (.inr k)⟩
  · rintro ⟨hg, hh⟩ k
    cases k with
    | inl i => exact hg i
    | inr k => exact hh k

def removedGates (r : Row) : Fin 6 ⊕ Fin 4 → MixedGate := joinedGates highGates (rowGates r)

theorem rowDomain_eq_mixed (r : Row) : rowDomain r = mixedRegion (removedGates r) := by
  rw [removedGates, joined_region, ← original_high_eq_mixed, ← rowRegion_eq_mixed]
  rfl

def keptMass (S : Finset Row) (n : ℕ) (eta : ℚ) (N : ℕ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
    ((keptDomain S).indicator (ordinaryStep n eta))

def keptIntegral (S : Finset Row) (n : ℕ) (eta : ℚ) : ℝ :=
  ∫ v in cube ∩ keptDomain S, ordinaryStep n eta v * logWeight v

def fixedJointIntegral (S : Finset Row) (n : ℕ) (eta : ℚ) : ℝ :=
  ∫ v in U1011OriginalJointHarmonic.jointDomain S, ordinaryStep n eta v * logWeight v

theorem keptMass_eq_difference (S : Finset Row) (n N : ℕ) (eta : ℚ) :
    keptMass S n eta N = regionalMass highGates n eta N -
      ∑ r ∈ S, regionalMass (removedGates r) n eta N := by
  have hsplit : regionalMass highGates n eta N = keptMass S n eta N +
      ∑ r ∈ S, regionalMass (removedGates r) n eta N := by
    unfold regionalMass keptMass actualPrimeBoxTestSum
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [← Finset.mul_sum, ← mul_add]
    have hp := U1011OriginalPairedFixedMaskHarmonic.kept_indicator_split S
      (ordinaryStep n eta) (actualPrimeTupleLog N q)
    simpa only [U1011OriginalPairedFixedMaskHarmonic.domain, original_high_eq_mixed,
      rowDomain_eq_mixed] using congrArg (fun z => (∏ i, 1 / ((q i : ℝ) - 1)) * z) hp
  linarith only [hsplit]

theorem keptIntegral_eq_difference (S : Finset Row) (n : ℕ) (eta : ℚ) :
    keptIntegral S n eta = regionalIntegral highGates n eta -
      ∑ r ∈ S, regionalIntegral (removedGates r) n eta := by
  let w : LogFour → ℝ := fun v => ordinaryStep n eta v * logWeight v
  have hi := integrableOn_weighted_step n eta
  have hD : MeasurableSet (originalDomain ∅) := measurableSet_originalDomain ∅ measurableSet_empty
  have hK := U1011OriginalPairedFixedMaskHarmonic.measurableSet_keptDomain S
  have hR (r : Row) := U1011OriginalPairedFixedMaskHarmonic.measurableSet_rowDomain r
  have hsplit : regionalIntegral highGates n eta = keptIntegral S n eta +
      ∑ r ∈ S, regionalIntegral (removedGates r) n eta := by
    calc
      _ = ∫ v in cube, (originalDomain ∅).indicator w v := by
        rw [setIntegral_indicator hD]
        simp only [regionalIntegral, ← original_high_eq_mixed, w]
      _ = ∫ v in cube, (keptDomain S).indicator w v + ∑ r ∈ S, (rowDomain r).indicator w v := by
        apply integral_congr_ae
        exact Eventually.of_forall (U1011OriginalPairedFixedMaskHarmonic.kept_indicator_split S w)
      _ = (∫ v in cube, (keptDomain S).indicator w v) +
          ∑ r ∈ S, ∫ v in cube, (rowDomain r).indicator w v := by
        rw [integral_add (hi.indicator hK)
          (integrable_finsetSum S (fun r _ => hi.indicator (hR r))),
          integral_finsetSum S (fun r _ => hi.indicator (hR r))]
      _ = _ := by
        rw [setIntegral_indicator hK]
        apply congrArg (fun z => keptIntegral S n eta + z)
        apply Finset.sum_congr rfl
        intro r hr
        rw [setIntegral_indicator (hR r)]
        simp only [regionalIntegral, ← rowDomain_eq_mixed, w]
  linarith only [hsplit]

theorem tendsto_keptMass_fixedRows (S : Finset Row) (n : ℕ) (eta : ℚ) :
    Tendsto (keptMass S n eta) atTop (𝓝 (keptIntegral S n eta)) := by
  have ht := (tendsto_regional_ordinaryStep highGates n eta).sub
    (tendsto_finsetSum S (fun r _ => tendsto_regional_ordinaryStep (removedGates r) n eta))
  rw [← keptIntegral_eq_difference] at ht
  exact ht.congr' (Eventually.of_forall (fun N => (keptMass_eq_difference S n N eta).symm))

theorem cube_inter_low : cube ∩ U1011OriginalSixteenU10Geometry.domain10 =
    U1011OriginalSixteenU10Geometry.domain10 := by
  apply inter_eq_right.mpr
  intro v hv
  rw [cube_eq_literal]
  exact U1011OriginalSixteenU10Geometry.domain10_subset_box hv

theorem cube_inter_kept (S : Finset Row) : cube ∩ keptDomain S = keptDomain S := by
  apply inter_eq_right.mpr
  intro v hv
  rw [cube_eq_literal]
  exact U1011OriginalSixteenFullHarmonic.domain_subset_box hv.1

theorem fixedJointIntegral_eq_band_sum (S : Finset Row) (n : ℕ) (eta : ℚ) :
    fixedJointIntegral S n eta = regionalIntegral U1011OriginalSixteenU10Geometry.supportGates n eta +
      keptIntegral S n eta := by
  have hK := U1011OriginalPairedFixedMaskHarmonic.measurableSet_keptDomain S
  have hdis : Disjoint U1011OriginalSixteenU10Geometry.domain10 (keptDomain S) := by
    rw [← U1011OriginalPairedFixedMaskHarmonic.originalDomain_outerUnion S]
    exact U1011OriginalJointHarmonic.domain10_disjoint_originalDomain _
  have hi := integrableOn_weighted_step n eta
  have hi10 : IntegrableOn (fun v => ordinaryStep n eta v * logWeight v)
      U1011OriginalSixteenU10Geometry.domain10 := hi.mono_set (by
    intro v hv
    exact (inter_eq_right.mp cube_inter_low) hv)
  have hi11 : IntegrableOn (fun v => ordinaryStep n eta v * logWeight v) (keptDomain S) :=
    hi.mono_set (inter_eq_right.mp (cube_inter_kept S))
  unfold fixedJointIntegral U1011OriginalJointHarmonic.jointDomain
  rw [U1011OriginalPairedFixedMaskHarmonic.originalDomain_outerUnion S,
    setIntegral_union hdis hK hi10 hi11]
  simp only [regionalIntegral, ← U1011OriginalSixteenU10Geometry.domain10_eq_mixed,
    cube_inter_low, keptIntegral, cube_inter_kept]

/-- Arithmetic attachment uses the true reversed slots and the SAME
fixed geometric row mask. Only its high-band source is removed. -/
theorem ordinaryNativeMass_eq_actual_band_means {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (n : ℕ) (eta : ℚ) :
    ordinaryNativeMass n N eta (nativeMask (outerUnion S) N) =
      regionalMass U1011OriginalSixteenU10Geometry.supportGates n eta N + keptMass S n eta N := by
  rw [ordinaryNativeMass_eq_nativeJoint_step eta hN,
    U1011OriginalJointHarmonic.nativeJoint_eq_native10_add_native11 hN,
    U1011OriginalSixteenU10Geometry.native10_eq_actualPrimeBox hN,
    nativeHarmonicSum_eq_fixedMask_box hN,
    U1011OriginalPairedFixedMaskHarmonic.originalDomain_outerUnion S]
  simp only [regionalMass, ← U1011OriginalSixteenU10Geometry.domain10_eq_mixed, keptMass]

theorem tendsto_ordinaryNativeMass_actual_fixedRows (S : Finset Row) (n : ℕ) (eta : ℚ) :
    Tendsto (fun N : ℕ => ordinaryNativeMass n N eta (nativeMask (outerUnion S) N))
      atTop (𝓝 (fixedJointIntegral S n eta)) := by
  rw [fixedJointIntegral_eq_band_sum]
  have ht := (tendsto_regional_ordinaryStep U1011OriginalSixteenU10Geometry.supportGates n eta).add
    (tendsto_keptMass_fixedRows S n eta)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (ordinaryNativeMass_eq_actual_band_means hN S n eta).symm

/-- Actual same-sigma density integral. S, finite mesh and eta are fixed
BEFORE N; no target density, PP bound or boundary estimate is assumed. -/
theorem tendsto_actual_same_sigma_density_integral (S : Finset Row) (n : ℕ) (eta : ℚ)
    (heta : 0 < eta) :
    Tendsto (fun N : ℕ => normalizedPhysicalDensity n N eta (nativeMask (outerUnion S) N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (fixedJointIntegral S n eta)) := by
  have herr := tendsto_normalizedPhysicalDensity_sub_ordinaryNativeMass n eta heta
    (fun N => nativeMask (outerUnion S) N)
  have hmass := (tendsto_ordinaryNativeMass_actual_fixedRows S n eta).mono_left inf_le_left
  simpa only [sub_add_cancel, zero_add] using herr.add hmass

/-- Concrete original all-row mask, retaining its literal N-dependent
prime-coordinate pullback. This is not a licence for arbitrary moving E. -/
theorem tendsto_actual_adopted_same_sigma_density_integral (n : ℕ) (eta : ℚ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => normalizedPhysicalDensity n N eta
      (FullMask.P1E0E1.deletionMask (N : ℝ)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (fixedJointIntegral (Finset.univ : Finset Row) n eta)) := by
  simpa only [U1011OriginalPairedFixedMaskHarmonic.outerUnion_all, nativeMask_actual_adopted] using
    tendsto_actual_same_sigma_density_integral (Finset.univ : Finset Row) n eta heta

end

end ImbalancedChen.P5Z.U1011SameRhoActualMaskDensityIntegral
