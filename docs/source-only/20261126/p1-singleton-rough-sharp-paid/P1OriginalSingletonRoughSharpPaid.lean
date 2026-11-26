import ImbalancedChen.P1OriginalSingletonSharpComparisonPaid

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The paid historical sharp-to-smooth difference and the complete paid
rough smooth norm are combined at accuracy+1. Their smoothing orders
are both stripSmoothingOrder (accuracy+1), while their original Brun
cutoffOrder, physical N, historical moduli/coefficient and actual
shortSequence are identical. The smooth theorem is used at label 0,
so its two profiles reduce to the profile false pair in the strip bill.

All fixed orders precede one physical-N threshold, which also supplies
log X0 >= 2 from the original active-rectangle scale. The original two
long-frequency logarithmic bands are retained. No analytic estimate,
coefficient-mass bound or payment conclusion is assumed or re-proved.

The conclusion is the local sharp-profile rough norm only. Native
rectangle equality, Fourier attachment and the outer HB sum remain
outside this statement, as do the inherited missing-source and
unique-owner import-closure obligations.
-/

namespace ImbalancedChen.P1OriginalSingletonRoughSharpPaid
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile rowRoles)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale shortSupport shortSequence)
open Part3.TwoLongHBMellinBrunProfiles (leftMellin rightMellin)
open Part3.TwoLongTransitionMellinN2 (profile)
open P4BOriginalNoMediumPairRows (longPositions)
open P4BOriginalSharpLongProfiles (sharpProfile)
open P1OriginalHistoricalTwoLongRoughComparison (historicalRoughSum)
open P1OriginalSingletonSharpComparisonPaid
  (stripSmoothingOrder eventually_actual_singleton_sharp_comparison_paid)
open P1OriginalSingletonRoughSmoothPaid (eventually_actual_singleton_rough_smooth_paid)
open P1OriginalSingletonFixedRectangleScale (eventually_actual_singleton_fixed_rectangle_level)

/-- The complete local sharp-profile rough norm for the original active
singleton two-long branch, with the same signed historical coefficient
and exact actual short sequence. The threshold is uniform in all the
subsequently quantified historical parameters and frequencies. -/
theorem eventually_actual_singleton_rough_sharp_paid
    (accuracy frequencyOrder cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      longPositions (originalMediumHigh zeta [cj]) bs = {i,k} →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ)
        (w z L t₁ t₂ : ℝ) (log₁ log₂ : Bool)
        (xi : Fin (2*(j+1)) → ℝ),
      |t₁| ≤ (Real.log (shortScale bs : ℝ))^frequencyOrder →
      |t₂| ≤ (Real.log (shortScale bs : ℝ))^frequencyOrder →
      let X0 : ℝ := shortScale bs
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let shortBlocks := fun a : ShortPositions i k => bs a.val
      let shortCutoffs := fun _ : ShortPositions i k => hbCutoff cj
      let shortFrequencies := fun a : ShortPositions i k => xi a.val
      let shortRoles := fun a : ShortPositions i k => rowRoles j a.val
      let alpha := shortSequence shortBlocks Z shortCutoffs shortFrequencies shortRoles
      ‖historicalRoughSum levelB old fresh N cap w z L
          (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂)
          U V Z (shortSupport shortBlocks) alpha‖ ≤
        X0/(Real.log X0)^accuracy := by
  let B := stripSmoothingOrder (accuracy+1)
  have hB : 1 ≤ B := by dsimp only [B, stripSmoothingOrder]; omega
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_sharp_comparison_paid
      (accuracy+1) cutoffOrder hkappa hsmall hzeta htrim,
    eventually_actual_singleton_rough_smooth_paid (accuracy+1) B frequencyOrder
      cutoffOrder hB hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*Real.exp (2 : ℝ)))]
      with N hsharp hsmooth hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
    levelB old fresh cap w z L t₁ t₂ log₁ log₂ xi ht₁ ht₂
  let X0 : ℝ := shortScale bs
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  let bS := fun a : ShortPositions i k => bs a.val
  let ys := fun _ : ShortPositions i k => hbCutoff cj
  let xis := fun a : ShortPositions i k => xi a.val
  let rs := fun a : ShortPositions i k => rowRoles j a.val
  let alpha := shortSequence bS Z ys xis rs
  let ell := Real.log X0
  let delta := (ell^B)⁻¹
  let rough := historicalRoughSum levelB old fresh N cap w z L
    (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂)
    U V Z (shortSupport bS) alpha
  let smooth := historicalRoughSum levelB old fresh N cap w z L
    (profile false log₁ delta U t₁) (profile false log₂ delta V t₂)
    U V Z (shortSupport bS) alpha
  obtain ⟨_, _, _, htrimX, _, hx, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hExp : Real.exp (2 : ℝ) ≤ X0 := by linarith only [hlarge, htrimX]
  have hlog2 : (2 : ℝ) ≤ ell := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (2 : ℝ)) hExp
  have hell0 : 0 < ell := by linarith
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  have hdiff : ‖rough-smooth‖ ≤ X0/ell^(accuracy+1) :=
    hsharp kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
      levelB old fresh cap w z L t₁ t₂ log₁ log₂ xi
  have hsm : ‖smooth‖ ≤ X0/ell^(accuracy+1) := by
    simpa only [leftMellin, rightMellin,
      show decide ((0 : Fin 3) = 1) = false from rfl,
      show decide ((0 : Fin 3) = 2) = false from rfl] using
      (hsmooth kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
        levelB old fresh cap w z L t₁ t₂ (0 : Fin 3) log₁ log₂ xi ht₁ ht₂)
  have htriangle : ‖rough‖ ≤ ‖rough-smooth‖+‖smooth‖ := by
    simpa only [sub_add_cancel] using norm_add_le (rough-smooth) smooth
  calc
    _ ≤ ‖rough-smooth‖+‖smooth‖ := htriangle
    _ ≤ X0/ell^(accuracy+1)+X0/ell^(accuracy+1) := add_le_add hdiff hsm
    _ = 2*X0/ell^(accuracy+1) := by ring
    _ = (2/ell)*(X0/ell^accuracy) := by rw [pow_succ]; field_simp [hell0.ne']; ring
    _ ≤ 1*(X0/ell^accuracy) := mul_le_mul_of_nonneg_right
      ((div_le_one hell0).mpr hlog2) (by positivity)
    _ = _ := one_mul _

end
end ImbalancedChen.P1OriginalSingletonRoughSharpPaid
