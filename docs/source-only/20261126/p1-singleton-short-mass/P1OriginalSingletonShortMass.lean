import ImbalancedChen.P1OriginalSingletonFixedScaleTransport

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The existing shortSequence_mass is applied to the original singleton
short-position carrier, rowRoles, hbCutoff and beforeHBCutoff. Ordered
collisions, signs, unit blocks, numerator logs and Mellin phases remain
inside the original shortSequence. No new short coefficient is defined.

The fixed scale is the product of ALL block lower endpoints. Its actual
M and short-block bounds come from FixedScaleTransport. The exact short
rectangle cardinality is M, so there is no additional 2^s factor.

K (and eps for the second theorem) precedes the physical-N threshold;
kap, B, the chart, HB row, active tuple, selected positions and xi follow
it. These are finite coefficient bounds, uniform in the unchanged Q/rho
of the existing dictionary. No rough, P2, strip, Fourier or whole-row
discrepancy bound is asserted.
-/

namespace ImbalancedChen.P1OriginalSingletonShortMass
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
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open Part3.TwoLongActualHBShortMass
  (ShortPositions shortScale shortSupport shortSequence shortSequence_mass)
open P4BOriginalNoMediumPairRows (short_card)
open P1OriginalSingletonFixedScaleTransport
  (eventually_actual_singleton_fixed_scale_transport)

/-- The actual singleton short coefficient has the original finite L1
bound, at the fixed complete-rectangle scale and for every real xi.
Only the given tuple is active; no aggregate or whole-rectangle activity
is assumed. -/
theorem eventually_actual_singleton_short_mass (K : ℕ)
    {kappa kap0 zeta : ℝ}
    (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta / 10000)
    (hzeta : zeta ≤ 1 / 400) (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap B N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      ∀ xi : Fin (2*(j+1)) → ℝ,
      let X0 : ℝ := shortScale bs
      (∑ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
        ‖shortSequence (fun a : ShortPositions i k => bs a.val)
          (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
          (fun a => xi a.val) (fun a => rowRoles j a.val) m‖) ≤
        X0^(40*zeta) * (1 + Real.log X0)^4 := by
  filter_upwards [eventually_actual_singleton_fixed_scale_transport K 1
    (by norm_num) hkappa hsmall hzeta htrim] with N htransport
  intro kap hkap B cj j bs ns i k hj hik hns hactive hshort xi
  let X0 : ℝ := shortScale bs
  obtain ⟨hx, _, _, _, hM, hcap, _⟩ :=
    htransport kap hkap B cj j bs ns i k hj hik hns hactive hshort
  have hcard := short_card i k hik
  have hj' := Finset.mem_range.mp hj
  have hfour : Fintype.card (ShortPositions i k) ≤ 4 := by omega
  have hlog : 0 ≤ Real.log X0 := Real.log_nonneg hx.le
  have hL : 1 ≤ 1 + Real.log X0 := by linarith only [hlog]
  calc
    _ ≤ (shortScale (fun a : ShortPositions i k => bs a.val) : ℝ) *
        (1 + Real.log X0)^Fintype.card (ShortPositions i k) :=
      shortSequence_mass (fun a : ShortPositions i k => bs a.val)
        (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
        (fun a => xi a.val) (fun a => rowRoles j a.val) hx.le hcap
    _ ≤ (shortScale (fun a : ShortPositions i k => bs a.val) : ℝ) *
        (1 + Real.log X0)^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hfour) (Nat.cast_nonneg _)
    _ ≤ X0^(40*zeta) * (1 + Real.log X0)^4 :=
      mul_le_mul_of_nonneg_right hM (pow_nonneg (zero_le_one.trans hL) 4)

/-- The SAME coefficient mass multiplied by the actual Brun support
square at halfOrder X0. This pays only the finite short/Brun prefactor;
the modulus, profile, rough-mean and Fourier budgets remain separate. -/
theorem eventually_actual_singleton_brun_short_mass (K : ℕ)
    (eps : ℝ) (heps : 0 < eps) {kappa kap0 zeta : ℝ}
    (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta / 10000)
    (hzeta : zeta ≤ 1 / 400) (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap B N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      ∀ xi : Fin (2*(j+1)) → ℝ,
      let X0 : ℝ := shortScale bs
      let Z := beforeHBCutoff K [cj]
      (Z^(2*halfOrder X0+1))^2 *
        (∑ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
          ‖shortSequence (fun a : ShortPositions i k => bs a.val) Z
            (fun _ => hbCutoff cj) (fun a => xi a.val)
            (fun a => rowRoles j a.val) m‖) ≤
        X0^(40*zeta+2*eps) * (1 + Real.log X0)^4 := by
  filter_upwards [eventually_actual_singleton_short_mass K hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_scale_transport K eps heps
      hkappa hsmall hzeta htrim] with N hmass htransport
  intro kap hkap B cj j bs ns i k hj hik hns hactive hshort xi
  let X0 : ℝ := shortScale bs
  let Z := beforeHBCutoff K [cj]
  let Y := Z^(2*halfOrder X0+1)
  have hm := hmass kap hkap B cj j bs ns i k hj hik hns hactive hshort xi
  obtain ⟨hx, _, _, _, _, _, _, _, hZ, hsupport⟩ :=
    htransport kap hkap B cj j bs ns i k hj hik hns hactive hshort
  have hxp : 0 < X0 := zero_lt_one.trans hx
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hY2 : Y^2 ≤ X0^(2*eps) := by
    calc
      Y^2 ≤ (X0^eps)^2 := pow_le_pow_left₀ hY hsupport 2
      _ = X0^(2*eps) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
        congr 1
        ring
  have hL : 0 ≤ 1 + Real.log X0 := by
    linarith only [Real.log_nonneg hx.le]
  calc
    _ ≤ Y^2 * (X0^(40*zeta) * (1 + Real.log X0)^4) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg Y)
    _ ≤ X0^(2*eps) * (X0^(40*zeta) * (1 + Real.log X0)^4) :=
      mul_le_mul_of_nonneg_right hY2
        (mul_nonneg (Real.rpow_nonneg hxp.le _) (pow_nonneg hL 4))
    _ = (X0^(2*eps) * X0^(40*zeta)) * (1 + Real.log X0)^4 :=
      (mul_assoc _ _ _).symm
    _ = X0^(2*eps+40*zeta) * (1 + Real.log X0)^4 := by
      rw [← Real.rpow_add hxp]
    _ = X0^(40*zeta+2*eps) * (1 + Real.log X0)^4 := by
      rw [add_comm (2*eps) (40*zeta)]

end
end ImbalancedChen.P1OriginalSingletonShortMass
