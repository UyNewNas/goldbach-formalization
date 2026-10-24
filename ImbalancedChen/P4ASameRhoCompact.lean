import ImbalancedChen.ActualExtendedThirdCompactSignedDensityLimit
import ImbalancedChen.ActualRosserUpperGeneralLimit
import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.ActualFirstExitDensityProjection

/-!
Exact compact-policy identification at the counting interface. The compact
parameters e,h,m and the attachment precision epsilon are distinct. The full
raw density has w=0; attachedUpperCoefficient has w=N^(nu*epsilon^2).
The explicit finite decomposition below retains this difference.
This source is uncompiled and does not assert a full22 or currentK estimate.
-/

namespace ImbalancedChen.P4ASameRhoCompact

noncomputable section
open Filter Topology
open scoped Classical BigOperators

def retain (e h : ℝ) (m : ℕ) : ℕ → List ℕ → Bool :=
  fun N => actualExtendedThirdCompactUpperPolicy e h m N false

def fullDensity (e h : ℝ) (m N : ℕ) : ℝ :=
  reciprocalTotientDensity
    (fixedRoughSupport (retain e h m N) N N 0 ((N : ℝ) ^ thirdPrefixRho))
    (fixedRoughCoefficient (retain e h m N) N N 0 ((N : ℝ) ^ thirdPrefixRho))

def baselineDensity (e : ℝ) (m N : ℕ) : ℝ :=
  actualSmallRosserPlusDensity N N
    ((N : ℝ) ^ actualExtendedThirdInitialStopExponent e m)
    ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))

def roughDensity (e h : ℝ) (m N : ℕ) (w : ℝ) : ℝ :=
  reciprocalTotientDensity
    (fixedRoughSupport (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho))
    (fixedRoughCoefficient (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho))

theorem even_retained (e h : ℝ) (m N : ℕ) (history : List ℕ) :
    actualExtendedThirdCompactUpperPolicy e h m N true history = true := by
  exact actualExtendedThirdCompactUpperPolicy_even e h m N history

theorem attached_moduli_eq (e h nu r epsilon : ℝ) (m N : ℕ) :
    attachedUpperModuli nu r epsilon (retain e h m) (fun N => N) N =
      actualExtendedThirdCompactModuli e h m N N
        ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) := by
  rfl

theorem attached_coefficient_eq (e h nu r epsilon : ℝ) (m N : ℕ) :
    attachedUpperCoefficient nu r epsilon (retain e h m) (fun N => N) N =
      actualExtendedThirdCompactRho e h m N N
        ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
        ((N : ℝ) ^ (nu * epsilon)) := by
  rfl

theorem attached_moduli_eq_firstExit (e h nu r epsilon : ℝ) (m N : ℕ) :
    attachedUpperModuli nu r epsilon (retain e h m) (fun N => N) N =
      smallRoughModuli
        (actualSmallRosserSupport N N ((N : ℝ) ^ (nu * epsilon ^ 2)))
        (firstExitRetainedModuli (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N N ((N : ℝ) ^ (nu * epsilon ^ 2))
            ((N : ℝ) ^ (nu * r)))) := by
  unfold attachedUpperModuli actualSmallRoughModuli retain
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (actualExtendedThirdCompactUpperPolicy e h m N) (even_retained e h m N)]

theorem attached_coefficient_eq_firstExit (e h nu r epsilon : ℝ) (m N : ℕ) :
    attachedUpperCoefficient nu r epsilon (retain e h m) (fun N => N) N =
      smallRoughRho
        (actualSmallRosserSupport N N ((N : ℝ) ^ (nu * epsilon ^ 2)))
        (firstExitRetainedModuli (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N N ((N : ℝ) ^ (nu * epsilon ^ 2))
            ((N : ℝ) ^ (nu * r))))
        (fun d => (firstExitRetainedCoefficient
          (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N N ((N : ℝ) ^ (nu * epsilon ^ 2))
            ((N : ℝ) ^ (nu * r))) d : ℝ))
        (actualSmallRosserMinus N N ((N : ℝ) ^ (nu * epsilon ^ 2))
          ((N : ℝ) ^ (nu * epsilon)))
        (actualSmallRosserPlus N N ((N : ℝ) ^ (nu * epsilon ^ 2))
          ((N : ℝ) ^ (nu * epsilon))) := by
  exact actualExtendedThirdCompactRho_eq_firstExitAttachment e h m N N _ _ _

theorem rough_coefficient_eq_signed (e h : ℝ) (m N : ℕ) (w : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) d =
      (firstExitRetainedCoefficient (actualExtendedThirdCompactUpperPolicy e h m N)
        (roughPrimeUniverse N N w ((N : ℝ) ^ thirdPrefixRho)) d : ℝ) := by
  exact UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (actualExtendedThirdCompactUpperPolicy e h m N) (even_retained e h m N) N N w _ d

/-- The complete original-cap finite identity, including its initial baseline. -/
theorem full_density_finite_identity {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    fullDensity e h m N * Real.log (N : ℝ) / singularSeries N =
      baselineDensity e m N * Real.log (N : ℝ) / singularSeries N +
        actualExtendedThirdCompactResidualDensitySum N e h m := by
  have hs := actualExtendedThirdCompactPolicySaving hN hh he0 he hmesh
  rw [← actualExtendedThirdCompactRoughDensity_eq_policy,
    actualExtendedThirdInitialPolicy_eq_actualPlus he0 he hN m] at hs
  change (fullDensity e h m N - baselineDensity e m N) *
    Real.log (N : ℝ) / singularSeries N = _ at hs
  rw [← hs]
  ring

/-- A finite presieve defect, with its sign proved below. -/
def projectionDefect (e h : ℝ) (m N : ℕ) (w : ℝ) : ℝ :=
  actualSmallEulerProduct N N w * roughDensity e h m N w - fullDensity e h m N

/-- The literal signed attachment correction, not an absolute rough sum. -/
def attachmentCorrection (e h : ℝ) (m N : ℕ) (w L : ℝ) : ℝ :=
  ∑ d ∈ fixedRoughSupport (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho),
    (signAttachedValue
      (fixedRoughCoefficient (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) d)
      (actualSmallRosserMinusDensity N N w L)
      (actualSmallRosserPlusDensity N N w L) -
      fixedRoughCoefficient (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) d *
        actualSmallEulerProduct N N w) / (Nat.totient d : ℝ)

theorem projectionDefect_nonpos (e h : ℝ) (m N : ℕ) (w : ℝ)
    (hwz : w ≤ (N : ℝ) ^ thirdPrefixRho) :
    projectionDefect e h m N w ≤ 0 := by
  exact sub_nonpos.mpr (fixedRoughDensity_presieveProjection
    (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) hwz)

theorem physical_density_finite_identity (e h : ℝ) (m N : ℕ) (w L : ℝ) :
    physicalDensitySum (actualExtendedThirdCompactModuli e h m N N w
        ((N : ℝ) ^ thirdPrefixRho))
      (actualExtendedThirdCompactRho e h m N N w ((N : ℝ) ^ thirdPrefixRho) L) =
      fullDensity e h m N + projectionDefect e h m N w +
        attachmentCorrection e h m N w L := by
  have hcorr :
      physicalDensitySum (actualExtendedThirdCompactModuli e h m N N w
          ((N : ℝ) ^ thirdPrefixRho))
        (actualExtendedThirdCompactRho e h m N N w ((N : ℝ) ^ thirdPrefixRho) L) -
          actualSmallEulerProduct N N w * roughDensity e h m N w =
        attachmentCorrection e h m N w L := by
    rw [show actualExtendedThirdCompactModuli e h m N N w ((N : ℝ) ^ thirdPrefixRho) =
        actualSmallRoughModuli (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) from rfl,
      show actualExtendedThirdCompactRho e h m N N w ((N : ℝ) ^ thirdPrefixRho) L =
        actualSmallRoughRho (retain e h m N) N N w ((N : ℝ) ^ thirdPrefixRho) L from rfl,
      actualSmallRoughRho_density_eq]
    exact signSensitiveReciprocalTotientDensity_sub_eq _ _ _ _ _
  unfold projectionDefect
  linarith

/-- Counting's very same physical coefficient, with nu*r fixed to the actual
compact cutoff. All terms are finite and no density estimate is a premise. -/
theorem attached_density_finite_identity {e h nu r epsilon : ℝ} {m N : ℕ}
    (hcut : nu * r = thirdPrefixRho)
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    physicalDensitySum
        (attachedUpperModuli nu r epsilon (retain e h m) (fun N => N) N)
        (attachedUpperCoefficient nu r epsilon (retain e h m) (fun N => N) N) *
          Real.log (N : ℝ) / singularSeries N =
      baselineDensity e m N * Real.log (N : ℝ) / singularSeries N +
        actualExtendedThirdCompactResidualDensitySum N e h m +
        (projectionDefect e h m N ((N : ℝ) ^ (nu * epsilon ^ 2)) +
          attachmentCorrection e h m N ((N : ℝ) ^ (nu * epsilon ^ 2))
            ((N : ℝ) ^ (nu * epsilon))) * Real.log (N : ℝ) / singularSeries N := by
  rw [attached_moduli_eq, attached_coefficient_eq, hcut, physical_density_finite_identity]
  calc
    _ = fullDensity e h m N * Real.log (N : ℝ) / singularSeries N +
        (projectionDefect e h m N ((N : ℝ) ^ (nu * epsilon ^ 2)) +
          attachmentCorrection e h m N ((N : ℝ) ^ (nu * epsilon ^ 2))
            ((N : ℝ) ^ (nu * epsilon))) * Real.log (N : ℝ) / singularSeries N := by ring
    _ = _ := by rw [full_density_finite_identity hN hh he0 he hmesh]

def baselineLimit (e : ℝ) (m : ℕ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) /
      actualExtendedThirdInitialStopExponent e m) *
    MathlibNt.SieveTheory.suzukiContinuousUpperFactor
      ((thirdPrefixTheta - 2 * e) / actualExtendedThirdInitialStopExponent e m)

theorem initial_stop_pos_and_residual {e : ℝ} {m : ℕ}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    0 < actualExtendedThirdInitialStopExponent e m ∧
      1 < (thirdPrefixTheta - 2 * e) / actualExtendedThirdInitialStopExponent e m := by
  have hb := actualExtendedThirdInitialStopExponent_bounds he0 he m
  have hu : 0 < actualExtendedThirdInitialStopExponent e m := by
    have hlower := hb.2.2.1
    dsimp [thirdPrefixRho] at hlower
    linarith
  refine ⟨hu, (one_lt_div hu).mpr ?_⟩
  have hub := hb.2.2.2
  dsimp [thirdPrefixRho, thirdPrefixTheta] at hub ⊢
  linarith

/-- A concrete baseline supplier: the exact dyadic stop, cap N, and old level. -/
theorem tendsto_baseline {e : ℝ} {m : ℕ}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    Tendsto (fun N : ℕ => baselineDensity e m N * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (baselineLimit e m)) := by
  obtain ⟨hu, hs⟩ := initial_stop_pos_and_residual he0 he hmesh
  have hule : actualExtendedThirdInitialStopExponent e m ≤ 1 := by
    have h := (actualExtendedThirdInitialStopExponent_bounds he0 he m).2.2.2
    dsimp [thirdPrefixRho] at h
    linarith
  have hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ actualExtendedThirdInitialStopExponent e m ≤ (N : ℝ) := by
    filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono inf_le_left] with N hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr hule
  have hlim := tendsto_actualSmallRosserPlusDensity_general_normalized
    (actualExtendedThirdInitialStopExponent e m) hu
    ((thirdPrefixTheta - 2 * e) / actualExtendedThirdInitialStopExponent e m)
    hs (fun N => N) hcap
  simpa only [div_mul_cancel₀ _ hu.ne', baselineDensity, baselineLimit] using hlim

/-- The compact third policy's full signed density limit is derived, not posited.
It is not an identification with the manuscript's complete full22 policy. -/
theorem tendsto_full_density {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    Tendsto (fun N : ℕ => fullDensity e h m N * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m)) := by
  have hbase := tendsto_baseline he0 he hmesh
  have hcorr := tendsto_actualExtendedThirdCompactSignedDensityCorrection hh he0 he hmesh
  have hsum := hbase.add hcorr
  apply hsum.congr'
  filter_upwards [] with N
  change fullDensity e h m N * Real.log (N : ℝ) / singularSeries N =
    baselineDensity e m N * Real.log (N : ℝ) / singularSeries N +
      (fullDensity e h m N - baselineDensity e m N) * Real.log (N : ℝ) / singularSeries N
  ring

end
end ImbalancedChen.P4ASameRhoCompact
