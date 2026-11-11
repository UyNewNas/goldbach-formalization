import ImbalancedChen.P3HBActualTwoAxisLocalization
import ImbalancedChen.P3HBSmoothTensorQuantitativeL1
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
P3.6; frozen manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b, prime-product
completion §4 (F), six original HB logarithmic coordinates.
SOURCE_ONLY, UNCOMPILED, KERNEL UNVERIFIED.
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The SAME genuine coupled two-axis mass is bounded in L1 using geometry
jet bounds ONLY on the genuine closed six-coordinate HB support box.
The old bound required jet estimates on all of R^6. Here the four
separated HB tensors provide a global integrable majorant, while exact
support localization makes the majorization valid outside the box too.

This still assumes genuine W coordinate differentiability, continuous
jets, and local bounds. No actual physical W_T/U5/trim estimates, full
2S derivatives, Fourier tail, arithmetic discrepancy or PP are claimed.
-/

namespace ImbalancedChen.P3HBLocalTwoAxisL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothTensorL1
open ImbalancedChen.P3HBSmoothTensorQuantitativeL1
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBCoupledTwoAxisL1
open ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
open ImbalancedChen.P3HBActualTwoAxisLocalization

/-- The true four HB derivative-mass envelopes multiplied by scalar
LOCAL geometry jet ceilings; the geometry itself is NOT extended. -/
def localJetEnvelope (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (i j : Fin 6) (M0 M1 M2 : ℝ) (u : Fin 6 → ℝ) : ℝ :=
  (M2 * tensorMass chi orders u +
   M1 * tensorMass chi (raiseOrder orders j) u) +
  (M1 * tensorMass chi (raiseOrder orders i) u +
   M0 * tensorMass chi (raiseOrder (raiseOrder orders i) j) u)

private theorem tensorMass_nonneg
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ) (u : Fin 6 → ℝ) :
    0 ≤ tensorMass chi orders u := by
  unfold tensorMass
  exact Finset.sum_nonneg (fun child _ => norm_nonneg _)

/-- The proposed majorant is nonnegative even outside the HB rectangle. -/
theorem localJetEnvelope_nonneg
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ) (i j : Fin 6)
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (u : Fin 6 → ℝ) :
    0 ≤ localJetEnvelope chi orders i j M0 M1 M2 u := by
  unfold localJetEnvelope
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hM2 (tensorMass_nonneg chi orders u))
      (mul_nonneg hM1 (tensorMass_nonneg chi (raiseOrder orders j) u)))
    (add_nonneg
      (mul_nonneg hM1 (tensorMass_nonneg chi (raiseOrder orders i) u))
      (mul_nonneg hM0 (tensorMass_nonneg chi
        (raiseOrder (raiseOrder orders i) j) u)))

/-- Genuine actual same-W two-axis mass is globally dominated by an
integrable HB-only majorant, using the W jet inequalities ONLY INSIDE
the exact original closed log-support box. In the complement the mass
vanishes, without assuming W or its derivatives globally bounded. -/
theorem actualTwoAxisMass_le_localJetEnvelope
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2)
    (h0 : ∀ u ∈ originalHBLogBox, ‖W u‖ ≤ M0)
    (hi : ∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u ∈ originalHBLogBox,
      ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2)
    (u : Fin 6 → ℝ) :
    actualTwoAxisMass chi orders W i j u ≤
      localJetEnvelope chi orders i j M0 M1 M2 u := by
  by_cases hu : u ∈ originalHBLogBox
  · calc
      actualTwoAxisMass chi orders W i j u ≤
          jetMass chi orders W i j u :=
        actualTwoAxisMass_le_jetMass chi hchi orders W i j hW hDi u
      _ ≤ localJetEnvelope chi orders i j M0 M1 M2 u := by
        unfold jetMass localJetEnvelope
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right (h2 u hu)
              (tensorMass_nonneg chi orders u))
            (mul_le_mul_of_nonneg_right (hi u hu)
              (tensorMass_nonneg chi (raiseOrder orders j) u)))
          (add_le_add
            (mul_le_mul_of_nonneg_right (hj u hu)
              (tensorMass_nonneg chi (raiseOrder orders i) u))
            (mul_le_mul_of_nonneg_right (h0 u hu)
              (tensorMass_nonneg chi
                (raiseOrder (raiseOrder orders i) j) u)))
  · rw [actualTwoAxisMass_zero_outside_box
      chi hchi hsmall hlarge orders W i j u hW hDi hu]
    exact localJetEnvelope_nonneg chi orders i j M0 M1 M2
      hM0 hM1 hM2 u

/-- The local-jet majorant itself is integrable on the original six-
coordinate Lebesgue chart. Its only analytic inputs are compact HB
cutoffs, not global boundedness/integrability of W's derivative jets. -/
theorem localJetEnvelope_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (i j : Fin 6) (M0 M1 M2 : ℝ) :
    Integrable (localJetEnvelope chi orders i j M0 M1 M2) := by
  have hmass (o : Fin 6 → ℕ) : Integrable (tensorMass chi o) :=
    all_logTensorMixed_children_norm_integrable chi hchi hsmall hlarge o
  have ha : Integrable (fun u => M2 * tensorMass chi orders u) :=
    (hmass orders).const_mul M2
  have hb : Integrable (fun u => M1 * tensorMass chi (raiseOrder orders j) u) :=
    (hmass (raiseOrder orders j)).const_mul M1
  have hc : Integrable (fun u => M1 * tensorMass chi (raiseOrder orders i) u) :=
    (hmass (raiseOrder orders i)).const_mul M1
  have hd : Integrable (fun u => M0 * tensorMass chi
      (raiseOrder (raiseOrder orders i) j) u) :=
    (hmass (raiseOrder (raiseOrder orders i) j)).const_mul M0
  change Integrable (fun u =>
    (M2 * tensorMass chi orders u +
     M1 * tensorMass chi (raiseOrder orders j) u) +
    (M1 * tensorMass chi (raiseOrder orders i) u +
     M0 * tensorMass chi (raiseOrder (raiseOrder orders i) j) u))
  exact (ha.add hb).add (hc.add hd)

private theorem raised_order_le (orders : Fin 6 → ℕ) (i k : Fin 6) :
    (raiseOrder orders i) k ≤ orders k + 1 := by
  by_cases h : k = i
  · subst k
    simp [raiseOrder]
  · simp [raiseOrder, Function.update_noteq h]

private theorem twice_raised_order_le (orders : Fin 6 → ℕ)
    (i j k : Fin 6) :
    (raiseOrder (raiseOrder orders i) j) k ≤ orders k + 2 := by
  have a := raised_order_le (raiseOrder orders i) j k
  have b := raised_order_le orders i k
  omega

/-- A TRUE LOCAL geometry-jet bound suffices for the original complete
729-label two-axis mixed L1. The preceding global jet bounds h0,hi,hj,h2
are explicitly weakened to the original HB support rectangle.
The constant is the prior fixed cutoff/6-coordinate budget, and nothing
is claimed about W_T/U5/trim providing these local envelopes uniformly
in N or growing m(N), nor about higher repeated 2S derivatives. -/
theorem actualTwoAxisMass_integrable_and_L1_of_local_jets
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (hk : ∀ k, orders k + 2 ≤ K)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (hWc : Continuous W)
    (hic : Continuous (actualAxisDeriv W i))
    (hjc : Continuous (actualAxisDeriv W j))
    (h2c : Continuous (actualAxisDeriv (actualAxisDeriv W i) j))
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2)
    (h0 : ∀ u ∈ originalHBLogBox, ‖W u‖ ≤ M0)
    (hi : ∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u ∈ originalHBLogBox,
      ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    Integrable (actualTwoAxisMass chi orders W i j) ∧
    (∫ u : Fin 6 → ℝ, actualTwoAxisMass chi orders W i j u) ≤
      (M2 + 2*M1 + M0) *
      ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  let E : ℝ := (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6
  have hmass (o : Fin 6 → ℕ) : Integrable (tensorMass chi o) :=
    all_logTensorMixed_children_norm_integrable chi hchi hsmall hlarge o
  have ha : Integrable (fun u => M2 * tensorMass chi orders u) :=
    (hmass orders).const_mul M2
  have hb : Integrable (fun u => M1 * tensorMass chi (raiseOrder orders j) u) :=
    (hmass (raiseOrder orders j)).const_mul M1
  have hc : Integrable (fun u => M1 * tensorMass chi (raiseOrder orders i) u) :=
    (hmass (raiseOrder orders i)).const_mul M1
  have hd : Integrable (fun u => M0 * tensorMass chi
      (raiseOrder (raiseOrder orders i) j) u) :=
    (hmass (raiseOrder (raiseOrder orders i) j)).const_mul M0
  have hEnvelope : Integrable (localJetEnvelope chi orders i j M0 M1 M2) :=
    localJetEnvelope_integrable chi hchi hsmall hlarge orders i j M0 M1 M2
  have hMassMeas : AEStronglyMeasurable (actualTwoAxisMass chi orders W i j) :=
    (actualTwoAxisMass_continuous chi hchi orders W i j
      hW hDi hWc hic hjc h2c).measurable.aestronglyMeasurable
  have hMassNonneg (u : Fin 6 → ℝ) :
      0 ≤ actualTwoAxisMass chi orders W i j u := by
    unfold actualTwoAxisMass
    exact Finset.sum_nonneg (fun child _ => norm_nonneg _)
  have hPoint (u : Fin 6 → ℝ) :
      actualTwoAxisMass chi orders W i j u ≤
        localJetEnvelope chi orders i j M0 M1 M2 u :=
    actualTwoAxisMass_le_localJetEnvelope chi hchi hsmall hlarge
      orders W i j hW hDi M0 M1 M2 hM0 hM1 hM2 h0 hi hj h2 u
  have hActual : Integrable (actualTwoAxisMass chi orders W i j) :=
    Integrable.mono_nonneg hEnvelope hMassMeas
      (Filter.Eventually.of_forall hMassNonneg)
      (Filter.Eventually.of_forall hPoint)
  have hk0 (k : Fin 6) : orders k ≤ K := by omega
  have hki (k : Fin 6) : (raiseOrder orders i) k ≤ K :=
    (raised_order_le orders i k).trans (by omega)
  have hkj (k : Fin 6) : (raiseOrder orders j) k ≤ K :=
    (raised_order_le orders j k).trans (by omega)
  have hkij (k : Fin 6) :
      (raiseOrder (raiseOrder orders i) j) k ≤ K :=
    (twice_raised_order_le orders i j k).trans (hk k)
  have ba : (∫ u : Fin 6 → ℝ, tensorMass chi orders u) ≤ E :=
    all_logTensorMixed_children_L1_le chi hchi hsmall hlarge
      K C hC orders hk0
  have bb : (∫ u : Fin 6 → ℝ, tensorMass chi (raiseOrder orders j) u) ≤ E :=
    all_logTensorMixed_children_L1_le chi hchi hsmall hlarge
      K C hC (raiseOrder orders j) hkj
  have bc : (∫ u : Fin 6 → ℝ, tensorMass chi (raiseOrder orders i) u) ≤ E :=
    all_logTensorMixed_children_L1_le chi hchi hsmall hlarge
      K C hC (raiseOrder orders i) hki
  have bd : (∫ u : Fin 6 → ℝ,
      tensorMass chi (raiseOrder (raiseOrder orders i) j) u) ≤ E :=
    all_logTensorMixed_children_L1_le chi hchi hsmall hlarge
      K C hC (raiseOrder (raiseOrder orders i) j) hkij
  have hEnvelopeIntegral :
      (∫ u : Fin 6 → ℝ, localJetEnvelope chi orders i j M0 M1 M2 u) =
      (M2 * (∫ u : Fin 6 → ℝ, tensorMass chi orders u) +
       M1 * (∫ u : Fin 6 → ℝ, tensorMass chi (raiseOrder orders j) u)) +
      (M1 * (∫ u : Fin 6 → ℝ, tensorMass chi (raiseOrder orders i) u) +
       M0 * (∫ u : Fin 6 → ℝ,
         tensorMass chi (raiseOrder (raiseOrder orders i) j) u)) := by
    change (∫ u : Fin 6 → ℝ,
      (M2 * tensorMass chi orders u +
       M1 * tensorMass chi (raiseOrder orders j) u) +
      (M1 * tensorMass chi (raiseOrder orders i) u +
       M0 * tensorMass chi (raiseOrder (raiseOrder orders i) j) u)) = _
    rw [integral_add (ha.add hb) (hc.add hd),
      integral_add ha hb, integral_add hc hd]
    simp only [integral_const_mul]
  refine ⟨hActual, ?_⟩
  calc
    (∫ u : Fin 6 → ℝ, actualTwoAxisMass chi orders W i j u) ≤
        ∫ u : Fin 6 → ℝ, localJetEnvelope chi orders i j M0 M1 M2 u :=
      integral_mono hActual hEnvelope hPoint
    _ = _ := hEnvelopeIntegral
    _ ≤ (M2*E + M1*E) + (M1*E + M0*E) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left ba hM2)
          (mul_le_mul_of_nonneg_left bb hM1))
        (add_le_add (mul_le_mul_of_nonneg_left bc hM1)
          (mul_le_mul_of_nonneg_left bd hM0))
    _ = (M2 + 2*M1 + M0) *
        ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
      dsimp [E]
      ring

end
end ImbalancedChen.P3HBLocalTwoAxisL1
