import ImbalancedChen.P3HBCanonicalTwoAxisQuantitative
import ImbalancedChen.P3HBWeightedOriginalChildrenL1
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
P3.6; fixed paper 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F).  SOURCE_ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This is the first integrated, genuinely coupled TWO-AXIS HB/geometry budget.
All four actual W derivative branches remain distinct, the exact 3^6
positional HB children are integrated, and repeated i=j is permitted.
This does not establish the physical W_T/U5/trim jet envelopes or full 2S,
nor uniform growth in m(N), Fourier H-box, complete same-rho arithmetic or PP.
The ordinary measurability of actual derivative jets and of the mixed-norm
mass is a physical smoothness obligation, NOT an assumed L1/PP conclusion.
-/

namespace ImbalancedChen.P3HBCoupledTwoAxisL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBWeightedOriginalChildrenL1

/-- Complete original three-way HB mass at a specified ordered derivative array. -/
def tensorMass (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖

/-- Actual canonical two-coordinate derivative of the SAME coupled geometry,
summed over every original child before taking any Fourier transform. -/
def actualTwoAxisMass (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren,
    ‖actualAxisDeriv
      (actualAxisDeriv (fun v =>
        W v * logTensorMixed chi orders child v) i) j u‖

/-- The genuine FOUR-branch derivative majorant, not a free Fourier
discrepancy bound; no mixed derivative of W is silently dropped. -/
def jetMass (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  (‖actualAxisDeriv (actualAxisDeriv W i) j u‖ * tensorMass chi orders u +
   ‖actualAxisDeriv W i u‖ * tensorMass chi (raiseOrder orders j) u) +
  (‖actualAxisDeriv W j u‖ * tensorMass chi (raiseOrder orders i) u +
   ‖W u‖ * tensorMass chi (raiseOrder (raiseOrder orders i) j) u)

/-- Actual two-axis Leibniz, including the diagonal case i=j, dominates
the complete 729-child norm mass by precisely four original HB tensors. -/
theorem actualTwoAxisMass_le_jetMass
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (u : Fin 6 → ℝ) :
    actualTwoAxisMass chi orders W i j u ≤ jetMass chi orders W i j u := by
  let Dji := actualAxisDeriv (actualAxisDeriv W i) j u
  let Di := actualAxisDeriv W i u
  let Dj := actualAxisDeriv W j u
  let z := W u
  have hchild (child : Fin 6 → Fin 3) :
      ‖actualAxisDeriv
        (actualAxisDeriv (fun v =>
          W v * logTensorMixed chi orders child v) i) j u‖ ≤
      ((‖Dji‖ * ‖logTensorMixed chi orders child u‖ +
        ‖Di‖ * ‖logTensorMixed chi (raiseOrder orders j) child u‖) +
       (‖Dj‖ * ‖logTensorMixed chi (raiseOrder orders i) child u‖ +
        ‖z‖ * ‖logTensorMixed chi
          (raiseOrder (raiseOrder orders i) j) child u‖)) := by
    rw [actualTwoAxisDeriv_weightedChild
      chi hchi orders child u i j W hW (hDi u)]
    calc
      _ ≤
        ‖Dji * logTensorMixed chi orders child u +
            Di * logTensorMixed chi (raiseOrder orders j) child u‖ +
        ‖Dj * logTensorMixed chi (raiseOrder orders i) child u +
            z * logTensorMixed chi
              (raiseOrder (raiseOrder orders i) j) child u‖ :=
          norm_add_le _ _
      _ ≤
        (‖Dji * logTensorMixed chi orders child u‖ +
         ‖Di * logTensorMixed chi (raiseOrder orders j) child u‖) +
        (‖Dj * logTensorMixed chi (raiseOrder orders i) child u‖ +
         ‖z * logTensorMixed chi
           (raiseOrder (raiseOrder orders i) j) child u‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ = _ := by simp only [norm_mul]
  calc
    actualTwoAxisMass chi orders W i j u ≤
      ∑ child ∈ smoothChildren,
        ((‖Dji‖ * ‖logTensorMixed chi orders child u‖ +
          ‖Di‖ * ‖logTensorMixed chi (raiseOrder orders j) child u‖) +
         (‖Dj‖ * ‖logTensorMixed chi (raiseOrder orders i) child u‖ +
          ‖z‖ * ‖logTensorMixed chi
            (raiseOrder (raiseOrder orders i) j) child u‖)) := by
      unfold actualTwoAxisMass
      apply Finset.sum_le_sum
      intro child _
      exact hchild child
    _ = jetMass chi orders W i j u := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl

/-- One ordinary measurable, uniformly bounded real norm of an ACTUAL
complex geometry jet costs only the existing separated HB L1 budget.
This requires no Fourier, PP or target-integral premise. -/
private theorem jetTensor_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (J : (Fin 6 → ℝ) → ℂ)
    (hJ : Measurable (fun u => ‖J u‖))
    (M : ℝ) (hBound : ∀ u, ‖J u‖ ≤ M) :
    Integrable (fun u : Fin 6 → ℝ => ‖J u‖ * tensorMass chi orders u) := by
  have h := weighted_children_norm_integrable
    chi hchi hsmall hlarge orders (fun u => ‖J u‖) hJ M (by
      intro u
      simpa only [abs_of_nonneg (norm_nonneg (J u))] using hBound u)
  simpa only [tensorMass, abs_of_nonneg (norm_nonneg _)] using h

private theorem jetTensor_integral_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (horders : ∀ k, orders k ≤ K)
    (J : (Fin 6 → ℝ) → ℂ)
    (hJ : Measurable (fun u => ‖J u‖))
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ u, ‖J u‖ ≤ M) :
    (∫ u : Fin 6 → ℝ, ‖J u‖ * tensorMass chi orders u) ≤
      M * ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  have h := weighted_children_L1_le
    chi hchi hsmall hlarge K C hC orders horders
    (fun u => ‖J u‖) hJ M hM (by
      intro u
      simpa only [abs_of_nonneg (norm_nonneg (J u))] using hBound u)
  simpa only [tensorMass, abs_of_nonneg (norm_nonneg _)] using h

private theorem raised_le (orders : Fin 6 → ℕ) (i k : Fin 6) :
    (raiseOrder orders i) k ≤ orders k + 1 := by
  by_cases h : k = i
  · subst k
    simp [raiseOrder]
  · simp [raiseOrder, Function.update_noteq h]

private theorem twice_raised_le (orders : Fin 6 → ℕ) (i j k : Fin 6) :
    (raiseOrder (raiseOrder orders i) j) k ≤ orders k + 2 := by
  have a := raised_le (raiseOrder orders i) j k
  have b := raised_le orders i k
  omega

/-- The four genuine original geometry jets, each coupled to an actual HB
derivative tensor, are Lebesgue-integrable on the original R^6 log chart.
No integrability of the FINAL differentiated mass is postulated. -/
theorem jetMass_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6) (M0 M1 M2 : ℝ)
    (h0m : Measurable (fun u => ‖W u‖))
    (him : Measurable (fun u => ‖actualAxisDeriv W i u‖))
    (hjm : Measurable (fun u => ‖actualAxisDeriv W j u‖))
    (h2m : Measurable (fun u =>
      ‖actualAxisDeriv (actualAxisDeriv W i) j u‖))
    (h0 : ∀ u, ‖W u‖ ≤ M0)
    (hi : ∀ u, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u, ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    Integrable (jetMass chi orders W i j) := by
  have ha := jetTensor_integrable chi hchi hsmall hlarge orders
    (actualAxisDeriv (actualAxisDeriv W i) j) h2m M2 h2
  have hb := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder orders j) (actualAxisDeriv W i) him M1 hi
  have hc := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder orders i) (actualAxisDeriv W j) hjm M1 hj
  have hd := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder (raiseOrder orders i) j) W h0m M0 h0
  exact (ha.add hb).add (hc.add hd)

/-- Real 6D integral cost for all 729 labelled original children,
including i=j: the SAME differentiated geometry jets pay M2+2M1+M0.
The original global derivative bound C_K is integrated, not just sampled. -/
theorem jetMass_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (hk : ∀ k, orders k + 2 ≤ K)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (h0m : Measurable (fun u => ‖W u‖))
    (him : Measurable (fun u => ‖actualAxisDeriv W i u‖))
    (hjm : Measurable (fun u => ‖actualAxisDeriv W j u‖))
    (h2m : Measurable (fun u =>
      ‖actualAxisDeriv (actualAxisDeriv W i) j u‖))
    (h0 : ∀ u, ‖W u‖ ≤ M0)
    (hi : ∀ u, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u, ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    (∫ u : Fin 6 → ℝ, jetMass chi orders W i j u) ≤
      (M2 + 2*M1 + M0) *
      ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  let E : ℝ := (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6
  have hk0 (k : Fin 6) : orders k ≤ K := by omega
  have hki (k : Fin 6) : (raiseOrder orders i) k ≤ K :=
    (raised_le orders i k).trans (by omega)
  have hkj (k : Fin 6) : (raiseOrder orders j) k ≤ K :=
    (raised_le orders j k).trans (by omega)
  have hkij (k : Fin 6) :
      (raiseOrder (raiseOrder orders i) j) k ≤ K :=
    (twice_raised_le orders i j k).trans (hk k)
  have ha := jetTensor_integrable chi hchi hsmall hlarge orders
    (actualAxisDeriv (actualAxisDeriv W i) j) h2m M2 h2
  have hb := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder orders j) (actualAxisDeriv W i) him M1 hi
  have hc := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder orders i) (actualAxisDeriv W j) hjm M1 hj
  have hd := jetTensor_integrable chi hchi hsmall hlarge
    (raiseOrder (raiseOrder orders i) j) W h0m M0 h0
  have ba := jetTensor_integral_le chi hchi hsmall hlarge
    K C hC orders hk0 _ h2m M2 hM2 h2
  have bb := jetTensor_integral_le chi hchi hsmall hlarge
    K C hC (raiseOrder orders j) hkj _ him M1 hM1 hi
  have bc := jetTensor_integral_le chi hchi hsmall hlarge
    K C hC (raiseOrder orders i) hki _ hjm M1 hM1 hj
  have bd := jetTensor_integral_le chi hchi hsmall hlarge
    K C hC (raiseOrder (raiseOrder orders i) j) hkij _ h0m M0 hM0 h0
  change (∫ u : Fin 6 → ℝ,
    ((‖actualAxisDeriv (actualAxisDeriv W i) j u‖ * tensorMass chi orders u +
      ‖actualAxisDeriv W i u‖ * tensorMass chi (raiseOrder orders j) u) +
     (‖actualAxisDeriv W j u‖ * tensorMass chi (raiseOrder orders i) u +
      ‖W u‖ * tensorMass chi (raiseOrder (raiseOrder orders i) j) u))) ≤ _
  rw [integral_add (ha.add hb) (hc.add hd)]
  rw [integral_add ha hb, integral_add hc hd]
  change _ ≤ (M2 + 2*M1 + M0) * E
  calc
    _ ≤ (M2*E + M1*E) + (M1*E + M0*E) :=
      add_le_add (add_le_add ba bb) (add_le_add bc bd)
    _ = _ := by ring

/-- True mixed-derivative mass has a quantitative real Lebesgue L1 bound
as soon as its ordinary measurability follows from the ACTUAL physical
smoothness class. No L1 estimate, Fourier estimate or PP premise is assumed.
The independently missing part is proving these jet/meas/bound conditions
for every original physical W_T (including U5 and trim) uniformly in T,m. -/
theorem actualTwoAxisMass_integrable_and_L1_le
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
    (hMassMeas : AEStronglyMeasurable
      (actualTwoAxisMass chi orders W i j))
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (h0m : Measurable (fun u => ‖W u‖))
    (him : Measurable (fun u => ‖actualAxisDeriv W i u‖))
    (hjm : Measurable (fun u => ‖actualAxisDeriv W j u‖))
    (h2m : Measurable (fun u =>
      ‖actualAxisDeriv (actualAxisDeriv W i) j u‖))
    (h0 : ∀ u, ‖W u‖ ≤ M0)
    (hi : ∀ u, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u, ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    Integrable (actualTwoAxisMass chi orders W i j) ∧
    (∫ u : Fin 6 → ℝ, actualTwoAxisMass chi orders W i j u) ≤
      (M2 + 2*M1 + M0) *
      ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  have hjet := jetMass_integrable chi hchi hsmall hlarge orders
    W i j M0 M1 M2 h0m him hjm h2m h0 hi hj h2
  have hpoint (u : Fin 6 → ℝ) :
      actualTwoAxisMass chi orders W i j u ≤
        jetMass chi orders W i j u :=
    actualTwoAxisMass_le_jetMass chi hchi orders W i j hW hDi u
  have hnonneg (u : Fin 6 → ℝ) :
      0 ≤ actualTwoAxisMass chi orders W i j u := by
    unfold actualTwoAxisMass
    exact Finset.sum_nonneg (fun child _ => norm_nonneg _)
  have hactual : Integrable (actualTwoAxisMass chi orders W i j) :=
    Integrable.mono_nonneg hjet hMassMeas
      (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hpoint)
  refine ⟨hactual, ?_⟩
  exact (integral_mono hactual hjet hpoint).trans
    (jetMass_L1_le chi hchi hsmall hlarge K C hC orders hk
      W i j M0 M1 M2 hM0 hM1 hM2 h0m him hjm h2m h0 hi hj h2)

end
end ImbalancedChen.P3HBCoupledTwoAxisL1
