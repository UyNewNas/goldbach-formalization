import ImbalancedChen.P3HBCoupledTwoAxisL1
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-!
P3.6, paper 9731290e8f53cffda44129906cde6a965eaa869b, §4 (F).
SOURCE_ONLY, NOT COMPILED, NOT KERNEL VERIFIED.
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
The previously independent final-mass AEStronglyMeasurable hypothesis is
discharged from continuity of the SAME geometry W, its genuine coordinate
jets, and the original C-infinity HB children. Actual physical W_T/U5/trim
jet continuity and T,m(N)-uniform bounds remain manuscript-internal.
-/

namespace ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBCoupledTwoAxisL1

/-- Actual original six-position HB derivative tensor is continuous. -/
theorem logTensorMixed_continuous
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3) :
    Continuous (logTensorMixed chi orders child) := by
  have hc : ∀ k ∈ (Finset.univ : Finset (Fin 6)),
      Continuous (fun u : Fin 6 → ℝ =>
        iteratedDeriv (orders k) (logChild chi (child k)) (u k)) := by
    intro k _
    exact ((logChild_contDiff chi hchi (child k)).continuous_iteratedDeriv
      (orders k) le_top).comp (continuous_apply k)
  simpa only [logTensorMixed, Finset.prod_univ] using
    (continuous_finsetProd (Finset.univ : Finset (Fin 6)) hc)

/-- Four branches with true ordered derivatives of one common W. -/
def twoAxisJetTerm
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6) (u : Fin 6 → ℝ) : ℂ :=
  ((actualAxisDeriv (actualAxisDeriv W i) j u *
      logTensorMixed chi orders child u +
    actualAxisDeriv W i u *
      logTensorMixed chi (raiseOrder orders j) child u) +
   (actualAxisDeriv W j u *
      logTensorMixed chi (raiseOrder orders i) child u +
    W u *
      logTensorMixed chi (raiseOrder (raiseOrder orders i) j) child u))

/-- The mixed mass equals the original 729-label four-branch mass. -/
theorem actualTwoAxisMass_eq_jetTerm_sum
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (u : Fin 6 → ℝ) :
    actualTwoAxisMass chi orders W i j u =
      ∑ child ∈ smoothChildren,
        ‖twoAxisJetTerm chi orders child W i j u‖ := by
  unfold actualTwoAxisMass
  apply Finset.sum_congr rfl
  intro child _
  rw [actualTwoAxisDeriv_weightedChild
    chi hchi orders child u i j W hW (hDi u)]
  rfl

/-- Continuity of W and its actual selected jets yields continuity of
the differentiated 729-child mass; no mass-measurability premise. -/
theorem actualTwoAxisMass_continuous
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (W : (Fin 6 → ℝ) → ℂ)
    (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (hWc : Continuous W)
    (hic : Continuous (actualAxisDeriv W i))
    (hjc : Continuous (actualAxisDeriv W j))
    (h2c : Continuous (actualAxisDeriv (actualAxisDeriv W i) j)) :
    Continuous (actualTwoAxisMass chi orders W i j) := by
  have hterm (child : Fin 6 → Fin 3) :
      Continuous (twoAxisJetTerm chi orders child W i j) := by
    unfold twoAxisJetTerm
    exact
      ((h2c.mul (logTensorMixed_continuous chi hchi orders child)).add
        (hic.mul (logTensorMixed_continuous chi hchi
          (raiseOrder orders j) child))).add
      ((hjc.mul (logTensorMixed_continuous chi hchi
          (raiseOrder orders i) child)).add
        (hWc.mul (logTensorMixed_continuous chi hchi
          (raiseOrder (raiseOrder orders i) j) child)))
  have hsum : Continuous
      (fun u : Fin 6 → ℝ =>
        ∑ child ∈ smoothChildren,
          ‖twoAxisJetTerm chi orders child W i j u‖) := by
    apply continuous_finsetSum smoothChildren
    intro child _
    exact (hterm child).norm
  have heq : actualTwoAxisMass chi orders W i j =
      (fun u : Fin 6 → ℝ =>
        ∑ child ∈ smoothChildren,
          ‖twoAxisJetTerm chi orders child W i j u‖) := by
    funext u
    exact actualTwoAxisMass_eq_jetTerm_sum
      chi hchi orders W i j hW hDi u
  rw [heq]
  exact hsum

/-- Genuine integrated two-axis L1, deriving all measurability from
actual continuous W jets. Physical uniform jet bounds remain to prove. -/
theorem actualTwoAxisMass_integrable_and_L1_of_continuous_jets
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
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (h0 : ∀ u, ‖W u‖ ≤ M0)
    (hi : ∀ u, ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ∀ u, ‖actualAxisDeriv W j u‖ ≤ M1)
    (h2 : ∀ u, ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    Integrable (actualTwoAxisMass chi orders W i j) ∧
    (∫ u : Fin 6 → ℝ, actualTwoAxisMass chi orders W i j u) ≤
      (M2 + 2*M1 + M0) *
      ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  have hmass : AEStronglyMeasurable
      (actualTwoAxisMass chi orders W i j) :=
    (actualTwoAxisMass_continuous chi hchi orders W i j
      hW hDi hWc hic hjc h2c).measurable.aestronglyMeasurable
  exact actualTwoAxisMass_integrable_and_L1_le
    chi hchi hsmall hlarge K C hC orders hk W i j hW hDi hmass
    M0 M1 M2 hM0 hM1 hM2
    hWc.norm.measurable hic.norm.measurable
    hjc.norm.measurable h2c.norm.measurable h0 hi hj h2

end
end ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
