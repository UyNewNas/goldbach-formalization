import ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
import Mathlib.Tactic

/-!
P3.6 internal manuscript increment, frozen paper
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F), physical six-log-coordinate HB chart.
SOURCE_ONLY: NOT ELABORATED / NOT KERNEL VERIFIED.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Localizes the GENUINE second coordinate derivatives of the same coupled
W times every original three-way six-slot HB child. Regardless of W's
values away from the HB chart, the entire differentiated 729-label mass
vanishes whenever one physical coordinate is strictly outside the
closed logarithmic support rectangle. Both i=j and i≠j are included.

This is only a support statement. It does NOT supply the actual W_T/U5/trim
uniform higher jets, common m(N) threshold, Fourier H tail, rho, or PP.
-/

namespace ImbalancedChen.P3HBActualTwoAxisLocalization
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBCoupledTwoAxisL1

/-- The literal original six-log-coordinate closed support rectangle. -/
def originalHBLogBox : Set (Fin 6 → ℝ) :=
  {u | ∀ k : Fin 6, u k ∈ Set.Icc (-Real.log 2) (Real.log 2)}

/-- Outside any one ORIGINAL coordinate interval, a genuine two-axis
coupled derivative vanishes. This uses the actual four-term product rule,
not a false inference that W has compact support. -/
theorem actualTwoAxisChild_zero_exterior
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (W : (Fin 6 → ℝ) → ℂ) (i j k : Fin 6) (u : Fin 6 → ℝ)
    (hW : ∀ (v : Fin 6 → ℝ) (r : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v r t)) (v r))
    (hDi : ∀ v : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update v j t)) (v j))
    (hout : u k ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    actualAxisDeriv
      (actualAxisDeriv
        (fun v => W v * logTensorMixed chi orders child v) i) j u = 0 := by
  have h0 := logTensorMixed_zero_exterior_coordinate
    chi orders child u hsmall hlarge k hout
  have h1 := logTensorMixed_zero_exterior_coordinate
    chi (raiseOrder orders j) child u hsmall hlarge k hout
  have h2 := logTensorMixed_zero_exterior_coordinate
    chi (raiseOrder orders i) child u hsmall hlarge k hout
  have h3 := logTensorMixed_zero_exterior_coordinate
    chi (raiseOrder (raiseOrder orders i) j) child u
    hsmall hlarge k hout
  rw [actualTwoAxisDeriv_weightedChild
    chi hchi orders child u i j W hW (hDi u)]
  simp [h0, h1, h2, h3]

/-- The complete positional 729-child norm mass is zero outside any
single genuine HB log coordinate support interval. -/
theorem actualTwoAxisMass_zero_exterior
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℂ) (i j k : Fin 6) (u : Fin 6 → ℝ)
    (hW : ∀ (v : Fin 6 → ℝ) (r : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v r t)) (v r))
    (hDi : ∀ v : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update v j t)) (v j))
    (hout : u k ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    actualTwoAxisMass chi orders W i j u = 0 := by
  unfold actualTwoAxisMass
  apply Finset.sum_eq_zero
  intro child _
  rw [actualTwoAxisChild_zero_exterior
    chi hchi hsmall hlarge orders child W i j k u hW hDi hout]
  exact norm_zero

/-- True mass has no support outside the actual original six-slot
rectangle. For fixed physical scales this lets subsequent integral
bounds use local jet envelopes, rather than a spurious global W bound. -/
theorem actualTwoAxisMass_zero_outside_box
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6) (u : Fin 6 → ℝ)
    (hW : ∀ (v : Fin 6 → ℝ) (r : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v r t)) (v r))
    (hDi : ∀ v : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update v j t)) (v j))
    (hout : u ∉ originalHBLogBox) :
    actualTwoAxisMass chi orders W i j u = 0 := by
  have hnot : ¬ ∀ k : Fin 6,
      u k ∈ Set.Icc (-Real.log 2) (Real.log 2) := by
    exact hout
  push_neg at hnot
  obtain ⟨k, hk⟩ := hnot
  have hcoord : u k ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2) := by
    by_cases hleft : u k < -Real.log 2
    · exact Or.inl hleft
    · have hlo : -Real.log 2 ≤ u k := le_of_not_gt hleft
      have hright : Real.log 2 < u k := by
        by_contra hright
        exact hk ⟨hlo, le_of_not_gt hright⟩
      exact Or.inr hright
  exact actualTwoAxisMass_zero_exterior
    chi hchi hsmall hlarge orders W i j k u hW hDi hcoord

/-- Exact localization identity for the REAL six-dimensional norm mass.
This is no Fourier error assumption: the RHS is literally the original
coupled mass with its already-proved compact support exposed. -/
theorem actualTwoAxisMass_eq_box_indicator
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (r : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v r t)) (v r))
    (hDi : ∀ v : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update v j t)) (v j)) :
    actualTwoAxisMass chi orders W i j =
      originalHBLogBox.indicator (actualTwoAxisMass chi orders W i j) := by
  funext u
  by_cases hu : u ∈ originalHBLogBox
  · simp [Set.indicator_of_mem hu]
  · rw [actualTwoAxisMass_zero_outside_box
      chi hchi hsmall hlarge orders W i j u hW hDi hu]
    simp [Set.indicator_of_not_mem hu]

end
end ImbalancedChen.P3HBActualTwoAxisLocalization
