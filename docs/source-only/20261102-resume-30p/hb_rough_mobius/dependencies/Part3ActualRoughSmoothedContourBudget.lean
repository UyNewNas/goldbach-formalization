import ImbalancedChen.Part3ActualRoughAsymmetricContour
import ImbalancedChen.Part3ActualRoughContourEdges

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- The two genuine conductor widths are retained independently. Their
-- witnesses need not agree. Every integrand and tail below is the actual
-- original-character rough Smooth1 Perron expression.

namespace ImbalancedChen.Part3.ActualRoughSmoothedContourBudget20261027
noncomputable section
open Classical Complex Set MeasureTheory
open ActualRoughContourHolomorphic20261026b
open ActualRoughAsymmetricContour20261026b
open ActualRoughContourEdges20261026b
open ActualRoughContourIntegrandBounds20261026b
open RoughSlotSmoothedPerron20261026b RoughSlotPerronTruncation20261026b

-- No contour identity, unknown L norm, or desired character saving is a
-- hypothesis. Only the geometric gates for the two actual zero-free
-- widths are explicit; their uniform real-parameter supplier is phase28.
theorem exists_actual_rough_smoothed_contour_budget (η : ℝ) (hη : 0 < η) :
    ∃ c₁ A₁ c₂ A₂ E : ℝ,
      0 < c₁ ∧ 0 < A₁ ∧ 0 < c₂ ∧ 0 < A₂ ∧ 0 < E ∧
      ∀ (ν : ℝ → ℝ), ContDiff ℝ 1 ν → (∀ x > 0, 0 ≤ ν x) →
      Function.support ν ⊆ Icc (1/2) 2 →
      (∫ x in Ioi (0 : ℝ), ν x/x) = 1 →
      ∃ Ctail Cedge : ℝ, 0 < Ctail ∧ 0 < Cedge ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (useMu : Bool) (z τ U T X ε δ κ ξ : ℝ),
      0 ≤ z → 0 < U → 0 < T → 1 ≤ X → 0 < ε → ε < 1 →
      0 < δ → 0 ≤ κ →
      δ ≤ conductorWidth c₁ A₁ η χ (T+|τ|) →
      δ ≤ conductorWidth c₂ A₂ η χ (T+|τ|) →
      δ ≤ 1 / RoughQuadraticLowRectangle20261026b.rectangleLog q (T+|τ|) →
      δ * Real.log (max 2 z) ≤ κ →
      0 < ξ → ξ ≤ δ → ξ * Real.log X ≤ 1 →
      let P := contourAmplitude E Cedge q (T+|τ|) δ κ z ε
      ‖∑ n ∈ smoothCarrier ν ε X,
        coefficient useMu χ z τ U n * Smooth1 ν ε (n/X)‖ ≤
        P * X^(1-δ/2) +
        P * Real.exp 1 * X * (δ/2+ξ) / (Real.pi*T^2) +
        Real.exp 1 * (1+1/ξ) * X * (Ctail/ε) / (Real.pi*T) := by
  obtain ⟨c₁,A₁,hc₁,hA₁,hcontour⟩ := exists_actual_asymmetric_rough_contour η hη
  obtain ⟨c₂,A₂,E,hc₂,hA₂,hE,hedges⟩ := exists_actual_rough_contour_edge_bounds η hη
  refine ⟨c₁,A₁,c₂,A₂,E,hc₁,hA₁,hc₂,hA₂,hE,?_⟩
  intro ν hν hnonneg hsupp hmass
  obtain ⟨Ctail,hCtail,hidentity⟩ := hcontour ν hν hnonneg hsupp hmass
  obtain ⟨Cedge,hCedge,hedge⟩ := hedges ν hν hsupp
  refine ⟨Ctail,Cedge,hCtail,hCedge,?_⟩
  intro q _ χ hχ useMu z τ U T X ε δ κ ξ hz hU hT hX hε hε1 hδ hκ hw₁ hw₂ hdisk hcap hξ hξδ hξlog
  dsimp only
  let f := roughPerronIntegrand useMu χ z τ U ν ε X
  let a := 1-δ/2
  let b := 1+ξ
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hid := hidentity q χ hχ useMu z τ U T X ε δ ξ
    hz hU hT hXpos hε hε1 hδ hw₁ hξ hξδ hξlog
  have heb := hedge q χ hχ useMu z τ U T X ε δ κ ξ
    hz hT hX hε hε1 hδ hκ hw₂ hdisk hcap hξ hξδ hξlog
  rw [hid.1]
  calc
    ‖VIntegral' f a (-T) T + HIntegral' f a b T -
        HIntegral' f a b (-T) + rightTail useMu χ z τ U ν ε X b T‖ ≤
        ‖VIntegral' f a (-T) T‖ +
        (‖HIntegral' f a b T‖ + ‖HIntegral' f a b (-T)‖) +
        ‖rightTail useMu χ z τ U ν ε X b T‖ := by
      calc
        _ ≤ ‖VIntegral' f a (-T) T + HIntegral' f a b T - HIntegral' f a b (-T)‖ +
            ‖rightTail useMu χ z τ U ν ε X b T‖ := norm_add_le _ _
        _ ≤ (‖VIntegral' f a (-T) T + HIntegral' f a b T‖ +
            ‖HIntegral' f a b (-T)‖) + ‖rightTail useMu χ z τ U ν ε X b T‖ :=
          add_le_add_right (norm_sub_le _ _) _
        _ ≤ (‖VIntegral' f a (-T) T‖ + ‖HIntegral' f a b T‖ +
            ‖HIntegral' f a b (-T)‖) + ‖rightTail useMu χ z τ U ν ε X b T‖ :=
          add_le_add_right (add_le_add_right (norm_add_le _ _) _) _
        _ = _ := by ring
    _ ≤ _ := add_le_add (add_le_add heb.1 heb.2) hid.2

end
end ImbalancedChen.Part3.ActualRoughSmoothedContourBudget20261027
