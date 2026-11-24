import ImbalancedChen.P4AOrderedThirdReachableCeiling
import ImbalancedChen.SelectedPrefixBoxCap

namespace ImbalancedChen.P4AOrderedThirdBufferedFallbackBoxes
noncomputable section
open scoped Classical BigOperators Topology
open Set VariableEnvelope P5OriginalAboveMuThirdLowerPhysicalCoefficient

private theorem half_old {x : ℝ} (h : mu<x) (hu : x<rho) : (1/2:ℝ)<v x := by
  rw [v_eq_C h.le]
  dsimp [C,rho] at *
  linarith

private theorem local {k : ℕ} (I : Finset (Fin (k+1))) (t : Fin (k+1) → ℝ)
    (hhalf : 1/2<v (t 0)) (htent : v (t 0)<v (∑ i∈I,t i))
    (hfull : ∀ i,prefixSquareExpr t i<v (t 0))
    (hsel : ∀ i∉I,selectedSquareExpr I t i<v (t 0)) :
    ∃ old : ℚ, v (t 0)<(old:ℝ) ∧ ∃ δ : ℝ, 0<δ ∧
      (∀ s : Fin (k+1) → ℝ, dist s t<δ → v (s 0)<(old:ℝ)) ∧
      ∀ l u : Fin (k+1) → ℚ,dist (fun i => (l i:ℝ)) t<δ → dist (fun i => (u i:ℝ)) t<δ →
        selectedBoxCapCheck I old (299/500) l u=true := by
  obtain ⟨old,ho,hu⟩ := exists_rat_btwn htent
  have hv : v (∑ i∈I,t i)<((299/500:ℚ):ℝ) := (v_le_cap _).trans_lt (by norm_num [cap])
  have H : SelectedPrefixLicense I old (299/500) t := by
    unfold SelectedPrefixLicense
    rw [min_eq_right hv.le]
    exact ⟨hu,hhalf.trans htent,fun i => (hfull i).trans htent,fun i hi => (hsel i hi).trans htent⟩
  obtain ⟨r,hr,hcheck⟩ := exists_selectedBoxCapCheck_radius_of_strict I old (299/500) t H
  have hopen : IsOpen {s : Fin (k+1) → ℝ | v (s 0)<(old:ℝ)} := isOpen_lt (continuous_v.comp (continuous_apply _)) continuous_const
  obtain ⟨r',hr',hball⟩ := Metric.isOpen_iff.mp hopen t ho
  refine ⟨old,ho,min r r',lt_min hr hr',?_,?_⟩
  · intro s hs
    exact hball (hs.trans_le (min_le_right _ _))
  · intro l u hl hu
    exact hcheck l u (hl.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))

theorem second (t : Fin 2 → ℝ) (h : SecondRegion (t 0) (t 1)) :
    ∃ old : ℚ, v (t 0)<(old:ℝ) ∧ ∃ δ : ℝ, 0<δ ∧
      (∀ s : Fin 2 → ℝ,dist s t<δ → v (s 0)<(old:ℝ)) ∧
      ∀ l u : Fin 2 → ℚ,dist (fun i => (l i:ℝ)) t<δ → dist (fun i => (u i:ℝ)) t<δ →
        selectedBoxCapCheck secondMask old (299/500) l u=true := by
  obtain ⟨h1,h2,hs,hnew⟩ := second_initial_physical_gates h
  apply local secondMask t (half_old h.1 h.2.1)
  · simpa [secondMask] using hnew
  · intro i
    fin_cases i <;> simp [prefixSquareExpr,Fin.sum_univ_two,Finset.sum_filter] <;> linarith
  · intro i hi
    fin_cases i <;> simp [secondMask,selectedSquareExpr,Fin.sum_univ_two,Finset.sum_filter] at hi ⊢ <;> linarith

theorem third (t : Fin 3 → ℝ) (h : ThirdRegion (t 0) (t 1) (t 2)) :
    ∃ old : ℚ, v (t 0)<(old:ℝ) ∧ ∃ δ : ℝ, 0<δ ∧
      (∀ s : Fin 3 → ℝ,dist s t<δ → v (s 0)<(old:ℝ)) ∧
      ∀ l u : Fin 3 → ℚ,dist (fun i => (l i:ℝ)) t<δ → dist (fun i => (u i:ℝ)) t<δ →
        selectedBoxCapCheck thirdMask old (299/500) l u=true := by
  obtain ⟨h1,h2,h3,_,hs,hnew⟩ := third_initial_physical_gates h
  apply local thirdMask t (half_old h.1 h.2.1)
  · simpa [thirdMask] using hnew
  · intro i
    fin_cases i <;> simp [prefixSquareExpr,Fin.sum_univ_three,Finset.sum_filter] <;> linarith
  · intro i hi
    fin_cases i <;> simp [thirdMask,selectedSquareExpr,Fin.sum_univ_three,Finset.sum_filter] at hi ⊢ <;> linarith

end
end ImbalancedChen.P4AOrderedThirdBufferedFallbackBoxes
