import ImbalancedChen.P2SeedOmegaGeneratedSumRate

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual simultaneous spatial/node/alpha-box refinement with EXACT rational
weights and a threshold BEFORE every box/query in a fixed horizon. The
box span is explicitly bounded by the refining rate; fixed nonzero spans
are NOT claimed to have vanishing error. No pass/desired bound is assumed.
-/

namespace ImbalancedChen.P2SeedOmegaSimultaneousRefinement
noncomputable section
open Set Filter
open scoped Topology
open P2SeedOmegaGeneratedRangeRate
open P2SeedOmegaGeneratedSumRate
open P2SeedOmegaFiniteRationalBounds
open P2SeedOmegaSampledKappaEnclosure
open P2SeedOmegaBadGlobalCost (actualBadCost)
open P5Z.AutomaticBuchstabWidthRate

def refinementRate (d n : ℕ) : ℚ :=
  (128*(2*(227/50)+2*depthConstant (d+1)+2)+16384*(10/29-19/58))/(n+1:ℚ)

theorem simultaneous_budget_bound (d n : ℕ) {A B : ℚ}
    (hspan : B-A≤1/(n+1:ℚ)) : totalBudget d (n+1) n A B≤refinementRate d n := by
  have hnode : omegaBudget d (n+1) A B≤
      2*(227/50)*(1/(n+1:ℚ))+(2*depthConstant (d+1)+2)/(n+1:ℚ) := by
    simp only [omegaBudget,Nat.cast_add,Nat.cast_one]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hspan (by norm_num)) _
  have h := add_le_add_right (mul_le_mul_of_nonneg_left hnode (by norm_num : (0:ℚ)≤128))
    (2*geometricError n)
  have he : 128*(2*(227/50)*(1/(n+1:ℚ))+(2*depthConstant (d+1)+2)/(n+1:ℚ))+
      2*geometricError n=refinementRate d n := by
    unfold geometricError refinementRate
    field_simp [show (n+1:ℚ)≠0 by positivity]
    <;> ring
  rw [he] at h
  exact h

theorem actual_simultaneous_endpoint_errors (d n : ℕ) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2)
    (hspan : B-A≤1/(n+1:ℚ)) {alpha : ℝ}
    (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    |(actualCostLower (n+1) (generatedNodes d (n+1)) A B n:ℝ)-actualBadCost alpha|≤(refinementRate d n:ℝ) ∧
      |(actualCostUpper (n+1) (generatedNodes d (n+1)) A B n:ℝ)-actualBadCost alpha|≤(refinementRate d n:ℝ) := by
  have hb := generated_actual_cost_bounds d (n+1) (Nat.succ_pos _) hA hAB hR n ha
  have hg := (generated_actual_interval_gap d (n+1) (Nat.succ_pos _) hA hAB hR n).2.trans
    (simultaneous_budget_bound d n hspan)
  have hgR : (actualCostUpper (n+1) (generatedNodes d (n+1)) A B n:ℝ)-
      (actualCostLower (n+1) (generatedNodes d (n+1)) A B n:ℝ)≤(refinementRate d n:ℝ) := by
    exact_mod_cast hg
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]
    linarith only [hb.2,hgR]
  · rw [abs_of_nonneg (sub_nonneg.mpr hb.2)]
    linarith only [hb.1,hgR]

theorem refinementRate_tendsto_zero (d : ℕ) :
    Tendsto (fun n =>(refinementRate d n:ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul
    ((128*(2*(227/50)+2*depthConstant (d+1)+2)+16384*(10/29-19/58):ℚ):ℝ)
  simpa only [refinementRate,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_div,mul_zero] using h

/-- The threshold is chosen BEFORE the inherited rational boxes and
their actual alpha queries. It pays all three independent refinements. -/
theorem uniform_simultaneous_actual_consistency (d : ℕ) {epsilon : ℝ} (he : 0<epsilon) :
    ∃ N : ℕ,∀ n : ℕ,N≤n→∀ A B : ℚ,2≤A→A≤B→boxTop B≤(d:ℚ)+2→
      B-A≤1/(n+1:ℚ)→∀ alpha : ℝ,alpha ∈ Icc (A:ℝ) (B:ℝ)→
      |(actualCostLower (n+1) (generatedNodes d (n+1)) A B n:ℝ)-actualBadCost alpha|<epsilon ∧
        |(actualCostUpper (n+1) (generatedNodes d (n+1)) A B n:ℝ)-actualBadCost alpha|<epsilon := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((refinementRate_tendsto_zero d).eventually (gt_mem_nhds he))
  refine ⟨N,?_⟩
  intro n hn A B hA hAB hR hspan alpha ha
  have h := actual_simultaneous_endpoint_errors d n hA hAB hR hspan ha
  exact ⟨h.1.trans_lt (hN n hn),h.2.trans_lt (hN n hn)⟩

end
end ImbalancedChen.P2SeedOmegaSimultaneousRefinement
