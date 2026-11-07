import ImbalancedChen.P2SeedOmegaGeneratedPointConsistency

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The total rational-area budget is DERIVED from actual cell intersections,
their enclosing disjoint mesh rectangles and exact interval measures.
No total area/error budget is a premise. This is geometry, not evaluation
of any selected finite certificate or desired numerical saving.
-/

namespace ImbalancedChen.P2SeedOmegaAreaBudget
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2SeedOmegaLiteralFibre
open P2SeedOmegaFiniteMesh
open P2SeedOmegaFiniteCellSum
open P2SeedOmegaRationalCellArea
open P2SeedOmegaFiniteRationalBounds
open P2SeedOmegaSampledKappaEnclosure

theorem actual_cell_area_le_mesh_square (n : ℕ) (i j : Fin (n+1)) :
    (rationalArea n i j:ℝ)≤step n^2 := by
  have hsub : cell n (some i) (some j) ⊆
      Ico (node n i) (hiNode n i) ×ˢ Ico (node n j) (hiNode n j) := inter_subset_right
  have hvol := measure_mono hsub
  have hfinite : volume (Ico (node n i) (hiNode n i) ×ˢ
      Ico (node n j) (hiNode n j))≠⊤ := by
    rw [Measure.prod_prod,Real.volume_Ico,Real.volume_Ico]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono hfinite hvol
  have hi : hiNode n i-node n i=step n := by
    have h := logPrimeMeshPoint_succ corner a2 n i.val
    dsimp [hiNode,node,step]
    linarith only [h]
  have hj : hiNode n j-node n j=step n := by
    have h := logPrimeMeshPoint_succ corner a2 n j.val
    dsimp [hiNode,node,step]
    linarith only [h]
  rw [Measure.prod_prod,Real.volume_Ico,Real.volume_Ico,ENNReal.toReal_mul,hi,hj,
    ENNReal.toReal_ofReal (original_mesh_step_pos n).le] at hr
  rw [←actual_weight_eq_rationalArea]
  simpa only [weight,pow_two] using hr

/-- The same exact area budget holds for every finite mesh cardinality.
Every summand is a true bad-domain intersection volume. -/
theorem total_rational_area_budget (n : ℕ) :
    0≤(∑ i : Fin (n+1),∑ j : Fin (n+1),rationalArea n i j) ∧
      (∑ i : Fin (n+1),∑ j : Fin (n+1),rationalArea n i j)≤1 := by
  have h0 : (0:ℚ)≤∑ i : Fin (n+1),∑ j : Fin (n+1),rationalArea n i j :=
    Finset.sum_nonneg (fun i _ =>Finset.sum_nonneg (fun j _ =>rationalArea_nonnegative n i j))
  have hS : (∑ i : Fin (n+1),∑ j : Fin (n+1),(rationalArea n i j:ℝ))≤
      ∑ i : Fin (n+1),∑ j : Fin (n+1),step n^2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.sum_le_sum (fun j _ =>actual_cell_area_le_mesh_square n i j)
  have hden : (n:ℝ)+1≠0 := by positivity
  have hmesh : ((n+1:ℕ):ℝ)*(((n+1:ℕ):ℝ)*step n^2)=(a2-corner)^2 := by
    simp only [step,logPrimeMeshStep,Nat.cast_add,Nat.cast_one]
    field_simp [hden]
    <;> ring
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hS
  rw [hmesh] at hS
  have hspan : 0≤a2-corner ∧ a2-corner≤1 := by norm_num [a2,corner]
  have h1 : (∑ i : Fin (n+1),∑ j : Fin (n+1),(rationalArea n i j:ℝ))≤1 := by
    nlinarith only [hS,hspan.1,hspan.2]
  exact ⟨h0,by exact_mod_cast h1⟩

/-- Both prime denominators in the true original kappa coefficient
have the same fixed positive geometry margin, independently of mesh. -/
theorem kappaCoefficient_le_128 (n : ℕ) (i j : Fin (n+1)) :
    0≤kappaCoefficient n i j ∧ kappaCoefficient n i j≤128 := by
  have hi := rational_node_bounds n i
  have hj := rational_node_bounds n j
  have hi4 : (1/4:ℚ)≤P2SeedOmegaFiniteMeshLimit.rationalNode n i := by linarith only [hi.1]
  have hj4 : (1/4:ℚ)≤P2SeedOmegaFiniteMeshLimit.rationalNode n j := by linarith only [hj.1]
  have hi0 : (0:ℚ)<P2SeedOmegaFiniteMeshLimit.rationalNode n i := lt_of_lt_of_le (by norm_num) hi4
  have hj0 : (0:ℚ)<P2SeedOmegaFiniteMeshLimit.rationalNode n j := lt_of_lt_of_le (by norm_num) hj4
  have hden : (1/16:ℚ)≤P2SeedOmegaFiniteMeshLimit.rationalNode n i*
      P2SeedOmegaFiniteMeshLimit.rationalNode n j := by
    have h := mul_le_mul hi4 hj4 (by norm_num : (0:ℚ)≤1/4) hi0.le
    norm_num only [show (1/4:ℚ)*(1/4)=1/16 by norm_num] at h
    exact h
  refine ⟨(coefficient_positive n i j).le,?_⟩
  unfold kappaCoefficient
  calc
    _ ≤ 8/(P2SeedOmegaFiniteMeshLimit.rationalNode n i*P2SeedOmegaFiniteMeshLimit.rationalNode n j) :=
      div_le_div_of_nonneg_right (by norm_num) (mul_pos hi0 hj0).le
    _ ≤ 8/(1/16) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ = 128 := by norm_num

end
end ImbalancedChen.P2SeedOmegaAreaBudget
