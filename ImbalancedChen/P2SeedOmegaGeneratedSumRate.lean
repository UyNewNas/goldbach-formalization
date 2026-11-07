import ImbalancedChen.P2SeedOmegaAreaBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Constructive transport of authentic causal-node consistency through the
EXACT nonnegative rational cell areas. The total area and kappa multiplier
budgets are proved in AreaBudget. The alpha-box span is paid explicitly.
No supplied recurrence/check/error/convergence/certificate premise remains.
-/

namespace ImbalancedChen.P2SeedOmegaGeneratedSumRate
noncomputable section
open Set
open scoped BigOperators
open P2SeedOmegaGeneratedRangeRate
open P2SeedOmegaRationalRangeEnclosure
open P2SeedOmegaSampledKappaEnclosure
open P2SeedOmegaRationalCellArea
open P2SeedOmegaFiniteRationalBounds
open P2SeedOmegaAreaBudget
open P5Z.AutomaticBuchstabWidthRate

def omegaBudget (d m : ℕ) (A B : ℚ) : ℚ :=
  2*(227/50)*(B-A)+(2*depthConstant (d+1)+2)/(m:ℚ)
def totalBudget (d m n : ℕ) (A B : ℚ) : ℚ :=
  128*omegaBudget d m A B+2*geometricError n

theorem generated_box_coverage (d m : ℕ) (hm : 0<m) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2) :
    queryIndex m (boxTop B)+1<(generatedNodes d m).length := by
  have ht : (1:ℚ)≤boxTop B := by
    have hB := hA.trans hAB
    dsimp [boxTop]
    linarith only [hB]
  have h := generated_query_coverage d m hm ht hR
  change queryIndex m (boxTop B)+1<(P5Z.AutomaticBuchstabNodes.nodes m ((d+2)*m)).length
  rw [P5Z.AutomaticBuchstabNodes.nodes_length]
  exact Nat.lt_succ_of_le h

theorem budget_nonnegative (d m : ℕ) {A B : ℚ} (hAB : A≤B) : 0≤omegaBudget d m A B := by
  have hC := depthConstant_nonneg (d+1)
  have hn : (0:ℚ)≤2*depthConstant (d+1)+2 := by linarith only [hC]
  unfold omegaBudget
  exact add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hAB))
    (div_nonneg hn (Nat.cast_nonneg m))

theorem generated_kappa_gap (d m : ℕ) (hm : 0<m) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2)
    (n : ℕ) (i j : Fin (n+1)) :
    0≤upperKappa m (generatedNodes d m) A B n i j-lowerKappa m (generatedNodes d m) A B n i j ∧
      upperKappa m (generatedNodes d m) A B n i j-lowerKappa m (generatedNodes d m) A B n i j≤
        128*omegaBudget d m A B := by
  have hq := original_queries n i j hA hAB
  have hq1 : (1:ℚ)≤queryLo A n i j := by linarith only [hq.1]
  have hw := generated_range_width d m hm hq1 hq.2.1 (hq.2.2.trans hR)
  have hspan : queryHi B n i j-queryLo A n i j=(227/50:ℚ)*(B-A) := by
    unfold queryHi queryLo
    ring
  have hbound : upperOmega m (generatedNodes d m) (queryLo A n i j) (queryHi B n i j)-
      lowerOmega m (generatedNodes d m) (queryLo A n i j) (queryHi B n i j)≤omegaBudget d m A B := by
    rw [hspan] at hw
    simpa only [omegaBudget,mul_assoc] using hw.2
  have hc := kappaCoefficient_le_128 n i j
  have hpos := mul_nonneg hc.1 hw.1
  have hupper := mul_le_mul hc.2 hbound hw.1 (by norm_num : (0:ℚ)≤128)
  simpa only [lowerKappa,upperKappa,mul_sub] using And.intro hpos hupper

theorem generated_finite_sum_gap (d m : ℕ) (hm : 0<m) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2) (n : ℕ) :
    0≤upperSum m (generatedNodes d m) A B n-lowerSum m (generatedNodes d m) A B n ∧
      upperSum m (generatedNodes d m) A B n-lowerSum m (generatedNodes d m) A B n≤
        128*omegaBudget d m A B := by
  have hpoint (i j : Fin (n+1)) := generated_kappa_gap d m hm hA hAB hR n i j
  have he : upperSum m (generatedNodes d m) A B n-lowerSum m (generatedNodes d m) A B n=
      ∑ i : Fin (n+1),∑ j : Fin (n+1),
        (upperKappa m (generatedNodes d m) A B n i j-lowerKappa m (generatedNodes d m) A B n i j)*rationalArea n i j := by
    simp only [upperSum,lowerSum,←Finset.sum_sub_distrib,sub_mul]
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun i _ =>Finset.sum_nonneg
      (fun j _ =>mul_nonneg (hpoint i j).1 (rationalArea_nonnegative n i j)))
  · calc
      _ ≤ ∑ i : Fin (n+1),∑ j : Fin (n+1),128*omegaBudget d m A B*rationalArea n i j := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum (fun j _ =>mul_le_mul_of_nonneg_right
          (hpoint i j).2 (rationalArea_nonnegative n i j))
      _ = (128*omegaBudget d m A B)*(∑ i : Fin (n+1),∑ j : Fin (n+1),rationalArea n i j) := by
        simp only [Finset.mul_sum]
      _ ≤ 128*omegaBudget d m A B := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (total_rational_area_budget n).2
          (mul_nonneg (by norm_num) (budget_nonnegative d m hAB))

theorem generated_actual_cost_bounds (d m : ℕ) (hm : 0<m) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2)
    (n : ℕ) {alpha : ℝ} (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    (actualCostLower m (generatedNodes d m) A B n:ℝ)≤P2SeedOmegaBadGlobalCost.actualBadCost alpha ∧
      P2SeedOmegaBadGlobalCost.actualBadCost alpha≤(actualCostUpper m (generatedNodes d m) A B n:ℝ) :=
  actual_bad_cost_rational_bounds (generated_nodes_check d m hm) hA hAB
    (generated_box_coverage d m hm hA hAB hR) n ha

/-- Full actual-cost rational interval width: inherited parameter span,
genuine node recurrence error, AND actual geometric mesh error retained. -/
theorem generated_actual_interval_gap (d m : ℕ) (hm : 0<m) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) (hR : boxTop B≤(d:ℚ)+2) (n : ℕ) :
    0≤actualCostUpper m (generatedNodes d m) A B n-actualCostLower m (generatedNodes d m) A B n ∧
      actualCostUpper m (generatedNodes d m) A B n-actualCostLower m (generatedNodes d m) A B n≤totalBudget d m n A B := by
  have hs := generated_finite_sum_gap d m hm hA hAB hR n
  have he : (0:ℚ)≤geometricError n := by unfold geometricError; positivity
  simp only [actualCostUpper,actualCostLower,totalBudget]
  constructor <;> linarith only [hs.1,hs.2,he]

end
end ImbalancedChen.P2SeedOmegaGeneratedSumRate
