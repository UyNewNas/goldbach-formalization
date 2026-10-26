import ImbalancedChen.P2SeedOmegaSwitchedMassFour
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailTransport
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One spatial refinement works for ALL alpha >= 2 simultaneously in the
actual M12..M15 kernels. The bounded-alpha native oscillation theorem
pays the compact head. The actual factorial Buchstab tail pays the whole
remaining half-line; its limiting spatial weight is a continuous function
on the original reciprocal cube. No hidden upper-alpha parameter, K/4
count premise, supplied tail certificate or sampled approximation occurs.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedSpatialHalfline

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalJointTail
open P2SeedOmegaSwitchedKernelFour

def limitingKernel (x : Point) : ℝ := buchstabTailLimit*geometricWeight (1 : Fin 3) x

private theorem cube_compact : IsCompact (continuousCube 3) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

private theorem density_continuous : ContinuousOn (continuousDensity (n:=3)) (continuousCube 3) := by
  unfold continuousDensity
  apply continuousOn_finset_prod
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn
    (fun x hx => ne_of_gt (by linarith [(hx i (mem_univ i)).1] : 0<x i))

private theorem geometric_continuous :
    ContinuousOn (geometricWeight (1 : Fin 3)) (continuousCube 3) :=
  density_continuous.div (continuous_apply 1).continuousOn
    (fun x hx => ne_of_gt (by linarith [(hx 1 (mem_univ _)).1] : 0<x 1))

private theorem limit_continuous : ContinuousOn limitingKernel (continuousCube 3) :=
  continuousOn_const.mul geometric_continuous

private theorem cube_density_bound {x : Point} (hx : x ∈ continuousCube 3) :
    0≤continuousDensity x ∧ continuousDensity x≤1000 := by
  refine ⟨continuousDensity_nonneg hx,?_⟩
  calc
    _ ≤ ∏ _i : Fin 3,(10 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact div_nonneg zero_le_one (by linarith [(hx i (mem_univ i)).1])
      · intro i _
        apply (div_le_iff₀ (by linarith [(hx i (mem_univ i)).1] : 0<x i)).mpr
        linarith [(hx i (mem_univ i)).1]
    _ = _ := by norm_num

private theorem cube_geometric_bound {x : Point} (hx : x ∈ continuousCube 3) :
    0≤geometricWeight (1 : Fin 3) x ∧ geometricWeight (1 : Fin 3) x≤10000 := by
  have hv := (hx 1 (mem_univ _)).1
  have hD := cube_density_bound hx
  refine ⟨geometricWeight_nonneg 1 hx,?_⟩
  change continuousDensity x/x 1≤10000
  apply (div_le_iff₀ (by linarith only [hv] : 0<x 1)).mpr
  linarith only [hv,hD.2]

private theorem kernel_factor (alpha : ℝ) (x : Point) :
    actualKernel alpha x=buchstab (argument alpha x)*geometricWeight (1 : Fin 3) x := by
  rw [actualKernel,geometricWeight_literal]
  ring

private theorem kernel_weighted {alpha : ℝ} (ha : 2≤alpha)
    {x : Point} (hx : x ∈ continuousCube 3) :
    actualKernel alpha x=HighNonunitLegal.G (1 : Fin 3) alpha x*continuousDensity x := by
  exact (LowerTripleContinuous.weighted_legal_literal
    (LowerTripleContinuous.cube_legal ha hx)).symm

/-- Pointwise factorial tail, uniform on the ENTIRE spatial cube. -/
theorem actual_kernel_spatial_tail (m : ℕ) (hm : 3≤m) {alpha : ℝ}
    (ha : ((m:ℝ)+6)/2≤alpha) {x : Point} (hx : x ∈ continuousCube 3) :
    |actualKernel alpha x-limitingKernel x|≤
      (4/(m.factorial:ℝ))*geometricWeight (1 : Fin 3) x := by
  have harg : (m:ℝ)≤argument alpha x := by
    have h := argument_ge_six (n:=3) (by omega) (1 : Fin 3)
      (show 0≤(m:ℝ) by positivity) (by linarith only [ha]) hx
    simpa only [LowerTripleContinuous.sum_literal,argument] using h
  have hw := buchstab_tail_limit_error m hm (argument alpha x) harg
  have hg := (cube_geometric_bound hx).1
  have heq : actualKernel alpha x-limitingKernel x=
      (buchstab (argument alpha x)-buchstabTailLimit)*geometricWeight (1 : Fin 3) x := by
    rw [kernel_factor,limitingKernel]
    ring
  rw [heq,abs_mul,abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_right hw hg

/-- Equicontinuity of the actual spatial kernels over the full admitted
half-line. Only the finite head uses an auxiliary alpha ceiling, and the
proved factorial tail covers every alpha above it. -/
theorem actual_kernel_all_alpha_spatial {epsilon : ℝ} (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∀ alpha : ℝ,2≤alpha →
      ∀ x ∈ continuousCube 3,∀ y ∈ continuousCube 3,dist x y<delta →
        |actualKernel alpha x-actualKernel alpha y|<epsilon := by
  obtain ⟨m,hm,hsmall⟩ := exists_factorial_tail_threshold
    (show 0<epsilon/40000 by positivity)
  let P : ℝ := ((m:ℝ)+6)/2
  have hP : 2≤P := by
    have hmR : (3:ℝ)≤m := by exact_mod_cast hm
    dsimp [P]
    linarith only [hmR]
  let C : ℝ := 400+1000*P
  have hC : 0<C := by dsimp [C]; linarith only [hP]
  have hDuc := cube_compact.uniformContinuousOn_of_continuous density_continuous
  have hLuc := cube_compact.uniformContinuousOn_of_continuous limit_continuous
  obtain ⟨dD,hdD,hD⟩ := Metric.uniformContinuousOn_iff.mp hDuc
    (epsilon/40) (by positivity)
  obtain ⟨dL,hdL,hL⟩ := Metric.uniformContinuousOn_iff.mp hLuc
    (epsilon/2) (by positivity)
  let dH : ℝ := epsilon/(4000*C)
  have hdH : 0<dH := div_pos he (mul_pos (by norm_num) hC)
  refine ⟨min dD (min dL dH),lt_min hdD (lt_min hdL hdH),?_⟩
  intro alpha ha x hx y hy hxy
  have hxyD : dist x y<dD := hxy.trans_le (min_le_left _ _)
  have hxyL : dist x y<dL :=
    hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxyH : dist x y<dH :=
    hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hhead : alpha≤P
  · have hosc := HighNonunitLegal.G_oscillation (j:=(1 : Fin 3)) hP ⟨ha,hhead⟩ hx hy
      (LowerTripleContinuous.cube_legal ha hx) (LowerTripleContinuous.cube_legal ha hy)
      (fun i => by simpa only [Real.dist_eq] using dist_le_pi_dist x y i)
    have hosc' : |HighNonunitLegal.G (1 : Fin 3) alpha x-
        HighNonunitLegal.G (1 : Fin 3) alpha y|≤C*dist x y := by
      have hcoef : 100*((3:ℝ)+1)+1000*P=C := by dsimp [C]; ring
      simpa only [hcoef] using hosc
    have hsmallD : |continuousDensity x-continuousDensity y|<epsilon/40 := by
      simpa only [Real.dist_eq] using hD x hx y hy hxyD
    have hGy : |HighNonunitLegal.G (1 : Fin 3) alpha y|≤10 := by
      rw [abs_of_nonneg (HighNonunitLegal.G_bounds (1 : Fin 3) alpha hy).1]
      exact (HighNonunitLegal.G_bounds (1 : Fin 3) alpha hy).2
    have hDx := cube_density_bound hx
    have hfirst := mul_le_mul hosc' hDx.2 hDx.1 (by positivity : 0≤C*dist x y)
    have hsecond := mul_le_mul_of_nonneg_right hGy
      (abs_nonneg (continuousDensity x-continuousDensity y))
    have hheadsmall : dist x y*(4000*C)<epsilon :=
      (lt_div_iff₀ (mul_pos (by norm_num) hC)).mp hxyH
    have heq : actualKernel alpha x-actualKernel alpha y=
        (HighNonunitLegal.G (1 : Fin 3) alpha x-HighNonunitLegal.G (1 : Fin 3) alpha y)*
          continuousDensity x+HighNonunitLegal.G (1 : Fin 3) alpha y*
          (continuousDensity x-continuousDensity y) := by
      rw [kernel_weighted ha hx,kernel_weighted ha hy]
      ring
    rw [heq]
    have ht := abs_add
      ((HighNonunitLegal.G (1 : Fin 3) alpha x-HighNonunitLegal.G (1 : Fin 3) alpha y)*
        continuousDensity x)
      (HighNonunitLegal.G (1 : Fin 3) alpha y*(continuousDensity x-continuousDensity y))
    rw [abs_mul,abs_of_nonneg hDx.1,abs_mul] at ht
    nlinarith only [ht,hfirst,hsecond,hsmallD,hheadsmall,he]
  · have haP : P≤alpha := (lt_of_not_ge hhead).le
    have hfrac : 0≤4/(m.factorial:ℝ) := by positivity
    have htx := actual_kernel_spatial_tail m hm haP hx
    have hty := actual_kernel_spatial_tail m hm haP hy
    have hbx := mul_le_mul_of_nonneg_left (cube_geometric_bound hx).2 hfrac
    have hby := mul_le_mul_of_nonneg_left (cube_geometric_bound hy).2 hfrac
    have hlim : |limitingKernel x-limitingKernel y|<epsilon/2 := by
      simpa only [Real.dist_eq] using hL x hx y hy hxyL
    have htri := abs_sub_le (actualKernel alpha x) (limitingKernel x) (actualKernel alpha y)
    have htri' := abs_sub_le (limitingKernel x) (limitingKernel y) (actualKernel alpha y)
    rw [abs_sub_comm (limitingKernel y) (actualKernel alpha y)] at htri'
    nlinarith only [htri,htri',htx,hty,hbx,hby,hlim,hsmall]

/-- One spatial refinement serves all four actual original domains and
all admitted alpha, with no change to arithmetic boundary membership. -/
theorem original_four_common_spatial_refinement {epsilon : ℝ} (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∀ (j : Fin 4) (alpha : ℝ),2≤alpha →
      ∀ x ∈ domain j,∀ y ∈ domain j,dist x y<delta →
        |actualKernel alpha x-actualKernel alpha y|<epsilon := by
  obtain ⟨delta,hd,h⟩ := actual_kernel_all_alpha_spatial he
  exact ⟨delta,hd,fun j alpha ha x hx y hy hxy =>
    h alpha ha x (domain_subset_cube j hx) y (domain_subset_cube j hy) hxy⟩

end
end ImbalancedChen.P2SeedOmegaSwitchedSpatialHalfline
