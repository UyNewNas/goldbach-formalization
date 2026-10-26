import ImbalancedChen.P2SeedOmegaGeneratedRangeRate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Genuine constructive convergence of the deterministic causal recurrence
coefficients at EVERY fixed rational query on a fixed finite horizon.
No array, actual-function error, convergence, PASS or desired gain is an
input. The rational interval span term in GeneratedRangeRate is explicit;
only its point specialization is asserted to shrink to zero here.
-/

namespace ImbalancedChen.P2SeedOmegaGeneratedPointConsistency
noncomputable section
open Set Filter LiLiuPrereqBuchstab
open scoped Topology
open P2SeedOmegaRationalRangeEnclosure
open P2SeedOmegaGeneratedRangeRate
open P5Z.AutomaticBuchstabWidthRate

def lowerSequence (d : ℕ) (r : ℚ) (m : ℕ) : ℚ :=
  lowerOmega (m+1) (generatedNodes d (m+1)) r r
def upperSequence (d : ℕ) (r : ℚ) (m : ℕ) : ℚ :=
  upperOmega (m+1) (generatedNodes d (m+1)) r r
def rate (d m : ℕ) : ℝ :=
  (2*(depthConstant (d+1):ℝ)+2)/((m:ℝ)+1)

/-- Both directed ACTUAL omega errors, with deterministic rational
data, are paid by a common vanishing recurrence-mesh rate. -/
theorem actual_point_errors (d m : ℕ) {r : ℚ} (hr : 1≤r) (hR : r≤(d:ℚ)+2) :
    |(lowerSequence d r m:ℝ)-buchstab r|≤rate d m ∧
      |(upperSequence d r m:ℝ)-buchstab r|≤rate d m := by
  have hb := generated_actual_range d (m+1) (Nat.succ_pos _) hr le_rfl hR
    (r:=(r:ℝ)) ⟨le_rfl,le_rfl⟩
  have hw := (generated_range_width d (m+1) (Nat.succ_pos _) hr le_rfl hR).2
  have hwR : (upperSequence d r m:ℝ)-(lowerSequence d r m:ℝ)≤rate d m := by
    have h : ((upperOmega (m+1) (generatedNodes d (m+1)) r r-
        lowerOmega (m+1) (generatedNodes d (m+1)) r r:ℚ):ℝ)≤
        ((2*(r-r)+(2*depthConstant (d+1)+2)/(m+1:ℚ):ℚ):ℝ) := by exact_mod_cast hw
    simpa only [lowerSequence,upperSequence,rate,Rat.cast_sub,Rat.cast_add,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one,
      Nat.cast_add,Nat.cast_one,sub_self,mul_zero,zero_add] using h
  have hL : (lowerSequence d r m:ℝ)≤buchstab r := hb.1
  have hU : buchstab r≤(upperSequence d r m:ℝ) := hb.2
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hL)]
    linarith only [hU,hwR]
  · rw [abs_of_nonneg (sub_nonneg.mpr hU)]
    linarith only [hL,hwR]

theorem rate_tendsto_zero (d : ℕ) : Tendsto (rate d) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul
    (2*(depthConstant (d+1):ℝ)+2)
  simpa only [rate,div_eq_mul_inv,one_div,mul_zero] using h

theorem lowerSequence_tendsto_actual (d : ℕ) {r : ℚ}
    (hr : 1≤r) (hR : r≤(d:ℚ)+2) :
    Tendsto (fun m =>(lowerSequence d r m:ℝ)) atTop (𝓝 (buchstab r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ =>norm_nonneg _)) ?_ (rate_tendsto_zero d)
  exact Eventually.of_forall (fun m =>by
    simpa only [Real.norm_eq_abs] using (actual_point_errors d m hr hR).1)

theorem upperSequence_tendsto_actual (d : ℕ) {r : ℚ}
    (hr : 1≤r) (hR : r≤(d:ℚ)+2) :
    Tendsto (fun m =>(upperSequence d r m:ℝ)) atTop (𝓝 (buchstab r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ =>norm_nonneg _)) ?_ (rate_tendsto_zero d)
  exact Eventually.of_forall (fun m =>by
    simpa only [Real.norm_eq_abs] using (actual_point_errors d m hr hR).2)

/-- A single refinement threshold works simultaneously for EVERY
rational query in the fixed horizon. It is obtained from the authentic
causal recurrence rate, not assumed as a convergence supplier. -/
theorem uniform_rational_point_consistency (d : ℕ) {epsilon : ℝ} (he : 0<epsilon) :
    ∃ M : ℕ,∀ m : ℕ,M≤m→∀ r : ℚ,1≤r→r≤(d:ℚ)+2→
      |(lowerSequence d r m:ℝ)-buchstab r|<epsilon ∧
        |(upperSequence d r m:ℝ)-buchstab r|<epsilon := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((rate_tendsto_zero d).eventually (gt_mem_nhds he))
  refine ⟨M,?_⟩
  intro m hm r hr hR
  have h := actual_point_errors d m hr hR
  exact ⟨h.1.trans_lt (hM m hm),h.2.trans_lt (hM m hm)⟩

end
end ImbalancedChen.P2SeedOmegaGeneratedPointConsistency
