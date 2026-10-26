import ImbalancedChen.P2SeedOmegaFiniteRationalBounds
import ImbalancedChen.P5ZU1011AutomaticBuchstabWidthRate

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Constructive tightness of THIS chain's floor-generated omega range
coefficients. The deterministic node producer and its arbitrary-depth
width theorem already exist and are reused without cloning or repair.
This file pays exact floor coverage and rational endpoint denominator
effects on arbitrary fixed horizons, beyond the old[1,8] specialization.
No node/error/convergence/checker-pass premise is supplied by a caller.
-/

namespace ImbalancedChen.P2SeedOmegaGeneratedRangeRate
noncomputable section
open Set LiLiuPrereqBuchstab
open Certificates.P2BuchstabRationalSemantics
open P5Z.AutomaticBuchstabNodes P5Z.AutomaticBuchstabWidthStep P5Z.AutomaticBuchstabWidthRate
open P2SeedOmegaRationalRangeEnclosure

def generatedNodes (d m : ℕ) : List NodeEnclosure := nodes m ((d+2)*m)

theorem generated_query_coverage (d m : ℕ) (hm : 0<m) {r : ℚ}
    (hr : 1≤r) (hR : r≤(d:ℚ)+2) : queryIndex m r+1≤(d+2)*m := by
  have hmQ : (0:ℚ)<m := by exact_mod_cast hm
  have hf : (queryIndex m r:ℚ)≤(r-1)*(m:ℚ) :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hr) hmQ.le)
  have hq : (queryIndex m r:ℚ)≤(((d+1)*m:ℕ):ℚ) := by
    push_cast
    nlinarith only [hf,hR,hmQ.le]
  have hn : queryIndex m r≤(d+1)*m := by exact_mod_cast hq
  nlinarith only [hn,hm]

theorem generated_nodes_check (d m : ℕ) (hm : 0<m) : check m (generatedNodes d m)=true :=
  generated_check m ((d+2)*m) hm

theorem generated_actual_range (d m : ℕ) (hm : 0<m) {lo hi : ℚ}
    (hlo : 1≤lo) (horder : lo≤hi) (hR : hi≤(d:ℚ)+2) {r : ℝ}
    (hr : r ∈ Icc (lo:ℝ) (hi:ℝ)) :
    (lowerOmega m (generatedNodes d m) lo hi:ℝ)≤buchstab r ∧
      buchstab r≤(upperOmega m (generatedNodes d m) lo hi:ℝ) := by
  apply actual_buchstab_range_enclosure (generated_nodes_check d m hm) hlo horder _ hr
  change queryIndex m hi+1<(nodes m ((d+2)*m)).length
  rw [nodes_length]
  exact Nat.lt_succ_of_le (generated_query_coverage d m hm (hlo.trans horder) hR)

/-- Actual rational endpoint-directed interval width. The span term is
paid separately from the vanishing deterministic recurrence width. -/
theorem generated_range_width (d m : ℕ) (hm : 0<m) {lo hi : ℚ}
    (hlo : 1≤lo) (horder : lo≤hi) (hR : hi≤(d:ℚ)+2) :
    0≤upperOmega m (generatedNodes d m) lo hi-lowerOmega m (generatedNodes d m) lo hi ∧
    upperOmega m (generatedNodes d m) lo hi-lowerOmega m (generatedNodes d m) lo hi≤
      2*(hi-lo)+(2*depthConstant (d+1)+2)/(m:ℚ) := by
  let a : ℝ := grid m (queryIndex m lo)
  let b : ℝ := grid m (queryIndex m hi+1)
  have hhi := hlo.trans horder
  have hkB := generated_query_coverage d m hm hhi hR
  have hkA : queryIndex m lo≤(d+2)*m :=
    (queryIndex_mono horder).trans ((Nat.le_succ _).trans hkB)
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hloR : (1:ℝ)≤(lo:ℝ) := by exact_mod_cast hlo
  have horderR : (lo:ℝ)≤(hi:ℝ) := by exact_mod_cast horder
  have hhiR := hloR.trans horderR
  have hLo := query_grid_bounds hm hlo
  have hHi := query_grid_bounds hm hhi
  have ha1 : 1≤a := by exact_mod_cast P2SeedOmegaRationalRangeEnclosure.grid_ge_one hm (queryIndex m lo)
  have haLo : a≤(lo:ℝ) := by exact_mod_cast hLo.1
  have hhiB : (hi:ℝ)≤b := by exact_mod_cast hHi.2.le
  have hab : a≤b := haLo.trans (horderR.trans hhiB)
  have hstepA : (grid m (queryIndex m lo+1):ℝ)-a=1/(m:ℝ) := by
    exact_mod_cast P5Z.AutomaticBuchstabWidthStep.grid_step m (queryIndex m lo)
  have hstepB : b-(grid m (queryIndex m hi):ℝ)=1/(m:ℝ) := by
    exact_mod_cast P5Z.AutomaticBuchstabWidthStep.grid_step m (queryIndex m hi)
  have hgap : b-a≤(hi:ℝ)-(lo:ℝ)+2/(m:ℝ) := by
    have hnext : (lo:ℝ)<(grid m (queryIndex m lo+1):ℝ) := by exact_mod_cast hLo.2
    have hleft : (grid m (queryIndex m hi):ℝ)≤(hi:ℝ) := by exact_mod_cast hHi.1
    linarith only [hstepA,hstepB,hnext,hleft]
  have hNA := actual_node_bounds m (queryIndex m lo) hm
  have hNB := actual_node_bounds m (queryIndex m hi+1) hm
  have hWA : (width m (queryIndex m lo):ℝ)≤(depthConstant (d+1):ℝ)/(m:ℝ) := by
    exact_mod_cast actual_width_depth (d+1) m hm (queryIndex m lo) (by simpa [Nat.add_assoc] using hkA)
  have hWB : (width m (queryIndex m hi+1):ℝ)≤(depthConstant (d+1):ℝ)/(m:ℝ) := by
    exact_mod_cast actual_width_depth (d+1) m hm (queryIndex m hi+1) (by simpa [Nat.add_assoc] using hkB)
  have hinc := weighted_increment_all ha1 hab
  have hcross0 : (0:ℝ)≤((node m (queryIndex m hi+1)).upper:ℝ)-
      ((node m (queryIndex m lo)).lower:ℝ) := by
    linarith only [hNA.1,hNB.2,hinc.1]
  have hcross : ((node m (queryIndex m hi+1)).upper:ℝ)-
      ((node m (queryIndex m lo)).lower:ℝ)≤
      2*(depthConstant (d+1):ℝ)/(m:ℝ)+(b-a) := by
    simp only [width,Rat.cast_sub] at hWA hWB
    linarith only [hNA.2,hNB.1,hWA,hWB,hinc.2]
  have hLower : ((node m (queryIndex m lo)).lower:ℝ)≤(lo:ℝ) := by
    have hω := mul_le_mul_of_nonneg_left (buchstab_le_one ha1) (zero_le_one.trans ha1)
    dsimp only [weighted] at hNA
    linarith only [hNA.1,hω,haLo]
  have hinv : 0≤1/(lo:ℝ)-1/(hi:ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (zero_lt_one.trans_le hloR) horderR)
  have hsecond : ((node m (queryIndex m lo)).lower:ℝ)*(1/(lo:ℝ)-1/(hi:ℝ))≤(hi:ℝ)-(lo:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hLower hinv
    have he : (lo:ℝ)*(1/(lo:ℝ)-1/(hi:ℝ))=((hi:ℝ)-(lo:ℝ))/(hi:ℝ) := by
      field_simp [(zero_lt_one.trans_le hloR).ne',(zero_lt_one.trans_le hhiR).ne']
      <;> ring
    rw [he] at h
    exact h.trans (div_le_self (sub_nonneg.mpr horderR) hhiR)
  have hfirst := (div_le_self hcross0 hloR).trans hcross
  have hraw : ((node m (queryIndex m hi+1)).upper:ℝ)/(lo:ℝ)-
      ((node m (queryIndex m lo)).lower:ℝ)/(hi:ℝ)≤
      2*((hi:ℝ)-(lo:ℝ))+(2*(depthConstant (d+1):ℝ)+2)/(m:ℝ) := by
    have he : ((node m (queryIndex m hi+1)).upper:ℝ)/(lo:ℝ)-
        ((node m (queryIndex m lo)).lower:ℝ)/(hi:ℝ)=
        (((node m (queryIndex m hi+1)).upper:ℝ)-((node m (queryIndex m lo)).lower:ℝ))/(lo:ℝ)+
        ((node m (queryIndex m lo)).lower:ℝ)*(1/(lo:ℝ)-1/(hi:ℝ)) := by ring
    rw [he]
    linarith only [hfirst,hsecond,hgap]
  have hU0 : (0:ℚ)≤(node m (queryIndex m hi+1)).upper := by
    have hb1 := ha1.trans hab
    have hW : 0≤weighted b := (mul_pos (zero_lt_one.trans_le hb1) (buchstab_positive b)).le
    have h : (0:ℝ)≤((node m (queryIndex m hi+1)).upper:ℝ) := hW.trans hNB.2
    exact_mod_cast h
  have hUpper : (upperOmega m (generatedNodes d m) lo hi:ℝ)=
      ((node m (queryIndex m hi+1)).upper:ℝ)/(lo:ℝ) := by
    simp only [upperOmega,generatedNodes,entry_nodes m ((d+2)*m) _ hkB,max_eq_right hU0,Rat.cast_div]
  have hLowerClamp : ((node m (queryIndex m lo)).lower:ℝ)/(hi:ℝ)≤
      (lowerOmega m (generatedNodes d m) lo hi:ℝ) := by
    simp only [lowerOmega,generatedNodes,entry_nodes m ((d+2)*m) _ hkA,
      Rat.cast_div,Rat.cast_max,Rat.cast_zero]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hhiR)
  have hBounds := generated_actual_range d m hm hlo horder hR
    (r:=(lo:ℝ)) ⟨le_rfl,horderR⟩
  have h0 : (0:ℝ)≤(upperOmega m (generatedNodes d m) lo hi:ℝ)-
      (lowerOmega m (generatedNodes d m) lo hi:ℝ) := by linarith only [hBounds.1,hBounds.2]
  have h1 : (upperOmega m (generatedNodes d m) lo hi:ℝ)-
      (lowerOmega m (generatedNodes d m) lo hi:ℝ)≤
      2*((hi:ℝ)-(lo:ℝ))+(2*(depthConstant (d+1):ℝ)+2)/(m:ℝ) := by
    rw [hUpper]
    linarith only [hraw,hLowerClamp]
  exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

end
end ImbalancedChen.P2SeedOmegaGeneratedRangeRate
