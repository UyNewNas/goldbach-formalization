import ImbalancedChen.P4AOriginalThirdFallbackArchive
import ImbalancedChen.Part4ActualThirdOriginalFirstChordQuery

/-! Whole-box lower tangent for the original third-prefix certificate.
All ratio, slope and denominator bounds are reconstructed from the
literal row and its four corners on the closed chart box. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackSlope
noncomputable section
open Set
open scoped BigOperators
open P4AOriginalThirdFallbackArchive
open P5OldFifthPointwiseQ (firstF)
open P5OldFifthFirstFConcavity
open Certificates.P2HistoricLogPointInterpreter (oddSum sharp_odd_log_upper)

def X (u : ℝ) : ℝ := (mu : ℝ) + (h : ℝ)*u
def S (b : Bool) (u v : ℝ) : ℝ := (mu : ℝ) + (branch b : ℝ)*(h : ℝ)*u*v
def O (u : ℝ) : ℝ := (peak : ℝ) - 3/2*(h : ℝ)*u
def A (u v : ℝ) : ℝ := (peak : ℝ) - 3/2*(h : ℝ)*u*v
def Z (b : Bool) (u v w : ℝ) : ℝ := S b u v*w/2
def Y (b : Bool) (u v w : ℝ) : ℝ := S b u v - Z b u v w
def argument (b : Bool) (L u v w : ℝ) : ℝ := (L-X u-S b u v)/Z b u v w
def jac (b : Bool) (u v : ℝ) : ℝ := |(branch b : ℝ)|*(h : ℝ)^2*u*S b u v/2
def physicalIntegrand (x y z Lo Ln : ℝ) : ℝ :=
  4*(actualExtendedThirdLowerFactor ((Ln-x-y-z)/z) -
    actualExtendedThirdLowerFactor ((Lo-x-y-z)/z))/(x*y*z^2)

theorem log_le_logUp {q : ℚ} (hq : 1 ≤ q) : Real.log (q : ℝ) ≤ (logUp q : ℝ) := by
  let r : ℝ := ((q : ℝ)-1)/((q : ℝ)+1)
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd : 0 < (q : ℝ)+1 := by linarith
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hq') hd.le
  have hr1 : r < 1 := (div_lt_one hd).mpr (by linarith)
  have he : (1+r)/(1-r) = (q : ℝ) := by
    apply (div_eq_iff (by linarith : 1-r ≠ 0)).mpr
    dsimp [r]
    field_simp [hd.ne'] <;> ring
  have hh := sharp_odd_log_upper hr0 hr1 16
  rw [he] at hh
  simpa [logUp,oddSum,r] using hh

theorem firstSlope_antitone : AntitoneOn firstSlope (Icc (2 : ℝ) 4) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 2 4) (f' := firstCurvature)
  · intro x hx
    exact (hasDerivAt_firstSlope (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hI : x ∈ Icc (2 : ℝ) 4 := interior_subset hx
    exact (hasDerivAt_firstSlope (by linarith [hI.1])).hasDerivWithinAt
  · intro x hx
    have hI : x ∈ Icc (2 : ℝ) 4 := interior_subset hx
    exact firstCurvature_nonpos hI.1 hI.2

theorem certified_derivative {c : Cell} {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ ((record c).t : ℝ)) :
    (slope c : ℝ)*(b-a) ≤ actualExtendedThirdLowerFactor b - actualExtendedThirdLowerFactor a := by
  obtain ⟨_,_,_,_,_,ht2,ht4,_⟩ := original_rows c
  have ht2' : (2 : ℝ) ≤ ((record c).t : ℝ) := by exact_mod_cast ht2
  have ht4' : ((record c).t : ℝ) ≤ 4 := by exact_mod_cast ht4
  have hs : (slope c : ℝ) ≤ firstSlope ((record c).t : ℝ) := by
    have hh := log_le_logUp (q := (record c).t-1) (by linarith)
    push_cast at hh
    unfold slope firstSlope
    push_cast
    exact div_le_div_of_nonneg_right (sub_le_sub_left hh _) (sq_nonneg _)
  have hcont : ContinuousOn firstF (Icc a b) := fun x hx =>
    (hasDerivAt_firstF (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ interior (Icc a b)) : HasDerivAt firstF (firstSlope x) x := by
    have hI : x ∈ Icc a b := interior_subset hx
    exact hasDerivAt_firstF (by linarith [hI.1])
  have hlow (x : ℝ) (hx : x ∈ interior (Icc a b)) : (slope c : ℝ) ≤ deriv firstF x := by
    rw [(hd x hx).deriv]
    have hI : x ∈ Icc a b := interior_subset hx
    have hxT := hI.2.trans hb
    exact hs.trans (firstSlope_antitone ⟨ha.trans hI.1,hxT.trans ht4'⟩ ⟨ht2',ht4'⟩ hxT)
  rw [OriginalU2FirstChordCellSourceOnly.actual_lower_eq_log (ha.trans hab) (hb.trans ht4'),
    OriginalU2FirstChordCellSourceOnly.actual_lower_eq_log ha (hab.trans (hb.trans ht4'))]
  exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) hlow
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab

private theorem affine_bound (A B l r t : ℝ) (hl : l ≤ t) (hr : t ≤ r)
    (hf : 0 ≤ A+B*l) (hg : 0 ≤ A+B*r) : 0 ≤ A+B*t := by
  by_cases hB : 0 ≤ B
  · linarith only [hf,mul_le_mul_of_nonneg_left hl hB]
  · linarith only [hg,mul_le_mul_of_nonpos_left hr (le_of_not_ge hB)]

private theorem corner_bound (c : Cell) {u v : ℝ} (hu : u ∈ Icc (ua c : ℝ) (ub c : ℝ))
    (hv : v ∈ Icc (va c : ℝ) (vb c : ℝ)) (P : ℝ → ℝ → ℝ)
    (hform : ∀ u v, P u v = P 0 0 + ((P 1 0 - P 0 0) + (P 1 1 - P 1 0)*v)*u)
    (hcorner : ∀ i j : Bool, 0 ≤ P (edge (ua c) (ub c) i : ℝ) (edge (va c) (vb c) j : ℝ)) :
    0 ≤ P u v := by
  let B := P 1 0 - P 0 0
  let D := P 1 1 - P 1 0
  have hside (i : Bool) : 0 ≤ P (edge (ua c) (ub c) i : ℝ) v := by
    let t : ℝ := (edge (ua c) (ub c) i : ℝ)
    have he (x : ℝ) : P t x = (P 0 0+B*t)+(D*t)*x := by rw [hform t x]; dsimp [B,D]; ring
    change 0 ≤ P t v
    rw [he]
    apply affine_bound _ _ _ _ v hv.1 hv.2
    · rw [← he]; exact hcorner i false
    · rw [← he]; exact hcorner i true
  rw [hform u v]
  apply affine_bound _ _ _ _ u hu.1 hu.2
  · rw [← hform]; exact hside false
  · rw [← hform]; exact hside true

theorem unit_bounds (c : Cell) {u v w : ℝ}
    (hu : u ∈ Icc (ua c : ℝ) (ub c : ℝ)) (hv : v ∈ Icc (va c : ℝ) (vb c : ℝ))
    (hw : w ∈ Icc (wa c : ℝ) (wb c : ℝ)) :
    u ∈ Icc (0 : ℝ) 1 ∧ v ∈ Icc (0 : ℝ) 1 ∧ w ∈ Icc (5/9 : ℝ) 1 := by
  have hi : (c.2.1.val : ℝ) ≤ 7 := by exact_mod_cast (show c.2.1.val ≤ 7 by omega)
  have hj : (c.2.2.1.val : ℝ) ≤ 7 := by exact_mod_cast (show c.2.2.1.val ≤ 7 by omega)
  have hl : (c.2.2.2.val : ℝ) ≤ 31 := by exact_mod_cast (show c.2.2.2.val ≤ 31 by omega)
  have hx := hu.1
  have hx' := hu.2
  have hy := hv.1
  have hy' := hv.2
  have hz := hw.1
  have hz' := hw.2
  simp only [ua,ub,va,vb,wa,wb] at hx hx' hy hy' hz hz'
  push_cast at hx hx' hy hy' hz hz'
  exact ⟨⟨by linarith [Nat.cast_nonneg (α := ℝ) c.2.1.val],by linarith⟩,⟨by linarith [Nat.cast_nonneg (α := ℝ) c.2.2.1.val],by linarith⟩,
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) c.2.2.2.val],by linarith⟩⟩

theorem positive_s {b : Bool} {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : 0 < S b u v := by
  have hprod : u*v ≤ 1 := (mul_le_mul_of_nonneg_left hv.2 hu.1).trans (by simpa using hu.2)
  have hnon := mul_nonneg hu.1 hv.1
  cases b <;> norm_num [S,mu,h,branch] <;> nlinarith

theorem old_le_new {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) : O u ≤ A u v := by
  have hg := mul_nonneg hu (sub_nonneg.mpr hv)
  norm_num [O,A,h,peak]
  nlinarith

theorem box_geometry (c : Cell) {u v w : ℝ}
    (hu : u ∈ Icc (ua c : ℝ) (ub c : ℝ)) (hv : v ∈ Icc (va c : ℝ) (vb c : ℝ))
    (hw : w ∈ Icc (wa c : ℝ) (wb c : ℝ)) :
    S c.1 u v ≤ (sMax c : ℝ) ∧
    2 ≤ argument c.1 (O u) u v w ∧
    argument c.1 (O u) u v w ≤ argument c.1 (A u v) u v w ∧
    argument c.1 (A u v) u v w ≤ ((record c).t : ℝ) := by
  obtain ⟨_,_,_,_,_,ht,_,_,_,_,_,_,hc⟩ := original_rows c
  obtain ⟨hu',hv',hw'⟩ := unit_bounds c hu hv hw
  have hS := positive_s (b := c.1) hu' hv'
  have hw0 : 0 < w := by linarith [hw'.1]
  have hz : 0 < Z c.1 u v w := by unfold Z; positivity
  have Tmax : (0 : ℝ) ≤ ((record c).t : ℝ) := by exact_mod_cast (by linarith : 0 ≤ (record c).t)
  have hsmax : 0 ≤ (sMax c : ℝ)-S c.1 u v := by
    refine corner_bound c hu hv (fun a b => (sMax c : ℝ)-S c.1 a b)
      (fun a b => by dsimp [S]; ring) ?_
    intro i j
    have hh := (hc i j).2.1
    apply sub_nonneg.mpr
    simpa [S,sQ] using (show ((sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j)) : ℝ)
      ≤ (sMax c : ℝ) by exact_mod_cast hh)
  have ho : 0 ≤ 2*(O u-X u-S c.1 u v)-2*S c.1 u v*(wb c : ℝ) := by
    refine corner_bound c hu hv (fun a b => 2*(O a-X a-S c.1 a b)-2*S c.1 a b*(wb c : ℝ))
      (fun a b => by dsimp [O,X,S]; ring) ?_
    intro i j
    apply sub_nonneg.mpr
    simpa [O,X,S,oldQ,xQ,sQ] using
      (show ((2*sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j)*wb c : ℚ) : ℝ) ≤
          ((2*(oldQ (edge (ua c) (ub c) i)-xQ (edge (ua c) (ub c) i)-
            sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j)) : ℚ) : ℝ)
        by exact_mod_cast (hc i j).2.2.1)
  have hn : 0 ≤ ((record c).t : ℝ)*S c.1 u v*(wa c : ℝ)-2*(A u v-X u-S c.1 u v) := by
    refine corner_bound c hu hv
      (fun a b => ((record c).t : ℝ)*S c.1 a b*(wa c : ℝ)-2*(A a b-X a-S c.1 a b))
      (fun a b => by dsimp [A,X,S]; ring) ?_
    intro i j
    apply sub_nonneg.mpr
    simpa [A,X,S,newQ,xQ,sQ] using
      (show ((2*(newQ (edge (ua c) (ub c) i) (edge (va c) (vb c) j)-xQ (edge (ua c) (ub c) i)-
          sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j)) : ℚ) : ℝ) ≤
          (((record c).t*sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j)*wa c : ℚ) : ℝ)
        by exact_mod_cast (hc i j).2.2.2)
  refine ⟨sub_nonneg.mp hsmax,(le_div_iff₀ hz).mpr ?_,
    div_le_div_of_nonneg_right (by linarith [old_le_new hu'.1 hv'.2]) hz.le,(div_le_iff₀ hz).mpr ?_⟩
  · unfold Z
    nlinarith only [ho,mul_le_mul_of_nonneg_left hw.2 hS.le]
  · unfold Z
    nlinarith only [hn,mul_le_mul_of_nonneg_left hw.1 (mul_nonneg Tmax hS.le)]

end
end ImbalancedChen.P4AOriginalThirdFallbackSlope

