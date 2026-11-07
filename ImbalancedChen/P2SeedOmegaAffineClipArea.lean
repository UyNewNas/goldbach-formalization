import ImbalancedChen.P2SeedOmegaFiniteMeshLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact symbolic clipped-affine slice areas for the two ORIGINAL bad-domain
pieces, with no cell evaluation. The positive-part primitive is proved by
splitting at its actual kink; no differentiability at a max seam is assumed.
These supply rational cell weights, not a numerical passing certificate.
-/

namespace ImbalancedChen.P2SeedOmegaAffineClipArea
noncomputable section
open Set MeasureTheory
open scoped Interval

def positive (x : ℝ) : ℝ := max 0 x

theorem integral_positive {a b : ℝ} (hab : a≤b) :
    (∫ x in a..b,positive x)=(positive b^2-positive a^2)/2 := by
  have hc : Continuous positive := continuous_const.max continuous_id
  by_cases hb : b≤0
  · have hi : (∫ x in a..b,positive x)=0 := by
      calc
        _ = ∫ x in a..b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hab] at hx
          exact max_eq_left (hx.2.trans hb)
        _ = 0 := by simp
    rw [hi]
    simp only [positive,max_eq_left hb,max_eq_left (hab.trans hb),zero_pow,sub_self,zero_div]
  · by_cases ha : 0≤a
    · have hi : (∫ x in a..b,positive x)=∫ x in a..b,x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact max_eq_right (ha.trans hx.1)
      rw [hi,integral_id]
      simp only [positive,max_eq_right ha,max_eq_right (ha.trans hab)]
    · have ha0 : a≤0 := (lt_of_not_ge ha).le
      have hb0 : 0≤b := (lt_of_not_ge hb).le
      have hleft : (∫ x in a..0,positive x)=0 := by
        calc
          _ = ∫ x in a..0,(0:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le ha0] at hx
            exact max_eq_left hx.2
          _ = 0 := by simp
      have hright : (∫ x in (0:ℝ)..b,positive x)=b^2/2 := by
        calc
          _ = ∫ x in (0:ℝ)..b,x := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hb0] at hx
            exact max_eq_right hx.1
          _ = b^2/2 := by rw [integral_id]; ring
      have hs := intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable a 0) (hc.intervalIntegrable 0 b)
      rw [←hs,hleft,hright]
      simp only [positive,max_eq_left ha0,max_eq_right hb0,zero_pow,sub_zero,zero_add]

/-- Integral of the rising boundary contribution in v>=1-2u. -/
theorem integral_rising_positive {a b t : ℝ} (hab : a≤b) :
    (∫ u in a..b,positive (t+2*u))=
      (positive (t+2*b)^2-positive (t+2*a)^2)/4 := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (f:=positive) (a:=a) (b:=b) (2:ℝ) t
  have hi := integral_positive (a:=2*a+t) (b:=2*b+t) (by linarith only [hab])
  rw [hi] at h
  change 2*(∫ u in a..b,positive (2*u+t))=_ at h
  have he : (fun u : ℝ =>positive (t+2*u))=(fun u : ℝ =>positive (2*u+t)) := by
    funext u
    rw [add_comm]
  rw [he]
  rw [show 2*a+t=t+2*a by ring,show 2*b+t=t+2*b by ring] at h
  linarith only [h]

/-- Integral of the falling boundary contribution in v>=u. -/
theorem integral_falling_positive {a b t : ℝ} (hab : a≤b) :
    (∫ u in a..b,positive (t-u))=
      (positive (t-a)^2-positive (t-b)^2)/2 := by
  rw [intervalIntegral.integral_comp_sub_left]
  exact integral_positive (by linarith only [hab])

/-- Exact length of a clipped v interval, including empty and zero-width
fibres. This identity avoids any floating decision about which wall wins. -/
theorem clipped_length_identity {c d z : ℝ} (hcd : c≤d) :
    max 0 (d-max c z)=positive (d-z)-positive (c-z) := by
  by_cases hzc : z≤c
  · have hd : 0≤d-z := by linarith only [hcd,hzc]
    have hc : 0≤c-z := by linarith only [hzc]
    rw [max_eq_left hzc,positive,positive,max_eq_right hd,max_eq_right hc,
      max_eq_right (sub_nonneg.mpr hcd)]
    ring
  · have hcz : c≤z := (lt_of_not_ge hzc).le
    rw [max_eq_right hcz,positive,positive,max_eq_left (by linarith only [hcz] : c-z≤0),sub_zero]

def risingArea (a b c d : ℝ) : ℝ :=
  (positive (d-1+2*b)^2-positive (d-1+2*a)^2-
    positive (c-1+2*b)^2+positive (c-1+2*a)^2)/4
def fallingArea (a b c d : ℝ) : ℝ :=
  (positive (d-a)^2-positive (d-b)^2-positive (c-a)^2+positive (c-b)^2)/2

/-- Exact symbolic area of a first-piece cell slice. -/
theorem integral_first_piece_clipped {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) :
    (∫ u in a..b,max 0 (d-max c (1-2*u)))=risingArea a b c d := by
  have he : (fun u : ℝ =>max 0 (d-max c (1-2*u)))=
      (fun u =>positive (d-1+2*u)-positive (c-1+2*u)) := by
    funext u
    rw [clipped_length_identity hcd]
    congr 1 <;> congr 1 <;> ring
  have hc : Continuous (fun u : ℝ =>positive (c-1+2*u)) :=
    continuous_const.max ((continuous_const.sub continuous_const).add
      (continuous_const.mul continuous_id))
  have hd : Continuous (fun u : ℝ =>positive (d-1+2*u)) :=
    continuous_const.max ((continuous_const.sub continuous_const).add
      (continuous_const.mul continuous_id))
  rw [he,intervalIntegral.integral_sub (hd.intervalIntegrable a b) (hc.intervalIntegrable a b)]
  rw [integral_rising_positive hab,integral_rising_positive hab]
  unfold risingArea
  ring

/-- Exact symbolic area of a second-piece cell slice. -/
theorem integral_second_piece_clipped {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) :
    (∫ u in a..b,max 0 (d-max c u))=fallingArea a b c d := by
  have he : (fun u : ℝ =>max 0 (d-max c u))=
      (fun u =>positive (d-u)-positive (c-u)) := by
    funext u
    exact clipped_length_identity hcd
  have hc : Continuous (fun u : ℝ =>positive (c-u)) := continuous_const.max (continuous_const.sub continuous_id)
  have hd : Continuous (fun u : ℝ =>positive (d-u)) := continuous_const.max (continuous_const.sub continuous_id)
  rw [he,intervalIntegral.integral_sub (hd.intervalIntegrable a b) (hc.intervalIntegrable a b),
    integral_falling_positive hab,integral_falling_positive hab]
  unfold fallingArea
  ring

end
end ImbalancedChen.P2SeedOmegaAffineClipArea
