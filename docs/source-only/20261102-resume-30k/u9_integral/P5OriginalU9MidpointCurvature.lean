import ImbalancedChen.CurrentChenP5U9MeshDiscretization
import ImbalancedChen.P2DirectedLogRounding
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal kind=9 formula of certify_sharp_switch_midpoint.py.  In particular
the logarithm is log((1-t-d)/d), with h=19/125 and d=59/250.  Both of its
first two derivatives have NEGATIVE signs. Signed four-corner arithmetic
encloses the actual second derivative over the complete closed cell.
There is no assumed derivative enclosure or saved numerical endpoint.
-/

namespace ImbalancedChen.P5OriginalU9MidpointCurvature

noncomputable section
open Set
open P2U9DirectedRationalCover P2ContinuousSieveRational
open Certificates.P2DirectedLogRounding

def logPart (x : ℝ) : ℝ := Real.log ((1-x-(d:ℝ))/(d:ℝ))
def logSlope (x : ℝ) : ℝ := -1/(1-x-(d:ℝ))
def logCurvature (x : ℝ) : ℝ := -1/(1-x-(d:ℝ))^2
def reciprocalPart (x : ℝ) : ℝ := 1/x+1/(1-x)
def reciprocalSlope (x : ℝ) : ℝ := -1/x^2+1/(1-x)^2
def reciprocalCurvature (x : ℝ) : ℝ := 2/x^3+2/(1-x)^3
def densitySlope (x : ℝ) : ℝ :=
  logSlope x*reciprocalPart x+logPart x*reciprocalSlope x
def densityCurvature (x : ℝ) : ℝ :=
  logCurvature x*reciprocalPart x+2*logSlope x*reciprocalSlope x+
    logPart x*reciprocalCurvature x

theorem source_positive {x : ℝ} (hx : x ∈ Icc (a:ℝ) (b:ℝ)) :
    0 < x ∧ 0 < 1-x ∧ 0 < 1-x-(d:ℝ) := by
  norm_num [a,b,d] at hx ⊢
  constructor
  · linarith only [hx.1]
  constructor <;> linarith only [hx.2]

theorem hasDerivAt_logPart {x : ℝ} (hg : 1-x-(d:ℝ) ≠ 0) :
    HasDerivAt logPart (logSlope x) x := by
  have hd : (d:ℝ) ≠ 0 := by norm_num [d]
  have hh := ((((hasDerivAt_id x).const_sub 1).sub_const (d:ℝ)).div_const (d:ℝ)).log
    (div_ne_zero hg hd)
  apply hh.congr_deriv
  dsimp [logSlope]
  field_simp [hg,hd]
  <;> ring

theorem hasDerivAt_logSlope {x : ℝ} (hg : 1-x-(d:ℝ) ≠ 0) :
    HasDerivAt logSlope (logCurvature x) x := by
  have hh := ((((hasDerivAt_id x).const_sub 1).sub_const (d:ℝ)).inv hg).neg
  simp only [logSlope,neg_div,one_div]
  apply hh.congr_deriv
  dsimp [logCurvature]
  field_simp [hg]
  <;> ring

theorem hasDerivAt_reciprocalPart {x : ℝ} (hx : x ≠ 0) (hx1 : 1-x ≠ 0) :
    HasDerivAt reciprocalPart (reciprocalSlope x) x := by
  have hh := (hasDerivAt_inv hx).add (((hasDerivAt_id x).const_sub 1).inv hx1)
  simp only [reciprocalPart,one_div]
  apply hh.congr_deriv
  dsimp [reciprocalSlope]
  field_simp [hx,hx1]
  <;> ring

theorem hasDerivAt_reciprocalSlope {x : ℝ} (hx : x ≠ 0) (hx1 : 1-x ≠ 0) :
    HasDerivAt reciprocalSlope (reciprocalCurvature x) x := by
  have hh := ((((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx)).neg).add
    ((((hasDerivAt_id x).const_sub 1).pow 2).inv (pow_ne_zero 2 hx1))
  simp only [reciprocalSlope,neg_div,one_div]
  apply hh.congr_deriv
  dsimp [reciprocalCurvature]
  field_simp [hx,hx1]
  <;> ring

theorem hasDerivAt_logDensity {x : ℝ} (hx : x ∈ Icc (a:ℝ) (b:ℝ)) :
    HasDerivAt logDensity (densitySlope x) x := by
  obtain ⟨hx0,hx1,hg⟩ := source_positive hx
  have hh := (hasDerivAt_logPart hg.ne').div
    ((hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1))
    (mul_ne_zero hx0.ne' hx1.ne')
  apply hh.congr_deriv
  dsimp [densitySlope,logSlope,reciprocalPart,reciprocalSlope]
  field_simp [hx0.ne',hx1.ne',hg.ne']
  <;> ring

/-- This is exactly main_second(t,9), including the negative log curvature. -/
theorem hasDerivAt_densitySlope {x : ℝ} (hx : x ∈ Icc (a:ℝ) (b:ℝ)) :
    HasDerivAt densitySlope (densityCurvature x) x := by
  obtain ⟨hx0,hx1,hg⟩ := source_positive hx
  have hh := ((hasDerivAt_logSlope hg.ne').mul
    (hasDerivAt_reciprocalPart hx0.ne' hx1.ne')).add
    ((hasDerivAt_logPart hg.ne').mul (hasDerivAt_reciprocalSlope hx0.ne' hx1.ne'))
  apply hh.congr_deriv
  dsimp [densityCurvature]
  ring

theorem continuousOn_densityCurvature :
    ContinuousOn densityCurvature (Icc (a:ℝ) (b:ℝ)) := by
  have hx : ∀ x ∈ Icc (a:ℝ) (b:ℝ), x ≠ 0 :=
    fun x hx => (source_positive hx).1.ne'
  have hx1 : ∀ x ∈ Icc (a:ℝ) (b:ℝ), 1-x ≠ 0 :=
    fun x hx => (source_positive hx).2.1.ne'
  have hg : ∀ x ∈ Icc (a:ℝ) (b:ℝ), 1-x-(d:ℝ) ≠ 0 :=
    fun x hx => (source_positive hx).2.2.ne'
  have hlog : ContinuousOn logPart (Icc (a:ℝ) (b:ℝ)) :=
    fun x h => (hasDerivAt_logPart (hg x h)).continuousAt.continuousWithinAt
  have hls : ContinuousOn logSlope (Icc (a:ℝ) (b:ℝ)) :=
    fun x h => (hasDerivAt_logSlope (hg x h)).continuousAt.continuousWithinAt
  have hr : ContinuousOn reciprocalPart (Icc (a:ℝ) (b:ℝ)) :=
    fun x h => (hasDerivAt_reciprocalPart (hx x h) (hx1 x h)).continuousAt.continuousWithinAt
  have hrs : ContinuousOn reciprocalSlope (Icc (a:ℝ) (b:ℝ)) :=
    fun x h => (hasDerivAt_reciprocalSlope (hx x h) (hx1 x h)).continuousAt.continuousWithinAt
  have hlc : ContinuousOn logCurvature (Icc (a:ℝ) (b:ℝ)) :=
    continuousOn_const.div
      (((continuousOn_const.sub continuousOn_id).sub continuousOn_const).pow 2)
      (fun x h => pow_ne_zero 2 (hg x h))
  have hrc : ContinuousOn reciprocalCurvature (Icc (a:ℝ) (b:ℝ)) :=
    (continuousOn_const.div (continuousOn_id.pow 3) (fun x h => pow_ne_zero 3 (hx x h))).add
      (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 3)
        (fun x h => pow_ne_zero 3 (hx1 x h)))
  exact ((hlc.mul hr).add ((continuousOn_const.mul hls).mul hrs)).add (hlog.mul hrc)

def xInverseBox (l r : ℚ) : Enclosure := ⟨1/r,1/l⟩
def oneMinusInverseBox (l r : ℚ) : Enclosure := ⟨1/(1-l),1/(1-r)⟩
def gapInverseBox (l r : ℚ) : Enclosure := ⟨1/(1-l-d),1/(1-r-d)⟩
def logBox (n : ℕ) (l r : ℚ) : Enclosure :=
  ⟨logLower n (logQuery r),logUpper n (logQuery l)⟩

private theorem inverse_box_contains {l r : ℚ} {x : ℝ}
    (hl : 0 < l) (hlx : (l:ℝ) ≤ x) (hxr : x ≤ (r:ℝ)) :
    (xInverseBox l r).Contains (1/x) := by
  have hlR : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  constructor <;> simp only [xInverseBox,Rat.cast_div,Rat.cast_one]
  · exact one_div_le_one_div_of_le (hlR.trans_le hlx) hxr
  · exact one_div_le_one_div_of_le hlR hlx

theorem inverse_boxes_contain {l r : ℚ} (hl : a ≤ l) (hr : r ≤ b)
    {x : ℝ} (hx : x ∈ Icc (l:ℝ) (r:ℝ)) :
    (xInverseBox l r).Contains (1/x) ∧
      (oneMinusInverseBox l r).Contains (1/(1-x)) ∧
      (gapInverseBox l r).Contains (1/(1-x-(d:ℝ))) := by
  have hlR : (a:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hrR : (r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hr
  constructor
  · exact inverse_box_contains (lt_of_lt_of_le (by norm_num [a]) hl) hx.1 hx.2
  constructor
  · have hp : 0 < (1-r : ℚ) := by norm_num [b] at hr; linarith only [hr]
    have h := inverse_box_contains (l := 1-r) (r := 1-l) (x := 1-x) hp
      (by push_cast; linarith only [hx.2]) (by push_cast; linarith only [hx.1])
    exact h
  · have hp : 0 < (1-r-d : ℚ) := by norm_num [b,d] at hr ⊢; linarith only [hr]
    have h := inverse_box_contains (l := 1-r-d) (r := 1-l-d) (x := 1-x-(d:ℝ)) hp
      (by push_cast; linarith only [hx.2]) (by push_cast; linarith only [hx.1])
    exact h

theorem logBox_contains (n : ℕ) {l r : ℚ} (hl : a ≤ l) (hr : r ≤ b)
    {x : ℝ} (hx : x ∈ Icc (l:ℝ) (r:ℝ)) :
    (logBox n l r).Contains (logPart x) := by
  have hlr : l ≤ r := by exact_mod_cast hx.1.trans hx.2
  have hq (s : ℚ) (hs : s ≤ b) : 2 ≤ logQuery s := by
    norm_num [logQuery,d,b] at hs ⊢
    linarith only [hs]
  have he (s : ℚ) : (logQuery s:ℝ)-1=(1-(s:ℝ)-(d:ℝ))/(d:ℝ) := by
    simp only [logQuery,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_sub]
    ring
  have hlo := (log_bounds n (logQuery r) (hq r hr)).1
  have hup := (log_bounds n (logQuery l) (hq l (hlr.trans hr))).2
  rw [he] at hlo hup
  have hrR : (r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hr
  have hp : 0 < (1-(r:ℝ)-(d:ℝ))/(d:ℝ) := by
    apply div_pos _ (by norm_num [d])
    norm_num [b,d] at hrR ⊢
    linarith only [hrR]
  have hrl : (1-(r:ℝ)-(d:ℝ))/(d:ℝ) ≤ (1-x-(d:ℝ))/(d:ℝ) :=
    div_le_div_of_nonneg_right (by linarith only [hx.2]) (by norm_num [d])
  have hxl : (1-x-(d:ℝ))/(d:ℝ) ≤ (1-(l:ℝ)-(d:ℝ))/(d:ℝ) :=
    div_le_div_of_nonneg_right (by linarith only [hx.1]) (by norm_num [d])
  exact ⟨hlo.trans (Real.log_le_log hp hrl),
    (Real.log_le_log (hp.trans_le hrl) hxl).trans hup⟩

/-- All operations are signed four-corner operations. This expression is
the producer's ldd*r + 2*ld*rd + l*rdd, evaluated on a WHOLE cell. -/
def curvatureBox (n : ℕ) (l r : ℚ) : Enclosure :=
  let X := xInverseBox l r
  let B := oneMinusInverseBox l r
  let G := gapInverseBox l r
  let R := X.add B
  let Rd := (X.mul X).neg.add (B.mul B)
  let Rdd := ((Enclosure.point 2).mul ((X.mul X).mul X)).add
    ((Enclosure.point 2).mul ((B.mul B).mul B))
  (((G.mul G).neg.mul R).add (((Enclosure.point 2).mul G.neg).mul Rd)).add
    ((logBox n l r).mul Rdd)

/-- No sampled curvature or certificate predicate is assumed here. -/
theorem curvatureBox_contains (n : ℕ) {l r : ℚ} (hl : a ≤ l) (hr : r ≤ b)
    {x : ℝ} (hx : x ∈ Icc (l:ℝ) (r:ℝ)) :
    (curvatureBox n l r).Contains (densityCurvature x) := by
  obtain ⟨hX,hB,hG⟩ := inverse_boxes_contain hl hr hx
  have hR := hX.add_contains hB
  have hRd := (hX.mul_contains hX).neg_contains.add_contains (hB.mul_contains hB)
  have hRdd := ((Enclosure.point_contains 2).mul_contains
    ((hX.mul_contains hX).mul_contains hX)).add_contains
      ((Enclosure.point_contains 2).mul_contains ((hB.mul_contains hB).mul_contains hB))
  have hh := (((hG.mul_contains hG).neg_contains.mul_contains hR).add_contains
    (((Enclosure.point_contains 2).mul_contains hG.neg_contains).mul_contains hRd)).add_contains
      ((logBox_contains n hl hr hx).mul_contains hRdd)
  have he :
      -((1/(1-x-(d:ℝ)))*(1/(1-x-(d:ℝ))))*(1/x+1/(1-x))+
        (2*(-(1/(1-x-(d:ℝ)))))*(-(1/x*(1/x))+1/(1-x)*(1/(1-x)))+
        logPart x*(2*(1/x*(1/x)*(1/x))+2*(1/(1-x)*(1/(1-x))*(1/(1-x)))) =
          densityCurvature x := by
    have hlR : (a:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    have hrR : (r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hr
    obtain ⟨hx0,hx1,hg⟩ := source_positive ⟨hlR.trans hx.1,hx.2.trans hrR⟩
    dsimp [densityCurvature,logCurvature,logSlope,reciprocalPart,
      reciprocalSlope,reciprocalCurvature]
    field_simp [hx0.ne',hx1.ne',hg.ne']
    <;> ring
  simpa only [curvatureBox,he,Rat.cast_ofNat] using hh

end
end ImbalancedChen.P5OriginalU9MidpointCurvature
