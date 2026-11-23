import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The exact switched correction on the entire seventh triangle. The
clamped logarithm vanishes on the first Buchstab branch. Two explicit
primitives cancel the derivative of the original moving boundary. -/
namespace ImbalancedChen.P6OriginalSeventhCorrectionIdentity

noncomputable section
open MeasureTheory Set

def delta : ℝ := 59/250
def f (z : ℝ) := Real.log (max 1 (z-1))/max 1 z
private def w (z : ℝ) := Real.log ((1-delta)/(delta*(max 1 z+1)))
private def F (v : ℝ) := ∫ z in (2:ℝ)..v, f z
private def G (v : ℝ) := ∫ z in (2:ℝ)..v, f z*w z

private theorem f_cont : Continuous f := by
  have h (z : ℝ) : (0:ℝ)<max 1 z := zero_lt_one.trans_le (le_max_left _ _)
  exact ((continuous_const.max (continuous_id.sub continuous_const)).log (fun z => (h (z-1)).ne')).div
    (continuous_const.max continuous_id) (fun z => (h z).ne')

private theorem w_cont : Continuous w := by
  have hd : 0<delta := by norm_num [delta]
  have h (z : ℝ) : (0:ℝ)<max 1 z+1 := by linarith only [le_max_left (1:ℝ) z]
  exact (continuous_const.div (continuous_const.mul ((continuous_const.max continuous_id).add continuous_const))
    (fun z => (mul_pos hd (h z)).ne')).log
    (fun z => (div_pos (by norm_num [delta] : 0<1-delta) (mul_pos hd (h z))).ne')

private theorem dF (v : ℝ) : HasDerivAt F (f v) v :=
  intervalIntegral.integral_hasDerivAt_right (f_cont.intervalIntegrable 2 v)
    f_cont.aestronglyMeasurable.stronglyMeasurableAtFilter f_cont.continuousAt

private theorem dG (v : ℝ) : HasDerivAt G (f v*w v) v :=
  intervalIntegral.integral_hasDerivAt_right ((f_cont.mul w_cont).intervalIntegrable 2 v)
    (f_cont.mul w_cont).aestronglyMeasurable.stronglyMeasurableAtFilter (f_cont.mul w_cont).continuousAt

theorem f_zero {z : ℝ} (hz : z≤2) : f z = 0 := by
  simp [f, max_eq_left (show z-1≤1 by linarith)]

private theorem primitives_at_one : F 1 = 0 ∧ G 1 = 0 := by
  have hz {z : ℝ} (hz : z ∈ uIcc (2:ℝ) 1) : f z=0 := by
    rw [uIcc_of_ge (by norm_num : (1:ℝ)≤2)] at hz
    exact f_zero hz.2
  constructor
  · calc
      F 1 = ∫ _ in (2:ℝ)..1, (0:ℝ) := intervalIntegral.integral_congr (fun _ h => hz h)
      _ = 0 := intervalIntegral.integral_zero
  · calc
      G 1 = ∫ _ in (2:ℝ)..1, (0:ℝ) := intervalIntegral.integral_congr (fun _ h => by rw [hz h,zero_mul])
      _ = 0 := intervalIntegral.integral_zero

def v (t u : ℝ) := (1-t)/u-1
private def s (t : ℝ) := 1/t-2

def row (t : ℝ) := ∫ u in t..((1-t)/2), f (v t u)/(t*u^2)

theorem row_kernel_continuous {t : ℝ} (ht : 0<t) :
    ContinuousOn (fun u => f (v t u)/(t*u^2)) (Icc t ((1-t)/2)) := by
  have hu {u : ℝ} (h : u ∈ Icc t ((1-t)/2)) : 0<u := ht.trans_le h.1
  have hv : ContinuousOn (v t) (Icc t ((1-t)/2)) :=
    (continuousOn_const.div continuousOn_id (fun _ h => (hu h).ne')).sub continuousOn_const
  exact (f_cont.comp_continuousOn hv).div (continuousOn_const.mul (continuousOn_id.pow _))
    (fun _ h => (mul_pos ht (sq_pos_of_pos (hu h))).ne')

private theorem semiprime_row {t : ℝ} (ht : t ∈ Icc delta (1/3:ℝ)) :
    row t = F (s t)/(t*(1-t)) := by
  have ht0 : 0<t := (show 0<delta by norm_num [delta]).trans_le ht.1
  have h1 : 0<1-t := by linarith [ht.2]
  have hcap : t≤(1-t)/2 := by linarith [ht.2]
  have hd (u : ℝ) (hu : u ∈ uIcc t ((1-t)/2)) :
      HasDerivAt (fun y => -F (v t y)/(t*(1-t))) (f (v t u)/(t*u^2)) u := by
    rw [uIcc_of_le hcap] at hu
    have hu0 := ht0.trans_le hu.1
    have dv : HasDerivAt (v t) (-(1-t)/u^2) u := by
      apply (((hasDerivAt_const u (1-t)).div (hasDerivAt_id u) hu0.ne').sub_const 1).congr_deriv
      simp <;> ring
    apply (((dF (v t u)).comp u dv).neg.div_const (t*(1-t))).congr_deriv
    field_simp [ht0.ne',hu0.ne',h1.ne']
    <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((row_kernel_continuous ht0).intervalIntegrable_of_Icc hcap)
  have htop : v t ((1-t)/2)=1 := by unfold v; field_simp [h1.ne'] <;> ring
  have hbot : v t t=s t := by unfold v s; field_simp [ht0.ne'] <;> ring
  simpa only [row,htop,hbot,primitives_at_one.1,neg_zero,zero_div,zero_sub,
    neg_div,neg_neg] using he

theorem row_continuous : ContinuousOn row (Icc delta (1/3:ℝ)) := by
  have ht {t : ℝ} (h : t ∈ Icc delta (1/3:ℝ)) : 0<t :=
    (show 0<delta by norm_num [delta]).trans_le h.1
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun y => (dF y).continuousAt
  have hs : ContinuousOn s (Icc delta (1/3:ℝ)) :=
    (continuousOn_const.div continuousOn_id (fun _ h => (ht h).ne')).sub continuousOn_const
  have H := (hF.comp_continuousOn hs).div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun t (h : t ∈ Icc delta (1/3:ℝ)) => (mul_pos (ht h) (show 0<1-t by linarith [h.2])).ne')
  exact H.congr (fun t h => semiprime_row h)

private def L (t : ℝ) := Real.log (((1-delta)*t)/(delta*(1-t)))

private theorem outer_primitive {t : ℝ} (ht : t ∈ Icc delta (1/3:ℝ)) :
    HasDerivAt (fun y => L y*F (s y)-G (s y)) (row t) t := by
  have ht0 : 0<t := (show 0<delta by norm_num [delta]).trans_le ht.1
  have h1 : 0<1-t := by linarith [ht.2]
  have hd : 0<delta := by norm_num [delta]
  have hd1 : 0<1-delta := by norm_num [delta]
  have hs : 1≤s t := by
    have H : 3≤1/t := (le_div_iff₀ ht0).mpr (by linarith [ht.2])
    unfold s; linarith
  have hW : w (s t)=L t := by
    have harg : s t + 1 = (1-t)/t := by
      unfold s
      field_simp [ht0.ne'] <;> ring
    unfold w L
    rw [max_eq_right hs,harg,← mul_div_assoc,div_div_eq_mul_div]
  have dL : HasDerivAt L (1/(t*(1-t))) t := by
    have hn := (hasDerivAt_id t).const_mul (1-delta)
    have he := ((hasDerivAt_id t).const_sub 1).const_mul delta
    apply ((hn.div he (mul_pos hd h1).ne').log (div_pos (mul_pos hd1 ht0) (mul_pos hd h1)).ne').congr_deriv
    change (((1-delta)*1*(delta*(1-t)) - ((1-delta)*t)*(delta*(-1))) /
      (delta*(1-t))^2) / (((1-delta)*t)/(delta*(1-t))) = 1/(t*(1-t))
    rw [div_div_div_eq]
    apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hd.ne' h1.ne'))
      (mul_ne_zero hd1.ne' ht0.ne')) (mul_ne_zero ht0.ne' h1.ne')).mpr
    ring
  have ds : HasDerivAt s (-1/t^2) t := by
    apply (((hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id t) ht0.ne').sub_const 2).congr_deriv
    simp <;> ring
  rw [semiprime_row ht]
  apply ((dL.mul ((dF _).comp t ds)).sub ((dG _).comp t ds)).congr_deriv
  simp only [hW,Function.comp_apply]
  ring

theorem correction_identity :
    (∫ t in delta..(1/3:ℝ), row t) =
      ∫ t in (2:ℝ)..(132/59:ℝ),
        (Real.log (t-1)/t)*Real.log ((1-59/250)/((59/250)*(t+1))) := by
  have hle : delta≤1/3 := by norm_num [delta]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=delta) (b:=1/3)
    (fun t ht => outer_primitive (uIcc_of_le hle ▸ ht))
    (row_continuous.intervalIntegrable_of_Icc hle)
  have hbot : s delta=132/59 := by norm_num [s,delta]
  have htop : s (1/3)=1 := by norm_num [s]
  have hL : L delta=0 := by norm_num [L,delta]
  have hG : (∫ t in delta..(1/3:ℝ), row t)=G (132/59) := by
    simpa only [hbot,htop,hL,primitives_at_one.1,primitives_at_one.2,
      mul_zero,zero_mul,sub_zero,zero_sub,neg_neg] using he
  rw [hG]
  unfold G
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (2:ℝ)≤132/59)] at ht
  simp only [f,w,max_eq_right (show 1≤t-1 by linarith [ht.1]),max_eq_right (show 1≤t by linarith [ht.1]),delta]

/-- The integrand with the exact moving branch in the manuscript. -/
def branchKernel (t u : ℝ) : ℝ :=
  if u < (1-t)/3 then Real.log ((1-t-2*u)/u)/(t*u*(1-t-u)) else 0

theorem kernel_branch {t u : ℝ} (ht : delta≤t) (htu : t≤u) (hcap : u≤(1-t)/2) :
    f (v t u)/(t*u^2) = branchKernel t u := by
  have ht0 : 0<t := (show 0<delta by norm_num [delta]).trans_le ht
  have hu0 := ht0.trans_le htu
  have hgap : 0<1-t-u := by linarith
  by_cases hc : u < (1-t)/3
  · have hv : 2<v t u := by
      have h : 3<(1-t)/u := (lt_div_iff₀ hu0).mpr (by linarith)
      dsimp [v]; linarith
    have h1 : v t u-1 = (1-t-2*u)/u := by unfold v; field_simp [hu0.ne'] <;> ring
    have h2 : v t u = (1-t-u)/u := by unfold v; field_simp [hu0.ne'] <;> ring
    rw [branchKernel,if_pos hc,f,max_eq_right (show 1≤v t u-1 by linarith),
      max_eq_right (show 1≤v t u by linarith),h1,h2]
    field_simp [ht0.ne',hu0.ne',hgap.ne']
    <;> ring
  · have hv : v t u≤2 := by
      have h : (1-t)/u≤3 := (div_le_iff₀ hu0).mpr (by linarith [le_of_not_gt hc])
      dsimp [v]; linarith
    simp [branchKernel,hc,f_zero hv]

theorem literal_double_correction_identity :
    (∫ t in (59/250:ℝ)..(1/3:ℝ), ∫ u in t..((1-t)/2),
      if u < (1-t)/3 then Real.log ((1-t-2*u)/u)/(t*u*(1-t-u)) else 0) =
      ∫ t in (2:ℝ)..(132/59:ℝ),
        (Real.log (t-1)/t)*Real.log ((1-59/250)/((59/250)*(t+1))) := by
  rw [← correction_identity]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59/250:ℝ)≤1/3)] at ht
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith [ht.2] : t≤(1-t)/2)] at hu
  exact (kernel_branch ht.1 hu.1 hu.2).symm

end
end ImbalancedChen.P6OriginalSeventhCorrectionIdentity
