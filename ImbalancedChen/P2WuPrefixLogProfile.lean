import ImbalancedChen.P2WuJointWindowProfile
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
An actual logarithmic outer profile inside the already priced Wu prefix
collars.  The logarithmic width is w/(1+w); each original half-open window
still has value one, and the new profile is pointwise at most the existing
physical profile on positive original-prime coordinates.

Manuscript: release-20261106/en/argument.tex, eq:current-PP and the proof of
prop:current-positive-product; coefficient-appendix.tex, lines 323--331 and
551--561.  This supplies geometric weights, not a distribution estimate.
SOURCE ONLY: not compiled and no kernel credit until separately replayed.
-/
namespace ImbalancedChen.P2WuPrefixLogProfile

noncomputable section
open Finset Real P4B
open scoped BigOperators Classical ContDiff

def innerLogWidth (w : ℝ) : ℝ := w / (1+w)

theorem innerLogWidth_pos {w : ℝ} (hw : 0 < w) : 0 < innerLogWidth w :=
  div_pos hw (by linarith)

def windowFromLogs (a b w t : ℝ) : ℝ :=
  smoothGateUpperStep (innerLogWidth w) (t-a) *
    smoothGateUpperStep (innerLogWidth w) (b-t)

def profileFromLogs {i r : ℕ} (a b : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) (t : Fin r → ℝ) : ℝ :=
  ∏ j, windowFromLogs (a j) (b j) w (t (slot j))

def physicalProfile {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) (x : Fin r → ℝ) : ℝ :=
  profileFromLogs (fun j => log (L j)) (fun j => log (V j)) w slot
    (fun l => log (x l))

theorem windowFromLogs_bounds (a b w t : ℝ) :
    0 ≤ windowFromLogs a b w t ∧ windowFromLogs a b w t ≤ 1 := by
  have h₁ := smoothGateUpperStep_bounds (innerLogWidth w) (t-a)
  have h₂ := smoothGateUpperStep_bounds (innerLogWidth w) (b-t)
  exact ⟨mul_nonneg h₁.1 h₂.1,
    (mul_le_mul_of_nonneg_right h₁.2 h₂.1).trans (by simpa using h₂.2)⟩

theorem profileFromLogs_bounds {i r : ℕ} (a b : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) (t : Fin r → ℝ) :
    0 ≤ profileFromLogs a b w slot t ∧ profileFromLogs a b w slot t ≤ 1 := by
  unfold profileFromLogs
  exact ⟨prod_nonneg (fun j _ => (windowFromLogs_bounds _ _ _ _).1),
    prod_le_one (fun j _ => (windowFromLogs_bounds _ _ _ _).1)
      (fun j _ => (windowFromLogs_bounds _ _ _ _).2)⟩

theorem physicalProfile_bounds {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) (x : Fin r → ℝ) :
    0 ≤ physicalProfile L V w slot x ∧ physicalProfile L V w slot x ≤ 1 :=
  profileFromLogs_bounds _ _ _ _ _

theorem profileFromLogs_smooth {i r : ℕ} (a b : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) : ContDiff ℝ ∞ (profileFromLogs a b w slot) := by
  unfold profileFromLogs
  apply contDiff_prod
  intro j _
  have hx : ContDiff ℝ ∞ (fun t : Fin r → ℝ => t (slot j)) :=
    contDiff_apply ℝ ℝ (slot j)
  exact ((contDiff_smoothGateUpperStep _).comp (hx.sub contDiff_const)).mul
    ((contDiff_smoothGateUpperStep _).comp (contDiff_const.sub hx))

theorem physicalProfile_one {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ}
    {slot : Fin i → Fin r} {x : Fin r → ℝ}
    (hL : ∀ j, 0 < L j) (hw : 0 < w)
    (hin : ∀ j, L j ≤ x (slot j) ∧ x (slot j) ≤ V j) :
    physicalProfile L V w slot x = 1 := by
  unfold physicalProfile profileFromLogs
  apply prod_eq_one
  intro j _
  have hx := (hL j).trans_le (hin j).1
  have hlo := log_le_log (hL j) (hin j).1
  have hhi := log_le_log hx (hin j).2
  exact (show windowFromLogs (log (L j)) (log (V j)) w (log (x (slot j))) = 1 by
    rw [windowFromLogs, smoothGateUpperStep_eq_one (innerLogWidth_pos hw)
      (sub_nonneg.mpr hlo), smoothGateUpperStep_eq_one (innerLogWidth_pos hw)
      (sub_nonneg.mpr hhi), one_mul])

private theorem lower_step_le {L w x : ℝ} (hL : 0 < L) (hw : 0 < w) (hx : 0 < x) :
    smoothGateUpperStep (innerLogWidth w) (log x-log L) ≤ 
      smoothGateUpperStep (P2WuJointWindowProfile.lowerBase L w*w) (x-L) := by
  have hlog := log_le_sub_one_of_pos (div_pos hx hL)
  rw [log_div hx.ne' hL.ne'] at hlog
  have hmargin : log x-log L ≤ (x-L)/L := by
    simpa only [sub_div, div_self hL.ne'] using hlog
  have hh := div_le_div_of_nonneg_right hmargin (innerLogWidth_pos hw).le
  have he : ((x-L)/L)/innerLogWidth w = 
      (x-L)/(P2WuJointWindowProfile.lowerBase L w*w) := by
    unfold innerLogWidth P2WuJointWindowProfile.lowerBase
    field_simp [hL.ne', hw.ne', show (1:ℝ)+w ≠ 0 by linarith]
  apply Real.smoothTransition.monotone
  exact add_le_add le_rfl (hh.trans_eq he)

private theorem upper_step_le {V w x : ℝ} (hV : 0 < V) (hw : 0 < w) (hx : 0 < x) :
    smoothGateUpperStep (innerLogWidth w) (log V-log x) ≤ 
      smoothGateUpperStep (V*w) (V-x) := by
  have hs := innerLogWidth_pos hw
  have h1 : 0 < 1+w := by linarith
  by_cases hleft : x ≤ V
  · rw [smoothGateUpperStep_eq_one hs (sub_nonneg.mpr (log_le_log hx hleft)),
      smoothGateUpperStep_eq_one (mul_pos hV hw) (sub_nonneg.mpr hleft)]
  have hVx : V < x := lt_of_not_ge hleft
  have hlog := log_le_sub_one_of_pos (div_pos hV hx)
  rw [log_div hV.ne' hx.ne'] at hlog
  have hmargin : log V-log x ≤ (V-x)/x := by
    simpa only [sub_div, div_self hx.ne'] using hlog
  by_cases hcap : x ≤ V*(1+w)
  · have hden : x*innerLogWidth w ≤ V*w := by
      rw [innerLogWidth, ←mul_div_assoc]
      apply (div_le_iff₀ h1).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hcap hw.le]
    have hratio : (V-x)/(x*innerLogWidth w) ≤ (V-x)/(V*w) := by
      apply (div_le_div_iff₀ (mul_pos hx hs) (mul_pos hV hw)).mpr
      exact mul_le_mul_of_nonpos_left hden (sub_nonpos.mpr hVx.le)
    have hh := (div_le_div_of_nonneg_right hmargin hs.le).trans
      (by simpa only [div_div] using hratio)
    exact Real.smoothTransition.monotone (add_le_add le_rfl hh)
  · have hVsmall : V ≤ x/(1+w) :=
      (le_div_iff₀ h1).mpr (le_of_not_ge hcap)
    have hid : -(innerLogWidth w)*x = x/(1+w)-x := by
      unfold innerLogWidth
      field_simp [h1.ne']
      ring
    have hratio : (V-x)/x ≤ -(innerLogWidth w) := by
      apply (div_le_iff₀ hx).mpr
      rw [hid]
      linarith only [hVsmall]
    rw [smoothGateUpperStep_eq_zero hs (hmargin.trans hratio)]
    exact smoothGateUpperStep_nonneg _ _

/-- The new logarithmic profile uses a subset of every already priced
physical collar, including both half-open endpoint conventions. -/
theorem physicalProfile_le_original {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ}
    {slot : Fin i → Fin r} {x : Fin r → ℝ}
    (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w)
    (hx : ∀ j, 0 < x (slot j)) :
    physicalProfile L V w slot x ≤ P2WuJointWindowProfile.profile L V w slot x := by
  unfold physicalProfile profileFromLogs P2WuJointWindowProfile.profile
  apply prod_le_prod
  · intro j _
    exact (windowFromLogs_bounds _ _ _ _).1
  · intro j _
    exact mul_le_mul (lower_step_le (hL j) hw (hx j))
      (upper_step_le (hV j) hw (hx j)) (smoothGateUpperStep_nonneg _ _)
      (smoothGateUpperStep_nonneg _ _)

theorem physicalProfile_support {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ}
    {slot : Fin i → Fin r} {x : Fin r → ℝ}
    (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w)
    (hx : ∀ j, 0 < x (slot j)) (hn : physicalProfile L V w slot x ≠ 0) :
    ∀ j, P2WuJointWindowProfile.lowerBase (L j) w < x (slot j) ∧
      x (slot j) < V j*(1+w) := by
  have hold : P2WuJointWindowProfile.profile L V w slot x ≠ 0 := by
    intro hz
    exact hn (le_antisymm ((physicalProfile_le_original hL hV hw hx).trans_eq hz)
      (physicalProfile_bounds _ _ _ _ _).1)
  exact (P2WuJointWindowProfile.profile_nonzero_iff hL hV hw).mp hold

/-- An arbitrary multiplicative chart only translates the logarithmic
endpoints. The derivative budget may therefore be chosen before every
positive prime point and every moving source-box endpoint. -/
theorem physicalProfile_log_chart {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) (p : Fin r → ℝ) (hp : ∀ l, 0 < p l) :
    (fun z : Fin r → ℝ => physicalProfile L V w slot
      (fun l => p l*exp (z l))) = 
    profileFromLogs (fun j => log (L j)-log (p (slot j)))
      (fun j => log (V j)-log (p (slot j))) w slot := by
  funext z
  unfold physicalProfile profileFromLogs
  apply prod_congr rfl
  intro j _
  simp only [windowFromLogs, log_mul (hp _).ne' (exp_pos _).ne', log_exp]
  congr 1 <;> congr 1 <;> ring

end
end ImbalancedChen.P2WuPrefixLogProfile
