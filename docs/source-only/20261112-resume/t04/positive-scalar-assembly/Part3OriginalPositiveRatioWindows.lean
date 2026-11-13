import ImbalancedChen.Part3OriginalPositiveStripDiagonal
import ImbalancedChen.Part3ActualPositivePacketHighFrequency
import ImbalancedChen.Part3PrescribedLogTensorWindows
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Batteries.Tactic.OpenPrivate

/-! A fixed unit-mass product profile and actual mean-zero approximations
to the manuscript's full positive-sign ratio profile. -/
namespace ImbalancedChen.Part3.OriginalPositiveRatioWindows20261112

noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology ContDiff BigOperators
open RadialSchrodingerL2Form20261025a P3NativePeriod64SamplingSourceOnly (D4)
open PrescribedLogTensorWindows20261112 (window win win_smooth win_bounds win_nonzero win_plateau)
open OriginalPositiveStrip20261112 (h smooth zero_mass)
open OriginalPositiveStripDensity20261112 (h_even h_jets)
open private abs_exp_integrable from ImbalancedChen.Part3OriginalPositiveStripContour

def unit : RadialTest where
  function s := (window.normed volume s:ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp window.contDiff_normed
  compact := window.hasCompactSupport_normed.comp_left (g:=Complex.ofReal) (by simp)

theorem unit_mass : ∫ s : ℝ,unit.function s=1 := by
  change (∫ s : ℝ,(window.normed volume s:ℂ))=1
  rw [integral_complex_ofReal,window.integral_normed,ofReal_one]

theorem unit_even (w : ℝ) : unit.function (-w)=unit.function w := by
  change (window.normed volume (-w):ℂ)=(window.normed volume w:ℂ)
  rw [window.normed_neg]

private def base (x : ℝ) : ℂ := (win x:ℂ)
private theorem base_smooth : ContDiff ℝ ∞ base := Complex.ofRealCLM.contDiff.comp win_smooth
private theorem base_compact : HasCompactSupport base :=
  window.hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp)

def scale (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
def cut (n : ℕ) (w : ℝ) := base (scale n*w)

private theorem scale_range (n : ℕ) : 0<scale n ∧ scale n≤1 := by
  have a : (1:ℝ)≤(n:ℝ)+1 := by linarith only [Nat.cast_nonneg (R:=ℝ) n]
  exact ⟨by dsimp [scale]; positivity,inv_le_one_of_one_le₀ a⟩

private theorem cut_compact (n : ℕ) : HasCompactSupport (cut n) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=-2/scale n) (b:=2/scale n))
  intro w hw
  have p := (scale_range n).1
  have wm : win (scale n*w)≠0 := by intro z; exact hw (by simp [cut,base,z])
  have e := win_nonzero wm
  exact ⟨(div_le_iff₀ p).2 (by linarith only [e.1]),(le_div_iff₀ p).2 (by linarith only [e.2])⟩

private theorem cut_smooth (n : ℕ) : ContDiff ℝ ∞ (cut n) :=
  base_smooth.comp (contDiff_const.mul contDiff_id)

private theorem cut_le (n : ℕ) (w : ℝ) : ‖cut n w‖≤1 := by
  simpa only [cut,base,Complex.norm_real,Real.norm_of_nonneg (win_bounds _).1] using (win_bounds (scale n*w)).2

private theorem cut_eventually (w : ℝ) : ∀ᶠ n : ℕ in atTop,cut n w=1 := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop |w|] with n hn
  have H : |scale n*w|≤1 := by
    rw [abs_mul,abs_of_pos (scale_range n).1,scale,inv_mul_eq_div,div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)]
    linarith
  simp [cut,base,win_plateau (abs_le.mp H)]

def mass (ell : D4→ℤ) (Y : ℝ) (n : ℕ) := ∫ w : ℝ,cut n w*h ell Y w

def ratio (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ) : RadialTest where
  function w := cut n w*h ell Y w-mass ell Y n*unit.function w
  smooth := ((cut_smooth n).mul (smooth ell hY)).sub (contDiff_const.mul unit.smooth)
  compact := (cut_compact n).mul_right.sub unit.compact.mul_left

theorem ratio_zero (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ) : ∫ w : ℝ,(ratio ell hY n).function w=0 := by
  have A := ((cut_smooth n).continuous.mul (smooth ell hY).continuous).integrable_of_hasCompactSupport
    (cut_compact n).mul_right
  have B := (unit.smooth.continuous.integrable_of_hasCompactSupport unit.compact).const_mul (mass ell Y n)
  rw [ratio,integral_sub A B,integral_const_mul,unit_mass,mul_one,mass,sub_self]

theorem ratio_even (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ) (w : ℝ) :
    (ratio ell hY n).function (-w)=(ratio ell hY n).function w := by
  change cut n (-w)*_-_*unit.function (-w)=_
  have E : cut n (-w)=cut n w := by simp [cut,base,win,mul_neg,window.neg]
  rw [E,h_even,unit_even]

private theorem h_L1 (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : Integrable (h ell Y) := by
  have A := OriginalPositiveStrip20261112.hhat_L1 ell hY (ξ:=0) (by norm_num)
  simpa [OriginalPositiveStripContour20261112.wave] using A

private theorem mass_bound (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ) :
    ‖mass ell Y n‖≤∫ w : ℝ,‖h ell Y w‖ := by
  apply norm_integral_le_of_norm_le (h_L1 ell hY).norm
  exact ae_of_all _ fun w => by rw [norm_mul]; simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (cut_le n w) (norm_nonneg _)

theorem mass_limit (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : Tendsto (mass ell Y) atTop (𝓝 0) := by
  rw [← zero_mass ell hY]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖h ell Y x‖)
  · exact fun n => ((cut_smooth n).continuous.mul (smooth ell hY).continuous).aestronglyMeasurable
  · exact (h_L1 ell hY).norm
  · intro n; exact ae_of_all _ fun w => by rw [norm_mul]; simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (cut_le n w) (norm_nonneg _)
  · exact ae_of_all _ fun w => tendsto_const_nhds.congr' ((cut_eventually w).mono fun n he => by rw [he,one_mul])

theorem ratio_pointwise (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    Tendsto (fun n => (ratio ell hY n).function w) atTop (𝓝 (h ell Y w)) := by
  have A := (mass_limit ell hY).mul_const (unit.function w)
  have B : Tendsto (fun n => cut n w*h ell Y w) atTop (𝓝 (h ell Y w)) :=
    tendsto_const_nhds.congr' ((cut_eventually w).mono fun n he => by rw [he,one_mul])
  simpa only [ratio,zero_mul,sub_zero] using B.sub A

private theorem jet_comp {T : ℝ→ℂ} (hc : HasCompactSupport T) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j T) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem compact_decay {T : ℝ→ℂ} (hs : ContDiff ℝ ∞ T) (hc : HasCompactSupport T) (j : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ x : ℝ,‖iteratedDeriv j T x‖≤C*Real.exp (-|x|) := by
  let f := iteratedDeriv j T
  have fc := jet_comp hc j
  have kk := fc.exists_bound_of_continuousOn (f:=fun x : ℝ => Real.exp |x|*‖f x‖)
    (((Real.continuous_exp.comp continuous_abs).mul (hs.continuous_iteratedDeriv j (by simp)).norm).continuousOn)
  obtain ⟨C,E⟩ := kk
  refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
  by_cases hx : x∈tsupport f
  · have U := (le_abs_self (Real.exp |x|*‖f x‖)).trans ((E x hx).trans (le_max_left _ _))
    rw [Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
    simpa only [mul_comm] using U
  · change ‖f x‖≤_; rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]; positivity

private theorem cut_jets (j : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ n w,‖iteratedDeriv j (cut n) w‖≤C := by
  obtain ⟨C,c,P⟩ := compact_decay base_smooth base_compact j
  refine ⟨C,c,fun n w => ?_⟩
  rw [cut,iteratedDeriv_comp_const_smul (base_smooth.of_le (by simp)) (scale n),norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (scale_range n).1.le j)]
  have b := P (scale n*w)
  have ex : Real.exp (-|scale n*w|)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  simpa only [one_mul,mul_one] using mul_le_mul (pow_le_one₀ (scale_range n).1.le (scale_range n).2)
    (b.trans (mul_le_mul_of_nonneg_left ex c)) (norm_nonneg _) zero_le_one

/-- Constants depend on the specified mark and scale. All derivatives
of these actual profiles have a common integrable exponential envelope. -/
theorem ratio_jets (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ n x,‖iteratedDeriv j (ratio ell hY n).function x‖≤C*Real.exp (-|x|) := by
  classical
  choose B b HB using cut_jets
  choose H a HH using h_jets ell hY
  obtain ⟨K,k,HK⟩ := compact_decay unit.smooth unit.compact j
  let M := ∫ w : ℝ,‖h ell Y w‖
  have m : 0≤M := integral_nonneg fun _ => norm_nonneg _
  let A := ∑ i∈Finset.range (j+1),(j.choose i:ℝ)*B i*H (j-i)
  have a0 : 0≤A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨A+M*K,by positivity,fun n x => ?_⟩
  have P : ‖iteratedDeriv j (fun x => cut n x*h ell Y x) x‖≤A*Real.exp (-|x|) := by
    change ‖iteratedDeriv j (cut n*h ell Y) x‖≤_
    rw [iteratedDeriv_mul ((cut_smooth n).of_le (by simp)).contDiffAt ((smooth ell hY).of_le (by simp)).contDiffAt,
      Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi; rw [norm_mul,norm_mul,Complex.norm_natCast,mul_assoc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul (HB i n x) (HH (j-i) x) (norm_nonneg _) (b i)) (Nat.cast_nonneg (R:=ℝ) (j.choose i))
  change ‖iteratedDeriv j ((cut n*h ell Y)-(fun w => mass ell Y n*unit.function w)) x‖≤_
  rw [iteratedDeriv_sub (((cut_smooth n).mul (smooth ell hY)).of_le (by simp)).contDiffAt
    ((contDiff_const.mul unit.smooth).of_le (by simp)).contDiffAt,iteratedDeriv_const_mul_field]
  have g := mul_le_mul (mass_bound ell hY n) (HK x) (norm_nonneg _) m
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ A*Real.exp (-|x|)+M*(K*Real.exp (-|x|)) := by rw [norm_mul]; exact add_le_add P g
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalPositiveRatioWindows20261112
