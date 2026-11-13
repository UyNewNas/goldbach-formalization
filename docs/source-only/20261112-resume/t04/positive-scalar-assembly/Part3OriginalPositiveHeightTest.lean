import ImbalancedChen.Part3OriginalPositiveRatioWindows
import ImbalancedChen.Part3ActualPositivePacketHighFrequency

/-! The bivariate height in the original physical order psi(a) * star(phi(b)).
The same definition is used by the geometric and spectral consumers. -/
namespace ImbalancedChen.Part3.OriginalPositiveHeightTest20261112

noncomputable section
open Set Complex Filter
open scoped Topology ContDiff
open RadialSchrodingerL2Form20261025a ActualPositiveScalarPacket20261112
open ActualPositivePacketHighFrequency20261112 (coords)
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalPositiveRatioWindows20261112 (unit ratio)

def logHeight (η H : RadialTest) (R x y : ℝ) : ℂ :=
  (Real.exp ((x+y)/2):ℂ)*η.function (x+y+R)*H.function ((x-y)/2)

def height (η H : RadialTest) (R a b : ℝ) : ℂ :=
  if 0<a ∧ 0<b then logHeight η H R (Real.log a) (Real.log b) else 0

theorem log_smooth (η H : RadialTest) (R : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (logHeight η H R)) := by
  exact ((by fun_prop : ContDiff ℝ ∞ (fun z : ℝ×ℝ => (Real.exp ((z.1+z.2)/2):ℂ))).mul
    (η.smooth.comp ((contDiff_fst.add contDiff_snd).add contDiff_const))).mul
      (H.smooth.comp ((contDiff_fst.sub contDiff_snd).div_const 2))

theorem log_compact (η H : RadialTest) (R : ℝ) :
    HasCompactSupport (Function.uncurry (logHeight η H R)) := by
  obtain ⟨S,s0,hs⟩ := test_radius η
  obtain ⟨U,u0,hu⟩ := test_radius H
  let B := S+|R|+U+1
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc : IsCompact (Icc (-B) B)).prod (isCompact_Icc : IsCompact (Icc (-B) B)))
  rintro ⟨x,y⟩ hx
  change (Real.exp ((x+y)/2):ℂ)*η.function (x+y+R)*H.function ((x-y)/2)≠0 at hx
  have a := abs_le.mp (hs _ (right_ne_zero_of_mul (left_ne_zero_of_mul hx)))
  have b := abs_le.mp (hu _ (right_ne_zero_of_mul hx))
  dsimp [B]; constructor <;> constructor <;> linarith [le_abs_self R,neg_le_abs R]

theorem height_exp (η H : RadialTest) (R x y : ℝ) :
    height η H R (Real.exp x) (Real.exp y)=logHeight η H R x y := by
  simp only [height,Real.exp_pos,and_self,if_true,Real.log_exp]

theorem height_pos (η H : RadialTest) (R : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    height η H R a b=(Real.sqrt (a*b):ℂ)*η.function (Real.log (a*b)+R)*
      H.function ((Real.log a-Real.log b)/2) := by
  rw [height,if_pos ⟨ha,hb⟩,logHeight,Real.log_mul ha.ne' hb.ne']
  congr 2
  apply Complex.ofReal_inj.mpr
  apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg ha.le hb.le),← Real.exp_nat_mul]
  norm_num; rw [show 2*((Real.log a+Real.log b)/2)=Real.log a+Real.log b by ring,
    Real.exp_add,Real.exp_log ha,Real.exp_log hb]

abbrev original (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (R : ℝ) (n : ℕ) :=
  height unit (ratio ell hY n) R

end
end ImbalancedChen.Part3.OriginalPositiveHeightTest20261112
