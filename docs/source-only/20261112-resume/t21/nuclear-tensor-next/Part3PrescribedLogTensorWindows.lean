import ImbalancedChen.Part3SmoothIntegerUnitPartition
import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Compact height profiles for the prescribed opposite-sign lift. All
frequencies on the same integer log window have the same modulus. -/
namespace ImbalancedChen.Part3.PrescribedLogTensorWindows20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Classical BigOperators Topology ContDiff
open SmoothIntegerUnitPartition20261026b P3TwoLogMixed22SourceOnly

def rho (x : ℝ) : ℂ := (horizontalUnitPartition x : ℂ)
theorem rho_smooth : ContDiff ℝ ∞ rho :=
  Complex.ofRealCLM.contDiff.comp horizontalUnitPartition_cinfty

theorem rho_nonzero {x : ℝ} (h : rho x ≠ 0) : x ∈ Ioo (-1:ℝ) 1 := by
  constructor
  · by_contra! hx; exact h (by simp [rho,horizontalUnitPartition_zero_left x hx])
  · by_contra! hx; exact h (by simp [rho,horizontalUnitPartition_zero_right x hx])

theorem rho_support : tsupport rho ⊆ Icc (-1:ℝ) 1 :=
  closure_minimal (fun _ hx => Ioo_subset_Icc_self (rho_nonzero hx)) isClosed_Icc

theorem rho_sum (x : ℝ) : HasSum (fun i : ℤ => rho (x-(i:ℝ))) 1 := by
  let n := Int.floor x
  have h : Summable (fun i : ℤ => horizontalUnitPartition (x-(i:ℝ))) := by
    apply summable_of_ne_finset_zero (s := {n,n+1})
    intro i hi
    have h0 : i ≠ n := by intro e; exact hi (by simp [e])
    have h1 : i ≠ n+1 := by intro e; exact hi (by simp [e])
    have hx := Int.floor_le x
    have hx' := Int.lt_floor_add_one x
    rcases (show i ≤ n-1 ∨ n+2 ≤ i by omega) with hlow | hhigh
    · have ht : (i:ℝ) ≤ (n:ℝ)-1 := by exact_mod_cast hlow
      exact horizontalUnitPartition_zero_right _ (by dsimp [n] at ht; linarith)
    · have ht : (n:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast hhigh
      exact horizontalUnitPartition_zero_left _ (by dsimp [n] at ht; linarith)
  have hs : (∑' i : ℤ, horizontalUnitPartition (x-(i:ℝ))) = 1 := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun i : ℤ => horizontalUnitPartition (x-(i:ℝ)))]
    simpa [sub_eq_add_neg] using horizontalUnitPartition_integer_sum x
  have hh : HasSum (fun i : ℤ => horizontalUnitPartition (x-(i:ℝ))) 1 := hs ▸ h.hasSum
  simpa only [rho,Complex.ofReal_one] using (Complex.ofRealCLM.hasSum hh)

def window : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def win (x : ℝ) : ℝ := window x
theorem win_smooth : ContDiff ℝ ∞ win := window.contDiff
theorem win_bounds (x : ℝ) : 0 ≤ win x ∧ win x ≤ 1 := ⟨window.nonneg,window.le_one⟩
theorem win_plateau {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) : win x = 1 := by
  apply window.one_of_mem_closedBall
  simpa [window,Metric.mem_closedBall,Real.dist_eq,abs_le] using hx
theorem win_nonzero {x : ℝ} (h : win x ≠ 0) : x ∈ Icc (-2:ℝ) 2 := by
  have hh := subset_tsupport (fun t : ℝ => window t) h
  rw [window.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_le] at hh
  exact hh

def pattern (i k : ℤ) (y : ℝ) : ℂ :=
  if 0 < y then (win (Real.log y-(i:ℝ)) : ℂ)*basis k (Real.log y-(i:ℝ)) else 0
def rightPattern (j l : ℤ) (y : ℝ) : ℂ := star (pattern j l y)

theorem pattern_exp (i k : ℤ) (x : ℝ) :
    pattern i k (Real.exp x) = (win (x-(i:ℝ)) : ℂ)*basis k (x-(i:ℝ)) := by
  simp only [pattern,Real.exp_pos,if_pos,Real.log_exp]

theorem pattern_norm (i k : ℤ) (y : ℝ) :
    ‖pattern i k y‖ = if 0 < y then win (Real.log y-(i:ℝ)) else 0 := by
  by_cases h : 0 < y
  · simp only [pattern,if_pos h,norm_mul,norm_basis,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (win_bounds _).1]
  · simp [pattern,h]

theorem right_norm (j l : ℤ) (y : ℝ) : ‖rightPattern j l y‖ = ‖pattern j 0 y‖ := by
  rw [rightPattern,norm_star,pattern_norm,pattern_norm]

def heights (i : ℤ) := Icc (Real.exp ((i:ℝ)-2)) (Real.exp ((i:ℝ)+2))

theorem pattern_support (i k : ℤ) : tsupport (pattern i k) ⊆ heights i := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_cases h : 0 < y
  · have hw : win (Real.log y-(i:ℝ)) ≠ 0 := by
      intro hz; exact hy (by simp [pattern,h,hz])
    obtain ⟨hl,hu⟩ := win_nonzero hw
    rw [← Real.exp_log h]
    exact ⟨Real.exp_le_exp.mpr (by linarith),Real.exp_le_exp.mpr (by linarith)⟩
  · exact False.elim (hy (by simp [pattern,h]))

theorem basis_smooth (k : ℤ) : ContDiff ℝ ∞ (basis k) := by
  simp only [basis,fourier_coe_apply]
  fun_prop

theorem pattern_smooth (i k : ℤ) : ContDiff ℝ ∞ (pattern i k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases h : 0 < y
  · have hj := (Real.contDiffAt_log h.ne').sub (contDiffAt_const (c := (i:ℝ)))
    apply (((Complex.ofRealCLM.contDiff.comp win_smooth).contDiffAt.comp y hj).mul
      ((basis_smooth k).contDiffAt.comp y hj)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with u hu
    exact if_pos hu
  · have hy : y ∉ heights i := fun e => h ((Real.exp_pos _).trans_le e.1)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hy] with u hu
    exact image_eq_zero_of_notMem_tsupport (fun e => hu (pattern_support i k e))

theorem pattern_test (i k : ℤ) :
    Continuous (pattern i k) ∧ HasCompactSupport (pattern i k) ∧
      tsupport (pattern i k) ⊆ Ioi (0:ℝ) :=
  ⟨(pattern_smooth i k).continuous,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (pattern_support i k),
    fun _ h => (Real.exp_pos _).trans_le (pattern_support i k h).1⟩

theorem right_test (j l : ℤ) :
    Continuous (rightPattern j l) ∧ HasCompactSupport (rightPattern j l) ∧
      tsupport (rightPattern j l) ⊆ Ioi (0:ℝ) := by
  obtain ⟨hc,hk,hp⟩ := pattern_test j l
  have ht : tsupport (rightPattern j l) = tsupport (pattern j l) := by
    unfold tsupport; congr 1; ext y; simp [Function.mem_support,rightPattern]
  exact ⟨hc.star,show IsCompact (tsupport (rightPattern j l)) by rw [ht]; exact hk,by rw [ht]; exact hp⟩

theorem product_floor {p0 a b : ℝ} {i j : ℤ}
    (ha : a ∈ heights i) (hb : b ∈ heights j) (hij : p0 < Real.exp ((i:ℝ)+(j:ℝ)+2)) :
    p0*Real.exp (-6) ≤ a*b := by
  calc
    _ ≤ Real.exp ((i:ℝ)+(j:ℝ)+2)*Real.exp (-6) :=
      mul_le_mul_of_nonneg_right hij.le (Real.exp_pos _).le
    _ = Real.exp ((i:ℝ)-2)*Real.exp ((j:ℝ)-2) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1 <;> ring
    _ ≤ a*b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ((Real.exp_pos _).le.trans ha.1)

end
end ImbalancedChen.Part3.PrescribedLogTensorWindows20261112
