import ImbalancedChen.Part3ActualPositiveHolomorphicWeights
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! At the original zero Fourier marking the prescribed holomorphic
moments are strictly nonzero in every sufficiently large even weight.
This concerns the actual archimedean transforms of the test. -/
namespace ImbalancedChen.Part3.ActualPositiveHolomorphicNonvanishing20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
open OriginalFullModulusTestJets20261102 ActualPositiveHolomorphicWeights20261112
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly

private def leading (n : ℕ) (q : ℝ) : ℝ := (q/2)^n/(n.factorial:ℝ)

private theorem term_le (n k : ℕ) {q : ℝ} (hq : 0<q) (h : (q/2)^2≤((n:ℝ)+1)/4) :
    ‖generalJTerm (n:ℂ) q k‖ ≤ leading n q*(1/4:ℝ)^k := by
  have x : 0≤q/2 := by linarith
  have d : 0<(n:ℝ)+1 := by positivity
  have fac : (1:ℝ)≤k.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k)
  have H := generalICoeff_norm_le (show -1<(n:ℂ).re by simp) k
  rw [Complex.Gamma_nat_eq_factorial,norm_inv,Complex.norm_natCast,Complex.natCast_re] at H
  rw [generalJTerm,Complex.cpow_natCast,norm_mul,norm_pow,norm_mul,norm_mul,norm_pow,norm_pow,
    norm_neg,norm_one,one_pow,one_mul,Complex.norm_real,Real.norm_of_nonneg x,pow_mul]
  calc
    _ ≤ (q/2)^n*(((n.factorial:ℝ)⁻¹/(((n:ℝ)+1)^k*(k.factorial:ℝ)))*(((n:ℝ)+1)/4)^k) := by
      gcongr
    _ = leading n q*(1/4:ℝ)^k/(k.factorial:ℝ) := by
      rw [leading,div_pow]
      field_simp [d.ne',Nat.factorial_ne_zero] <;> ring
    _ ≤ _ := div_le_self (by dsimp [leading]; positivity) fac

theorem intJ_re_pos (n : ℕ) {q : ℝ} (hq : 0<q) (h : (q/2)^2≤((n:ℝ)+1)/4) : 0<(intJ n q).re := by
  let f := generalJTerm (n:ℂ) q
  have z : f 0=(leading n q:ℂ) := by
    dsimp [f,leading,generalJTerm,generalICoeff]
    simp only [Complex.cpow_natCast,Nat.factorial_zero,Nat.cast_one,one_mul,pow_zero,mul_zero,
      Nat.cast_zero,zero_add,Complex.Gamma_nat_eq_factorial,mul_one,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_natCast,div_eq_mul_inv]
  have hs := generalJ_hasSum (show -1<(n:ℂ).re by simp) q
  have S : Summable (fun k => ‖f (k+1)‖) := (summable_nat_add_iff 1).mpr (summable_norm_generalJ (by simp) q)
  have G := summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)
  have E := hs.summable.sum_add_tsum_nat_add 1
  change (∑ k∈Finset.range 1,f k)+(∑' k : ℕ,f (k+1))=∑' k,f k at E
  rw [Finset.sum_range_one,z,hs.tsum_eq] at E
  have U : ‖∑' k : ℕ,f (k+1)‖≤leading n q/3 := by
    apply (norm_tsum_le_tsum_norm S).trans
    calc
      _ ≤ ∑' k : ℕ,(leading n q/4)*(1/4:ℝ)^k := S.tsum_le_tsum
        (fun k => by simpa only [pow_succ,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm,one_mul]
          using term_le n (k+1) hq h) (G.mul_left _)
      _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)]; ring
  have Re := congrArg Complex.re E
  simp only [Complex.add_re,Complex.ofReal_re] at Re
  have pos : 0<leading n q := by dsimp [leading]; positivity
  change 0<(generalJ (n:ℂ) q).re
  have lower := (abs_le.mp ((Complex.abs_re_le_norm (∑' k : ℕ,f (k+1))).trans U)).1
  linarith only [lower,Re,pos]

private theorem zero_test (Y q : ℝ) : spectralTest (0:D4 → ℤ) Y q=(chi (q/Y):ℂ) := by
  simp [spectralTest,spectralMode,e]

theorem prescribed_holomorphic_nonzero {Y : ℝ} (hY : 0<Y) (j : ℕ)
    (h : (8*Y)^2≤((2*j+1:ℕ):ℝ)/4+1/4) :
    holWeight j (spectralTest (0:D4 → ℤ) Y)≠0 := by
  let n := 2*j+1
  let Φ := spectralTest (0:D4 → ℤ) Y
  let F := fun q : ℝ => intJ n q*Φ q/(q:ℂ)
  have H := moment_L1 n (0:D4 → ℤ) hY
  have reF (q : ℝ) : (F q).re=(intJ n q).re*chi (q/Y)/q := by
    dsimp [F,Φ]; rw [zero_test]
    simp only [Complex.div_ofReal_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have on (q : ℝ) (hq : 0<q) (hi : Φ q≠0) : 0<(intJ n q).re := by
    have B := (spectralTest_tsupport_strict 0 hY (subset_tsupport _ hi)).2.le
    apply intJ_re_pos n hq
    have m : (q/2)^2≤(8*Y)^2 := by gcongr <;> linarith
    dsimp only [n]
    linarith only [m,h]
  have nn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun q => (F q).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    by_cases z : Φ q=0
    · simp [F,z]
    · rw [reF]; exact div_nonneg (mul_nonneg (on q hq z).le (chiBump.nonneg' _)) hq.le
  have subset : Ioo Y (2*Y) ⊆ Function.support (fun q => (F q).re) ∩ Ioi 0 := by
    intro q hq
    have p : 0<q := hY.trans hq.1
    have c : chi (q/Y)=1 := chi_eq_one ⟨(le_div_iff₀ hY).mpr (by linarith [hq.1]),(div_le_iff₀ hY).mpr (by linarith [hq.2])⟩
    have nz : Φ q≠0 := by dsimp [Φ]; rw [zero_test,c]; norm_num
    exact ⟨by change (F q).re≠0; rw [reF,c,mul_one]; exact (div_pos (on q p nz) p).ne',p⟩
  have hpos : 0<volume ((Ioo Y (2*Y)):Set ℝ) := IsOpen.measure_pos volume isOpen_Ioo
    (Set.nonempty_Ioo.mpr (by linarith))
  have integral_pos := (setIntegral_pos_iff_support_of_nonneg_ae nn (Complex.reCLM.integrable_comp H)).mpr (hpos.trans_le (measure_mono subset))
  change 4*I^(2*(j+1))*moment n Φ≠0
  apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ Complex.I_ne_zero))
  intro z
  have E := integral_re (𝕜:=ℂ) H
  change (∫ q in Ioi (0:ℝ),(F q).re)=(moment n Φ).re at E
  rw [z,Complex.zero_re] at E
  linarith only [integral_pos,E]

end
end ImbalancedChen.Part3.ActualPositiveHolomorphicNonvanishing20261112

