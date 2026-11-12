import ImbalancedChen.Part3ActualPositiveHolomorphicWeights
import ImbalancedChen.Part3ActualImaginaryKTwoWaveAsymptotic
import ImbalancedChen.Part3ActualImaginaryKIConnection
import Batteries.Tactic.OpenPrivate

/-! The two genuine K functions in a scalar packet with small heights.
The real spectral bound is uniform all the way down to argument zero. -/
namespace ImbalancedChen.Part3.ActualPositiveSmallHeightKBound20261112

noncomputable section
open Set Filter Complex
open scoped Topology
open ActualPositiveHolomorphicWeights20261112 GeneralComplexISeriesSourceOnly
open GeneralIConjugation20261025a ImaginaryKWaveCoefficients20261025a
open ActualImaginaryKIConnectionSourceOnly ComplexOrderKBridgeSourceOnly
open ImaginaryGammaNormalization20261025a
open private expMass_summable from ImbalancedChen.Part3ActualPositiveHolomorphicWeights

private theorem I_bound (t : ℝ) {q B : ℝ} (hq : 0<q) (hb : q≤B) :
    ‖generalI ((t:ℂ)*I) q‖≤‖(Gamma ((t:ℂ)*I+1))⁻¹‖*expMass B := by
  let ν := (t:ℂ)*I
  have r : ν.re=0 := by simp [ν]
  have hv : -1<ν.re := by rw [r]; norm_num
  have hp : ‖(((q/2:ℝ):ℂ)^ν)‖=1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<q/2),r,Real.rpow_zero]
  have S := summable_norm_generalI hv q
  rw [← (generalI_hasSum hv q).tsum_eq,expMass,← tsum_mul_left]
  apply (norm_tsum_le_tsum_norm S).trans
  apply S.tsum_le_tsum _ ((expMass_summable B).mul_left _)
  intro k
  have U := generalICoeff_norm_le hv k
  rw [r,zero_add,one_pow,one_mul] at U
  simp only [norm_mul,norm_pow,hp,one_mul,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤q/2)]
  calc
    _ ≤ (‖(Gamma (ν+1))⁻¹‖/(k.factorial:ℝ))*((B/2)^2)^k := by gcongr <;> linarith
    _ = _ := by rw [pow_mul]; ring

theorem K_bound (t : ℝ) (ht : t≠0) {q B : ℝ} (hq : 0<q) (hb : q≤B) :
    ‖complexOrderK ((t:ℂ)*I) q‖≤‖Gamma ((t:ℂ)*I)‖*expMass B := by
  let ν := (t:ℂ)*I
  let c := connectionCoefficient t
  rw [complexOrderK_imaginary_eq_generalI_sub t ht hq,generalI_neg_imaginary_eq_conj t hq,norm_mul]
  change ‖c‖*‖conj (generalI ν q)-generalI ν q‖≤_
  have h := norm_sub_le (conj (generalI ν q)) (generalI ν q)
  rw [Complex.norm_conj] at h
  have G := congrArg norm (neg_connectionCoefficient_mul_gamma_plus_inv t)
  rw [norm_mul,norm_neg,norm_div] at G
  have conjG : Gamma (-ν)=conj (Gamma ν) := by rw [← Complex.Gamma_conj]; congr 1; simp [ν]
  rw [show Gamma (-((t:ℂ)*I))=conj (Gamma ν) from conjG,Complex.norm_conj] at G
  norm_num only [Complex.norm_ofNat] at G
  calc
    _ ≤ ‖c‖*(2*(‖(Gamma (ν+1))⁻¹‖*expMass B)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith only [h,I_bound t hq hb]
    _ = _ := by dsimp only [c]; linear_combination 2*expMass B*G

private theorem coth_large {x : ℝ} (hx : Real.pi≤x) :
    Real.cosh x≤(1+(Real.sinh Real.pi)⁻¹)*Real.sinh x := by
  have s := Real.sinh_strictMono.monotone hx
  have p : 0<Real.sinh Real.pi := Real.sinh_pos.mpr Real.pi_pos
  have m : (1:ℝ)≤(Real.sinh Real.pi)⁻¹*Real.sinh x := by
    simpa only [inv_mul_cancel₀ p.ne'] using mul_le_mul_of_nonneg_left s (inv_nonneg.mpr p.le)
  have e : Real.exp (-x)≤1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have d : Real.cosh x-Real.sinh x=Real.exp (-x) := by rw [Real.cosh_eq,Real.sinh_eq]; ring
  linarith only [m,d,e]

/-- Both height arguments run over (0,B] with the actual native
spectral measure in mind. The sole order-height loss is 1/|t|. -/
theorem regular_small_product (B : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ t : ℝ,1≤|t| → ∀ a∈Ioc (0:ℝ) B,∀ b∈Ioc (0:ℝ) B,
      Real.cosh (Real.pi*t)*‖complexOrderK ((t:ℂ)*I) a*complexOrderK ((t:ℂ)*I) b‖≤C/|t| := by
  let c := Real.pi*(1+(Real.sinh Real.pi)⁻¹)*expMass B^2
  have hn : 0≤c := by dsimp [c]; positivity
  refine ⟨c,hn,fun t ht a ha b hb => ?_⟩
  have nt : t≠0 := abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
  have gamma := norm_gamma_mul_I_sq t nt
  have pp : |Real.pi*t|=Real.pi*|t| := by rw [abs_mul,abs_of_pos Real.pi_pos]
  have ts : t*Real.sinh (Real.pi*t)=|t|*Real.sinh (Real.pi*|t|) := by
    rcases le_or_gt 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,mul_neg,Real.sinh_neg]; ring
  have cc : Real.cosh (Real.pi*t)=Real.cosh (Real.pi*|t|) := by rw [← pp,Real.cosh_abs]
  have hh : Real.pi≤Real.pi*|t| := by simpa using mul_le_mul_of_nonneg_left ht Real.pi_pos.le
  have gt : 0<Real.sinh (Real.pi*|t|) := Real.sinh_pos.mpr (mul_pos Real.pi_pos (abs_pos.mpr nt))
  have g := mul_le_mul (K_bound t nt ha.1 ha.2) (K_bound t nt hb.1 hb.2)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (expMass_nonneg _))
  rw [norm_mul,cc]
  apply (mul_le_mul_of_nonneg_left g (Real.cosh_pos _).le).trans
  rw [show (‖Gamma ((t:ℂ)*I)‖*expMass B)*(‖Gamma ((t:ℂ)*I)‖*expMass B)=‖Gamma ((t:ℂ)*I)‖^2*expMass B^2 by ring,gamma,ts]
  calc
    _ ≤ ((1+(Real.sinh Real.pi)⁻¹)*Real.sinh (Real.pi*|t|))*
        (Real.pi/(|t|*Real.sinh (Real.pi*|t|))*expMass B^2) := by gcongr; exact coth_large hh
    _ = c/|t| := by dsimp [c]; field_simp [gt.ne',(abs_pos.mpr nt).ne'] <;> ring

end
end ImbalancedChen.Part3.ActualPositiveSmallHeightKBound20261112

