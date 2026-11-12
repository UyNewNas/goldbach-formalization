import ImbalancedChen.Part3ActualCompletedCurveMeans
import ImbalancedChen.Part3ActualEisensteinOrdinaryGrowth
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Batteries.Tactic.OpenPrivate

/-! Uniform vertical-strip bounds on the *completed* functions that enter
the native cusp expansion. The conductor-one constant really contains
both completed zetas; the proof uses the Mellin integral of Mathlib's
modified theta kernel, including its two explicit polar corrections. -/
namespace ImbalancedChen.Part3.ActualCompletedHorizontalBand20261112

noncomputable section
open Complex Set MeasureTheory UpperHalfPlane
open scoped BigOperators UpperHalfPlane Classical
open ActualCompletedCurveMeans20261110 ActualCharacterCriticalFamily20261110
open ActualYoungCriticalD20261110 ActualOrdinaryContinuousModes20261110
open ActualEisensteinOrdinaryGrowth20261110
open CompletedActualEisensteinIdentity20261025a CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open private envelope envelope_summable term_bound from ImbalancedChen.Part3ActualCompletedCurveMeans

private theorem theta_mellin_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 → ‖completedRiemannZeta₀ w‖ ≤ B := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let f := P.f_modif
  let W (s : ℂ) (y : ℝ) := (y : ℂ)^(s-1) • f y
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have HI (s : ℂ) : Integrable (W s) μ := (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  let B := ∫ y, ‖W 0 y‖ + ‖W 2 y‖ ∂μ
  have hB : 0 ≤ B := integral_nonneg (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨B,hB,?_⟩
  intro w h₀ h₃
  let v := w/2
  have V : 0 ≤ v.re ∧ v.re ≤ 2 := by
    dsimp [v]
    simp only [Complex.div_ofNat_re]
    constructor <;> linarith
  have H : ∀ᵐ y ∂μ, ‖W v y‖ ≤ ‖W 0 y‖+‖W 2 y‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change 0 < y at hy
    have Hpow (s : ℂ) : ‖W s y‖ = y^(s.re-1)*‖f y‖ := by
      simp [W,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
    rw [Hpow,Hpow,Hpow]
    rcases le_total y 1 with h | h
    · have hh := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hy h
          (by simp; linarith [V.1] : (0 : ℂ).re-1 ≤ v.re-1)) (norm_nonneg (f y))
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hy.le _) (norm_nonneg _)))
    · have hh := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h
          (by norm_num; linarith [V.2] : v.re-1 ≤ (2 : ℂ).re-1)) (norm_nonneg (f y))
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hy.le _) (norm_nonneg _)))
  have Hm : ‖∫ y, W v y ∂μ‖ ≤ B :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_ae (HI v).norm ((HI 0).norm.add (HI 2).norm) H)
  change ‖(∫ y, W v y ∂μ)/(2 : ℂ)‖ ≤ B
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans Hm

/-- The strip used by the two *actual* constant waves has real part in
[0,3]. Only the horizontal edges, of imaginary part at least one, are
needed here. -/
theorem completed_zeta_band :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 → 1 ≤ |w.im| → ‖completedRiemannZeta w‖ ≤ B := by
  obtain ⟨D,hD,H⟩ := theta_mellin_bound
  refine ⟨D+2,by linarith,?_⟩
  intro w h₀ h₃ hi
  have a := hi.trans (Complex.abs_im_le_norm w)
  have b : 1 ≤ ‖1-w‖ := hi.trans (by simpa using Complex.abs_im_le_norm (1-w))
  have U (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖1/z‖ ≤ 1 := by
    rw [norm_div,norm_one]
    exact (div_le_iff₀ (zero_lt_one.trans_le hz)).mpr (by simpa using hz)
  rw [completedRiemannZeta_eq]
  calc
    _ ≤ (‖completedRiemannZeta₀ w‖+‖1/w‖)+‖1/(1-w)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ D+2 := by linarith [H w h₀ h₃,U w a,U (1-w) b]

private theorem height_power_band {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, ∀ w : ℂ, -2 ≤ w.re → w.re ≤ 2 → ‖(y : ℂ)^w‖ ≤ B := by
  let K := Icc a b ×ˢ Icc (-2 : ℝ) 2
  let F (p : ℝ × ℝ) := Real.exp (Real.log p.1*p.2)
  have C : ContinuousOn F K := by
    intro p hp
    have hy := ha.trans_le hp.1.1
    exact (((Real.continuousAt_log hy.ne').comp continuousAt_fst).mul continuousAt_snd).rexp.continuousWithinAt
  obtain ⟨B,H⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn C
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro y hy w h₁ h₂
  have hp := ha.trans_le hy.1
  have J := H (y,w.re) ⟨hy,⟨h₁,h₂⟩⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp,Real.rpow_def_of_pos hp]
  have J' : Real.exp (Real.log y*w.re) ≤ B := by
    simpa [F,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using J
  exact J'.trans (le_max_left _ _)

theorem completed_principal_band {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
    ∀ z : ℍ, z.im ∈ Icc a b → ‖completedActualEisenstein s z‖ ≤ B := by
  obtain ⟨D,hD,Z⟩ := completed_zeta_band
  obtain ⟨P,hP,W⟩ := height_power_band (b := b) ha
  let U := fun n : ℕ => 2*majorant 2 a n
  let B := ∑' n, U n
  have S : Summable U := (majorant_summable 2 ha).const_mul 2
  have hB : 0 ≤ B := tsum_nonneg (fun n =>
    (norm_nonneg (nonzeroFrequencyPair n (0 : ℂ) a 0)).trans
      (nonzeroFrequencyPair_norm_bound 2 ha n (by norm_num) le_rfl 0))
  refine ⟨D*P+D*P+2*Real.sqrt b*B,by positivity,?_⟩
  intro s hl hr hi z hz
  have hne : s ≠ 1/2 := by intro e; norm_num [e] at hi
  have H₁ := Z (2*s) (by simp [Complex.mul_re]; linarith) (by simp [Complex.mul_re]; linarith)
    (by simp [Complex.mul_im,abs_mul]; linarith)
  have H₂ := Z (2*s-1) (by simp [Complex.mul_re]; linarith) (by simp [Complex.mul_re]; linarith)
    (by simp [Complex.mul_im,abs_mul]; linarith)
  have V := W _ hz s (by linarith) (by linarith)
  have V' := W _ hz (1-s) (by simp; linarith) (by simp; linarith)
  have hb : ‖∑' n : ℕ, nonzeroFrequencyPair n s z.im z.re‖ ≤ B :=
    tsum_of_norm_bounded S.hasSum (fun n => nonzeroFrequencyPair_norm_bound 2 ha n
      (abs_le.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩) hz.1 z.re)
  have hfac : ‖(2 : ℂ)*(Real.sqrt z.im : ℂ)‖ ≤ 2*Real.sqrt b := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    exact hz.2
  rw [completedActualEisenstein,completedEisensteinFourier_eq_raw _ _ _ hne]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul H₁ V (norm_nonneg _) hD) (mul_le_mul H₂ V' (norm_nonneg _) hD)
  · rw [norm_mul]
    exact mul_le_mul hfac hb (norm_nonneg _) (by positivity)

theorem completed_character_band {q : ℕ} (χ : DirichletCharacter ℂ q) {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 →
    ∀ z : ℍ, z.im ∈ Icc a b → ‖completedFamily χ s z‖ ≤ B := by
  let B := ∑' n : ℤ, envelope 2 a b n
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro s hl hr z hz
  apply le_trans _ (le_max_left B 0)
  exact tsum_of_norm_bounded (envelope_summable 2 ha b).hasSum
    (fun n => term_bound χ n (M := 2) (abs_le.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩) ha z hz)

/-- Both branches are estimated on the same positive height band,
uniformly in the original vertical parameter and horizontal coordinate. -/
theorem ordinary_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
    ∀ z : ℍ, z.im ∈ Icc a b →
    (s.re-1/2)*‖ordinary χ s z‖ ≤ C*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨D,hD,F⟩ := original_ordinary_factors χ
  obtain ⟨A,hA,G⟩ := completed_principal_band (b := b) ha
  obtain ⟨B,hB,H⟩ := completed_character_band χ (b := b) ha
  refine ⟨D*max A B,mul_nonneg hD (hA.trans (le_max_left _ _)),?_⟩
  intro s hl hr hi z hz
  by_cases e : q=1
  · simp only [ordinary,if_pos e]
    change (s.re-1/2)*‖principalFactor s*completedActualEisenstein s z‖ ≤ _
    rw [norm_mul,← mul_assoc]
    have T := mul_le_mul (F s hl hr hi).2 ((G s hl.le hr hi z hz).trans (le_max_left A B))
      (norm_nonneg _) (mul_nonneg hD (Real.exp_pos _).le)
    exact T.trans_eq (by ring)
  · simp only [ordinary,if_neg e]
    change (s.re-1/2)*‖uncompletionFactor χ s*completedFamily χ s z‖ ≤ _
    rw [norm_mul,← mul_assoc]
    have T := mul_le_mul (F s hl hr hi).1 ((H s hl.le hr z hz).trans (le_max_right A B))
      (norm_nonneg _) (mul_nonneg hD (Real.exp_pos _).le)
    exact T.trans_eq (by ring)

end
end ImbalancedChen.Part3.ActualCompletedHorizontalBand20261112
