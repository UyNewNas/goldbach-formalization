import ImbalancedChen.Part3TwoLongNaturalPeriodization
import ImbalancedChen.Part3TwoLongInternalP2Modes
import ImbalancedChen.Part3TwoLongNaturalInternalP2
import ImbalancedChen.Part3TwoLongLiteralBrunSubstitution
import ImbalancedChen.P5OriginalPrimitiveCoprimeDensity

/-! SOURCE ONLY / UNCOMPILED. The missing fixed-divisor smooth E1
primitive, from existing exact Poisson and actual Fourier decay.
The integral and weight are literal. N2 is a proved uniform error price;
no E1, progression, mean-gap, Weil or distribution bound is an input.
All q>0 and all short multipliers are retained, including nonunits. -/
namespace ImbalancedChen.P4BOriginalCoprimeSmoothE1
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
open Part3.TwoLongLiteralMellinModes (N2 wideWindow)
open Part3.TwoLongNaturalPeriodization
open Part3.TwoLongActualDoublePeriodization
open Part3.TwoLongNaturalInternalP2 (compact_of_window)
open Part3.TwoLongInternalP2Modes (N2_nonneg)
open Part3.TwoLongN2FourierDecay (fourierDecayConstant fourierDecayConstant_pos norm_fourier_le_N2)
open Part3.CommonSmoothCutoff (poissonNonzeroDecay poissonNonzeroDecay_summable_tsum_le)
open Part3.TwoLongLiteralBrunSubstitution (divisorIndicator sum_divisor_substitution)
open OriginalPrimitiveCoprimeDensity (muR muR_abs_le_one coprime_indicator_moebius reciprocal_moebius_totient)

def mass (F : ℝ→ℂ) : ℂ := ∫ x : ℝ,F x
def price (F : 𝓢(ℝ,ℂ)) : ℝ := 2*fourierDecayConstant*N2 (F : ℝ→ℂ)

theorem price_nonneg (F : 𝓢(ℝ,ℂ)) : 0≤price F := by
  exact mul_nonneg (mul_nonneg (by norm_num) fourierDecayConstant_pos.le) (N2_nonneg _)

theorem fourier_at_zero (F : 𝓢(ℝ,ℂ)) : (𝓕 F) 0=mass F := by
  rw [SchwartzMap.fourier_coe,Real.fourier_real_eq]
  simp [mass]

def nonzeroMode (F : 𝓢(ℝ,ℂ)) (U D b : ℝ) (h : ℤ) : ℂ :=
  if h=0 then 0 else poissonMode F U D b h

theorem poisson_E1 (F : 𝓢(ℝ,ℂ)) (hF : HasCompactSupport (F : ℝ→ℂ))
    {U D : ℝ} (hU : 0<U) (hD : 0<D) (b : ℝ) :
    ‖progressionPeriodization F U D b-(U/D) • mass F‖≤price F := by
  let C := fourierDecayConstant*N2 (F : ℝ→ℂ)
  have hC : 0≤C := mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _)
  have ht : 0<U/D := div_pos hU hD
  obtain ⟨hmajor,hsum⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) : ‖nonzeroMode F U D b h‖≤C*poissonNonzeroDecay (U/D) h := by
    by_cases hh : h=0
    · simp [nonzeroMode,poissonNonzeroDecay,hh]
    · simp only [nonzeroMode,poissonNonzeroDecay,if_neg hh,poissonMode,
        norm_mul,norm_smul,Real.norm_eq_abs,abs_of_pos ht,fourier_apply,Circle.norm_coe,mul_one]
      calc
        _≤(U/D)*(fourierDecayConstant*N2 (F : ℝ→ℂ)/(1+|(U/D)*(h:ℝ)|)^2) :=
          mul_le_mul_of_nonneg_left (norm_fourier_le_N2 F _) ht.le
        _=_ := by dsimp [C]; ring
  have hnorm : Summable (fun h : ℤ => ‖nonzeroMode F U D b h‖) :=
    (hmajor.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hupdate : Summable (Function.update (poissonMode F U D b) 0 0) := by
    apply hnorm.of_norm.congr
    intro h
    by_cases hh : h=0 <;> simp [nonzeroMode,hh]
  have hsplit := Summable.tsum_eq_add_tsum_ite' (f:=poissonMode F U D b) 0 hupdate
  have hidentity : progressionPeriodization F U D b-(U/D) • mass F=
      ∑' h : ℤ,nonzeroMode F U D b h := by
    rw [affine_periodization_poisson F hF hU hD,hsplit]
    simp only [poissonMode,Int.cast_zero,mul_zero,fourier_zero,mul_one,
      fourier_at_zero,add_sub_cancel_left,nonzeroMode]
  rw [hidentity]
  calc
    _≤∑' h : ℤ,C*poissonNonzeroDecay (U/D) h :=
      tsum_of_norm_bounded (hmajor.mul_left C).hasSum hpoint
    _=C*∑' h : ℤ,poissonNonzeroDecay (U/D) h := tsum_mul_left
    _≤C*2 := mul_le_mul_of_nonneg_left hsum hC
    _=price F := by dsimp [C,price]; ring

theorem natural_progression_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U : ℝ} (hU : 0<U) (d : ℕ) (hd : 0<d) (b : ℤ) :
    ‖(∑ n∈wideWindow U,if Int.ModEq d (n:ℤ) b then F ((n:ℝ)/U) else 0)-
      (U/d) • mass F‖≤price F := by
  rw [natural_progression_eq_periodization F hF hU hd b]
  exact poisson_E1 F (compact_of_window F hF) hU (by exact_mod_cast hd) b

theorem multiples_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U : ℝ} (hU : 0<U) (d : ℕ) (hd : 0<d) :
    ‖(∑ n∈wideWindow U,if d∣n then F ((n:ℝ)/U) else 0)-(U/d) • mass F‖≤price F := by
  simpa only [Int.modEq_zero_iff_dvd,Int.natCast_dvd_natCast] using
    natural_progression_E1 F hF hU d hd 0

def coprimeSum (F : ℝ→ℂ) (U : ℝ) (q : ℕ) : ℂ :=
  ∑ n∈wideWindow U,if n.Coprime q then F ((n:ℝ)/U) else 0

theorem complex_coprime_sum (I : Finset ℕ) (f : ℕ→ℂ) {q : ℕ} (hq : 0<q) :
    (∑ n∈I,if n.Coprime q then f n else 0)=
      ∑ d∈q.divisors,(muR d:ℂ)*(∑ n∈I,if d∣n then f n else 0) := by
  have hi (n : ℕ) : (if n.Coprime q then (1:ℂ) else 0)=
      ∑ d∈q.divisors,if d∣n then (muR d:ℂ) else 0 := by
    have H : (if q.Coprime n then (1:ℂ) else 0)=
        ∑ d∈q.divisors,if d∣n then (muR d:ℂ) else 0 := by
      exact_mod_cast coprime_indicator_moebius q n hq
    simpa only [Nat.coprime_comm] using H
  calc
    _=∑ n∈I,(∑ d∈q.divisors,if d∣n then (muR d:ℂ) else 0)*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [←hi]
      split_ifs <;> simp
    _=_ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp

/-- Exact phi(q)/q density, uniform for all q>0, including q=1 and q=2.
The actual Möbius source supplies the density; no Euler approximation. -/
theorem coprime_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U : ℝ} (hU : 0<U) (q : ℕ) (hq : 0<q) :
    ‖coprimeSum F U q-(U*((q.totient:ℝ)/q)) • mass F‖≤price F*q.divisors.card := by
  have hdensity : (∑ d∈q.divisors,(muR d:ℂ)/(d:ℂ))=(q.totient:ℂ)/q := by
    exact_mod_cast reciprocal_moebius_totient q hq
  have heq : coprimeSum F U q-(U*((q.totient:ℝ)/q)) • mass F=
      ∑ d∈q.divisors,(muR d:ℂ)*
        ((∑ n∈wideWindow U,if d∣n then F ((n:ℝ)/U) else 0)-(U/d) • mass F) := by
    rw [coprimeSum,complex_coprime_sum _ _ hq]
    simp only [smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast]
    rw [←hdensity,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq]
  calc
    _≤∑ d∈q.divisors,‖(muR d:ℂ)*
        ((∑ n∈wideWindow U,if d∣n then F ((n:ℝ)/U) else 0)-(U/d) • mass F)‖ := norm_sum_le _ _
    _≤∑ _d∈q.divisors,price F := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul (muR_abs_le_one d)
        (multiples_E1 F hF hU d (Nat.pos_of_mem_divisors hd)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _=price F*q.divisors.card := by simp [mul_comm]

def divisorMean (F : ℝ→ℂ) (U : ℝ) (q m d : ℕ) : ℂ :=
  ∑ n∈wideWindow U,F ((n:ℝ)/U)*divisorIndicator d n*
    (if (m*n).Coprime q then (1:ℂ) else 0)

theorem divisorMean_reindex (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U : ℝ} (hU : 0<U) (q m d : ℕ) (hd : 0<d) :
    divisorMean F U q m d=if (m*d).Coprime q then coprimeSum F (U/d) q else 0 := by
  rw [divisorMean,sum_divisor_substitution hU hd F hF]
  by_cases hmd : (m*d).Coprime q
  · simp only [if_pos hmd,coprimeSum]
    apply Finset.sum_congr rfl
    intro n hn
    have H : (m*(d*n)).Coprime q ↔ n.Coprime q := by
      rw [←mul_assoc,Nat.coprime_mul_iff_left]
      simp [hmd]
    by_cases hnq : n.Coprime q <;> simp [H,hnq]
  · rw [if_neg hmd]
    apply Finset.sum_eq_zero
    intro n hn
    have H : ¬(m*(d*n)).Coprime q := by
      rw [←mul_assoc]
      exact fun h => hmd (Nat.coprime_mul_iff_left.mp h).1
    simp [H]

/-- Nonunit inserted divisors delete their entire true mean. The modulus
remains q and the short multiplier becomes m*d only inside coprimality. -/
theorem divisor_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U : ℝ} (hU : 0<U) (q m d : ℕ) (hq : 0<q) (hd : 0<d) :
    ‖divisorMean F U q m d-
      (if (m*d).Coprime q then ((U/d)*((q.totient:ℝ)/q)) • mass F else 0)‖≤
      if (m*d).Coprime q then price F*q.divisors.card else 0 := by
  rw [divisorMean_reindex F hF hU q m d hd]
  split_ifs with hmd
  · exact coprime_E1 F hF (div_pos hU (by exact_mod_cast hd)) q hq
  · simp

end
end ImbalancedChen.P4BOriginalCoprimeSmoothE1
