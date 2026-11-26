import ImbalancedChen.P4BOriginalBrunCoprimeE1
import ImbalancedChen.TotientReciprocalBudget

/-! SOURCE ONLY / UNCOMPILED. Original declaration bytes are preserved;
see EXTRACTION_BINDING.json. No compilation or kernel credit is added. -/
namespace ImbalancedChen.P4BOriginalSameRhoCoprimeE1
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalBrunCoprimeE1
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial)

def pairMean (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (gap1 gap2 : Bool) (q short : ℕ) : ℂ :=
  (q.totient:ℂ)⁻¹ *
    ∑ u∈wideWindow U,∑ v∈wideWindow V,
      (F ((u:ℝ)/U)*brunPolynomial Z j gap1 u)*
      (G ((v:ℝ)/V)*brunPolynomial Z j gap2 v)*
      (if (short*u*v).Coprime q then (1:ℂ) else 0)

theorem pairMean_factor (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (gap1 gap2 : Bool) (q short : ℕ) :
    pairMean F G U V Z j gap1 gap2 q short=
      if short.Coprime q then (q.totient:ℂ)⁻¹ *
        mean F U Z j gap1 q 1 * mean G V Z j gap2 q 1 else 0 := by
  by_cases hm : short.Coprime q
  · simp only [pairMean,mean,if_pos hm,one_mul,Finset.sum_mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have he : (short*u*v).Coprime q ↔ u.Coprime q ∧ v.Coprime q := by
      simp [Nat.coprime_mul_iff_left,hm]
    by_cases huq : u.Coprime q <;> by_cases hvq : v.Coprime q <;> simp [he,huq,hvq] <;> ring
  · have hz (u v : ℕ) : ¬(short*u*v).Coprime q := by
      intro h
      exact hm (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp h).1).1
    simp [pairMean,hm,hz]

end
end ImbalancedChen.P4BOriginalSameRhoCoprimeE1

namespace ImbalancedChen.P4BOriginalPairMeanNorm
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)
open P4BOriginalBrunCoprimeE1
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds)

def densityLog (x : ℝ) : ℝ := 4*(1+Real.log x)

theorem densityLog_one_le {x : ℝ} (hx : 1≤x) : 1≤densityLog x := by
  have H := Real.log_nonneg hx
  dsimp [densityLog]
  linarith

/-- A conservative fixed-log price for the actual A_q. Its signed
reciprocal coefficient is unchanged. B2 is still used for the gap. -/
theorem density_norm_le_log {Z x : ℝ} (hZ : 1≤Z) (hx : 1≤x)
    (j : ℕ) (gap : Bool) (q short : ℕ) (hy : Z^(2*j+1)≤x) :
    ‖density Z j gap q short‖≤densityLog x := by
  let T := brunSupport Z (2*j+1)
  have hT : T⊆Finset.Icc 1 (Nat.floor x) := by
    intro d hd
    obtain ⟨hp,hb⟩ := brunSupport_bounds hZ _ hd
    exact Finset.mem_Icc.mpr ⟨hp,Nat.le_floor (hb.trans hy)⟩
  have H : ‖density Z j gap q short‖≤∑ d∈T,1/(d.totient:ℝ) := by
    unfold density
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hp,_⟩ := brunSupport_bounds hZ _ hd
    split_ifs
    · rw [norm_div,Complex.norm_natCast]
      calc
        _≤1/(d:ℝ) := div_le_div_of_nonneg_right (coefficient_norm Z j gap d) (Nat.cast_nonneg _)
        _≤1/(d.totient:ℝ) := one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr hp) (by exact_mod_cast Nat.totient_le d)
    · simp only [norm_zero]
      positivity
  have hfloor : (Nat.floor x:ℝ)≤x := Nat.floor_le (zero_le_one.trans hx)
  have hmax : max 1 (Nat.floor x:ℝ)≤x := max_le hx hfloor
  exact H.trans ((sum_reciprocal_totient_subset_le_log T (Nat.floor x) hT).trans (by
    dsimp [densityLog]
    gcongr
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax))

theorem mean_norm_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U Z : ℝ} (hU : 0<U) (hZ : 1≤Z) (j : ℕ) (gap : Bool) (q short : ℕ) (hq : 0<q) :
    ‖mean F U Z j gap q short‖≤
      U*((q.totient:ℝ)/q)*‖mass F‖*‖density Z j gap q short‖+
        price F*(q.divisors.card:ℝ)*Z^(2*j+1) := by
  have H := norm_add_le (mean F U Z j gap q short-main F U Z j gap q short)
    (main F U Z j gap q short)
  rw [sub_add_cancel] at H
  have he := actual_E1 F hF hU hZ j gap q short hq
  have hm : ‖main F U Z j gap q short‖=
      U*((q.totient:ℝ)/q)*‖mass F‖*‖density Z j gap q short‖ := by
    simp only [main,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤U*((q.totient:ℝ)/q)),norm_mul]
    ring
  linarith

end
end ImbalancedChen.P4BOriginalPairMeanNorm
