import ImbalancedChen.P4BOriginalActualChartCoprimeE1
import ImbalancedChen.TotientReciprocalBudget

/-! SOURCE ONLY / UNCOMPILED. Pair E1 is bounded at each actual q,
before the absolute fixed reciprocal moments are summed. No aggregated
signedError is multiplied by another q-dependent main term. -/
namespace ImbalancedChen.P4BOriginalPairMeanNorm
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)
open P4BOriginalBrunCoprimeE1
open P4BOriginalSameRhoCoprimeE1
open P4BOriginalTwoLongExpandedCore (rho actual_modulus_class)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds)

theorem pair_remainder_norm (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (g1 g2 : Bool)
    (q short : ℕ) (hq : 0<q) :
    ‖pairMean F G U V Z j g1 g2 q short-pairMain F G U V Z j g1 g2 q short‖≤
      (‖mean F U Z j g1 q 1-main F U Z j g1 q 1‖*‖main G V Z j g2 q 1‖+
       ‖main F U Z j g1 q 1‖*‖mean G V Z j g2 q 1-main G V Z j g2 q 1‖+
       ‖mean F U Z j g1 q 1-main F U Z j g1 q 1‖*
         ‖mean G V Z j g2 q 1-main G V Z j g2 q 1‖)/(q.totient:ℝ) := by
  rw [pairMean_E1_remainder F G U V Z j g1 g2 q short hq]
  split_ifs
  · rw [norm_mul,norm_inv,Complex.norm_natCast]
    have hn := (norm_add_le _ _).trans
      (add_le_add_right (norm_add_le _ _) _)
    simp only [norm_mul] at hn
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (Nat.cast_nonneg q.totient))
  · simp only [norm_zero]
    positivity

theorem pair_remainder_actual_E1 (F G : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    (hG : Function.support (G:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (q short : ℕ) (hq : 0<q) :
    let e1 := price F*(q.divisors.card:ℝ)*Z^(2*j+1)
    let e2 := price G*(q.divisors.card:ℝ)*Z^(2*j+1)
    ‖pairMean F G U V Z j g1 g2 q short-pairMain F G U V Z j g1 g2 q short‖≤
      (e1*‖main G V Z j g2 q 1‖+‖main F U Z j g1 q 1‖*e2+e1*e2)/(q.totient:ℝ) := by
  have h1 := actual_E1 F hF hU hZ j g1 q 1 hq
  have h2 := actual_E1 G hG hV hZ j g2 q 1 hq
  have he1 : 0≤price F*(q.divisors.card:ℝ)*Z^(2*j+1) :=
    mul_nonneg (mul_nonneg (price_nonneg F) (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hZ) _)
  have he2 : 0≤price G*(q.divisors.card:ℝ)*Z^(2*j+1) :=
    mul_nonneg (mul_nonneg (price_nonneg G) (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hZ) _)
  apply (pair_remainder_norm F G U V Z j g1 g2 q short hq).trans
  dsimp only
  gcongr

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

/-- The three moment orders needed below are all paid by the existing
fixed fourth moment on the SAME active physical support. -/
theorem actual_tau_moment (p : ℕ) (hp : p≤4)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    (∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^p/(v.totient:ℝ))≤
      (4*(1+Real.log (max 1 (D:ℝ))))^16 := by
  let T := S.filter (fun v => coefficient m r n e q a omega k N L v≠0)
  have heq : (∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^p/(v.totient:ℝ))=
      ∑ v∈T,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^p/(v.totient:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvT
    have hz : coefficient m r n e q a omega k N L v=0 := by
      by_contra h
      exact hvT (Finset.mem_filter.mpr ⟨hv,h⟩)
    simp [rho,hz]
  have hTD : T⊆Finset.Icc 1 D := by
    intro v hv
    obtain ⟨hvS,hvN⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_Icc.mpr ⟨(actual_modulus_class m r n e q a omega k N L (hS hvS)).1,hlevel v hvS hvN⟩
  rw [heq]
  apply (Finset.sum_le_sum (g:=fun v => (v.divisors.card:ℝ)^4/(v.totient:ℝ)) ?_).trans
    (sum_divisor_fourth_moment_le_log T D hTD (fun v hv =>
      (actual_modulus_class m r n e q a omega k N L (hS (Finset.mem_filter.mp hv).1)).2.2.1))
  intro v hv
  obtain ⟨hvpos,_,_,hc⟩ := actual_modulus_class m r n e q a omega k N L (hS (Finset.mem_filter.mp hv).1)
  have hcard : (1:ℝ)≤(v.divisors.card:ℝ) := by
    have H : 0<v.divisors.card := Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hvpos.ne'⟩⟩
    exact_mod_cast Nat.succ_le_of_lt H
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    (by simpa only [one_mul] using pow_le_pow_right₀ hcard hp)

end
end ImbalancedChen.P4BOriginalPairMeanNorm
