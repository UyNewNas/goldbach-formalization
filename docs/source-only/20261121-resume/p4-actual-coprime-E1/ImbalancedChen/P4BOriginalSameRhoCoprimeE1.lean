import ImbalancedChen.P4BOriginalBrunCoprimeE1
import ImbalancedChen.P4BOriginalTwoLongExpandedCore
import ImbalancedChen.P4BOriginalTwoLongActualScales

/-! SOURCE ONLY / UNCOMPILED. Same final Q/rho normalized E1 error.
The true mean keeps every nonunit short-product gate. N-coprimality is
not an E1 assumption: the generic mean theorem holds for every q>0.
Only membership in the original Q supplies positivity/squarefreeness for
the final reciprocal moment. The pair identity displays UV*phi(q)/q^2
and its exact 1/phi(q) mean, without asserting E3 or rough restoration. -/
namespace ImbalancedChen.P4BOriginalSameRhoCoprimeE1
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)
open P4BOriginalBrunCoprimeE1
open P4BOriginalTwoLongExpandedCore (rho actual_modulus_class)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial)
open Part3.TwoLongTransitionMellinN2

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

def pairMain (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (gap1 gap2 : Bool) (q short : ℕ) : ℂ :=
  if short.Coprime q then
    (U*V*(q.totient:ℝ)/(q:ℝ)^2) •
      (mass F*mass G*density Z j gap1 q 1*density Z j gap2 q 1) else 0

theorem pairMain_exact (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (gap1 gap2 : Bool)
    (q short : ℕ) (hq : 0<q) :
    pairMain F G U V Z j gap1 gap2 q short=
      if short.Coprime q then (q.totient:ℂ)⁻¹ *
        main F U Z j gap1 q 1 * main G V Z j gap2 q 1 else 0 := by
  have hphi : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hqC : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  by_cases hm : short.Coprime q
  · simp only [pairMain,main,if_pos hm,smul_eq_mul,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
    field_simp [hphi,hqC]
    ring
  · simp [pairMain,hm]

/-- Algebraic E1 expansion only. In particular this does not remove the
twice-mean term required by E3 or identify rough and upper polynomials. -/
theorem pairMean_E1_remainder (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (gap1 gap2 : Bool)
    (q short : ℕ) (hq : 0<q) :
    pairMean F G U V Z j gap1 gap2 q short-pairMain F G U V Z j gap1 gap2 q short=
      if short.Coprime q then (q.totient:ℂ)⁻¹ *
        ((mean F U Z j gap1 q 1-main F U Z j gap1 q 1)*main G V Z j gap2 q 1+
          main F U Z j gap1 q 1*(mean G V Z j gap2 q 1-main G V Z j gap2 q 1)+
          (mean F U Z j gap1 q 1-main F U Z j gap1 q 1)*
            (mean G V Z j gap2 q 1-main G V Z j gap2 q 1)) else 0 := by
  rw [pairMean_factor,pairMain_exact F G U V Z j gap1 gap2 q short hq]
  split_ifs <;> ring

def signedError (F : ℝ→ℂ) (U Z : ℝ) (j : ℕ) (gap : Bool) (short : ℕ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ v∈S,rho m r n e q a omega k N L v *
    ((mean F U Z j gap v short-main F U Z j gap v short)/(v.totient:ℂ))

/-- The gcd(N,v) branch is discharged from the true physical support,
not assumed for arbitrary moduli. Generic E1 above needs no target gate. -/
theorem nonprimitive_target_modulus_absent (omega : ℝ) (N v : ℕ)
    (h : ¬N.Coprime v) : v∉Q omega N := by
  intro hv
  exact h (P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hv).symm

/-- Exact original support and coefficient pay the fixed reciprocal
tau moment. Inactive moduli beyond D contribute zero. -/
theorem actual_reciprocal_moment (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N D : ℕ) (L : ℝ) (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    (∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)/(v.totient:ℝ))≤
      (4*(1+Real.log (max 1 (D:ℝ))))^16 := by
  let T := S.filter (fun v => coefficient m r n e q a omega k N L v≠0)
  have heq : (∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)/(v.totient:ℝ))=
      ∑ v∈T,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)/(v.totient:ℝ) := by
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
    exact Finset.mem_Icc.mpr ⟨(actual_modulus_class m r n e q a omega k N L (hS hvS)).1,
      hlevel v hvS hvN⟩
  rw [heq]
  apply (Finset.sum_le_sum (g:=fun v => (v.divisors.card:ℝ)^4/(v.totient:ℝ)) ?_).trans
    (sum_divisor_fourth_moment_le_log T D hTD (fun v hv =>
      (actual_modulus_class m r n e q a omega k N L (hS (Finset.mem_filter.mp hv).1)).2.2.1))
  intro v hv
  obtain ⟨hvpos,_,_,hc⟩ := actual_modulus_class m r n e q a omega k N L
    (hS (Finset.mem_filter.mp hv).1)
  have hcard : (1:ℝ)≤(v.divisors.card:ℝ) := by
    have H : 0<v.divisors.card :=
      Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hvpos.ne'⟩⟩
    exact_mod_cast (Nat.succ_le_of_lt H)
  have hp : (v.divisors.card:ℝ)≤(v.divisors.card:ℝ)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hcard (by norm_num : (1:ℕ)≤4)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans
    (by simpa only [one_mul] using hp)

theorem same_rho_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U Z : ℝ} (hU : 0<U) (hZ : 1≤Z) (j : ℕ) (gap : Bool) (short : ℕ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    ‖signedError F U Z j gap short m r n e q a omega k N L S‖≤
      price F*Z^(2*j+1)*(4*(1+Real.log (max 1 (D:ℝ))))^16 := by
  have hcost : 0≤price F*Z^(2*j+1) := mul_nonneg (price_nonneg F) (by positivity)
  calc
    _≤∑ v∈S,‖rho m r n e q a omega k N L v‖*
        ‖mean F U Z j gap v short-main F U Z j gap v short‖/(v.totient:ℝ) := by
      unfold signedError
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul,norm_div,Complex.norm_natCast,mul_div_assoc])
    _≤∑ v∈S,‖rho m r n e q a omega k N L v‖*
        (price F*(v.divisors.card:ℝ)*Z^(2*j+1))/(v.totient:ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (actual_E1 F hF hU hZ j gap v short
            (actual_modulus_class m r n e q a omega k N L (hS hv)).1) (norm_nonneg _))
        (Nat.cast_nonneg _)
    _=(price F*Z^(2*j+1))*
        ∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)/(v.totient:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (actual_reciprocal_moment m r n e q a omega k N D L S hS hlevel) hcost

theorem same_rho_actual_profile_E1 (isGap isLog gap : Bool) {delta U H t Z : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hH : 0≤H) (ht : |t|≤H)
    (hZ : 1≤Z) (j short : ℕ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N D : ℕ) (L : ℝ) (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    ‖signedError (profile isGap isLog delta U t) U Z j gap short m r n e q a omega k N L S‖≤
      profilePrice delta U H*Z^(2*j+1)*(4*(1+Real.log (max 1 (D:ℝ))))^16 := by
  have H0 := same_rho_E1 (profileSchwartz isGap isLog hd hs U t)
    (profile_support isGap isLog hd hs U t) hU hZ j gap short m r n e q a omega k N D L S hS hlevel
  apply H0.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (profile_price isGap isLog hd hs hH ht) (by positivity))
    (by positivity)

end
end ImbalancedChen.P4BOriginalSameRhoCoprimeE1
