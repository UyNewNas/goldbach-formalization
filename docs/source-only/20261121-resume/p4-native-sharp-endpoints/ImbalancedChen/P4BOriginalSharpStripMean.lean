import ImbalancedChen.P4BOriginalSharpLongProfiles

/-! SOURCE ONLY / UNCOMPILED. Small CURRENT smooth strip mass is
retained in the per-q main term. It is not replaced by its delta^-2
derivative price. The fixed actual reciprocal moments are summed later. -/
namespace ImbalancedChen.P4BOriginalSharpStripMean
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalSharpLongProfiles
open P4BOriginalPairMeanNorm
open P4BOriginalCoprimeSmoothE1 (mass price)
open P4BOriginalBrunCoprimeE1 (mean density)
open P4BOriginalSameRhoCoprimeE1 (pairMean pairMean_factor)
open P4BOriginalTwoLongExpandedCore (rho actual_modulus_class)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalRoughE3Assembly (reciprocalMoment)

def stripPairMean {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U V Z : ℝ) (j q short : ℕ) : ℝ :=
  (pairMean (stripProfile true hd hs U) (stripProfile false hd hs V) U V Z j false false q short+
   pairMean (stripProfile false hd hs U) (stripProfile true hd hs V) U V Z j false false q short).re

theorem stripPairMean_point {delta U V Z x : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (j q short : ℕ) (hq : 0<q) (hy : Z^(2*j+1)≤x) :
    let y := Z^(2*j+1)
    let T := (q.divisors.card:ℝ)
    let L := densityLog x
    stripPairMean hd hs U V Z j q short≤
      (32*delta*U*V*L^2+4*stripPrice/delta^2*(U+V)*y*L*T+
        2*stripPrice^2/delta^4*y^2*T^2)/(q.totient:ℝ) := by
  let y := Z^(2*j+1)
  let T : ℝ := q.divisors.card
  let L := densityLog x
  let e := stripPrice/delta^2*T*y
  have hy0 : 0≤y := pow_nonneg (zero_le_one.trans hZ) _
  have hL : 0≤L := zero_le_one.trans (densityLog_one_le hx)
  have hT : 0≤T := Nat.cast_nonneg _
  have hP0 := stripPrice_nonneg
  have he : 0≤e := by dsimp [e]; exact mul_nonneg (mul_nonneg (div_nonneg stripPrice_nonneg (sq_nonneg _)) hT) hy0
  have hphi : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ratio : (q.totient:ℝ)/q≤1 := (div_le_one (by exact_mod_cast hq)).mpr (by exact_mod_cast Nat.totient_le q)
  have per (gap : Bool) (W a : ℝ) (hW : 0<W) (ha : 0≤a)
      (hm : ‖mass (stripProfile gap hd hs W)‖≤a) :
      ‖mean (stripProfile gap hd hs W) W Z j false q 1‖≤W*a*L+e := by
    have H := mean_norm_E1 (stripProfile gap hd hs W) (stripProfile_support gap hd hs W) hW hZ j false q 1 hq
    have hD := density_norm_le_log hZ hx j false q 1 hy
    have hP := strip_prices hd hs W gap
    apply H.trans
    calc
      _≤W*1*a*L+(stripPrice/delta^2)*T*y := by gcongr
      _=_ := by dsimp [e]; ring
  have Gu := per false U 2 hU (by norm_num) (strip_masses hd hs U).1
  have Gv := per false V 2 hV (by norm_num) (strip_masses hd hs V).1
  have Ku := per true U (8*delta) hU (by positivity) (strip_masses hd hs U).2
  have Kv := per true V (8*delta) hV (by positivity) (strip_masses hd hs V).2
  have pair (a b : Bool) :
      ‖pairMean (stripProfile a hd hs U) (stripProfile b hd hs V) U V Z j false false q short‖≤
        ‖mean (stripProfile a hd hs U) U Z j false q 1‖*
          ‖mean (stripProfile b hd hs V) V Z j false q 1‖/(q.totient:ℝ) := by
    rw [pairMean_factor]
    split_ifs
    · simp only [norm_mul,norm_inv,Complex.norm_natCast]; ring_nf
    · simp only [norm_zero]; positivity
  have H : stripPairMean hd hs U V Z j q short≤
      ((8*delta*U*L+e)*(2*V*L+e)+(2*U*L+e)*(8*delta*V*L+e))/(q.totient:ℝ) := by
    unfold stripPairMean
    rw [Complex.add_re]
    apply (add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)).trans
    apply (add_le_add (pair true false) (pair false true)).trans
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ hphi.le
    have H1 := mul_le_mul Ku Gv (norm_nonneg _) (by positivity)
    have H2 := mul_le_mul Gu Kv (norm_nonneg _) (by positivity)
    nlinarith only [H1,H2]
  apply H.trans
  apply div_le_div_of_nonneg_right _ hphi.le
  have hc : 2+8*delta≤4 := by linarith
  have hh := mul_le_mul_of_nonneg_left hc (mul_nonneg (mul_nonneg (add_nonneg hU.le hV.le) hL) he)
  have he2 : e^2=stripPrice^2/delta^4*y^2*T^2 := by
    dsimp [e]
    field_simp [hd.ne']
    ring
  have hid : (8*delta*U*L+e)*(2*V*L+e)+(2*U*L+e)*(8*delta*V*L+e)=
      32*delta*U*V*L^2+(2+8*delta)*(U+V)*L*e+2*e^2 := by ring
  rw [hid,he2]
  dsimp [e] at hh ⊢
  nlinarith only [hh]

def stripMeanSum {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U V Z : ℝ) (j : ℕ) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (level : ℝ) (S : Finset ℕ) : ℝ :=
  2*∑ v∈S,‖rho m r n e q a omega k N level v‖*
    ∑ short∈Mset,‖alpha short‖*stripPairMean hd hs U V Z j v short

def stripMeanBill (delta U V x y mu : ℝ) (D : ℕ) : ℝ :=
  2*mu*reciprocalMoment D*
    (32*delta*U*V*(densityLog x)^2+4*stripPrice/delta^2*(U+V)*y*densityLog x+
      2*stripPrice^2/delta^4*y^2)

theorem stripMeanSum_bound {delta U V Z x : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (j : ℕ) (hy : Z^(2*j+1)≤x) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (level : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N level v≠0 → v≤D) :
    stripMeanSum hd hs U V Z j Mset alpha m r n e q a omega k N level S≤
      stripMeanBill delta U V x (Z^(2*j+1)) (∑ short∈Mset,‖alpha short‖) D := by
  let mu := ∑ short∈Mset,‖alpha short‖
  let y := Z^(2*j+1)
  let a0 := 32*delta*U*V*(densityLog x)^2
  let a1 := 4*stripPrice/delta^2*(U+V)*y*densityLog x
  let a2 := 2*stripPrice^2/delta^4*y^2
  have hmu : 0≤mu := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have ha0 : 0≤a0 := by dsimp [a0]; positivity
  have ha1 : 0≤a1 := by have H:=densityLog_one_le hx; have P:=stripPrice_nonneg; dsimp [a1,y]; positivity
  have ha2 : 0≤a2 := by dsimp [a2]; positivity
  have hinner (v : ℕ) (hv : v∈S) :
      (∑ short∈Mset,‖alpha short‖*stripPairMean hd hs U V Z j v short)≤
      mu*(a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ) := by
    calc
      _≤∑ short∈Mset,‖alpha short‖*
          ((a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ)) :=
        Finset.sum_le_sum (fun short hshort => mul_le_mul_of_nonneg_left
          (stripPairMean_point hd hs hU hV hZ hx j v short
            (actual_modulus_class m r n e q a omega k N level (hS hv)).1 hy) (norm_nonneg _))
      _=_ := by rw [←Finset.sum_mul]; dsimp [mu]; ring
  have h0 := actual_tau_moment 0 (by norm_num) m r n e q a omega k N D level S hS hlevel
  have h1 := actual_tau_moment 1 (by norm_num) m r n e q a omega k N D level S hS hlevel
  have h2 := actual_tau_moment 2 (by norm_num) m r n e q a omega k N D level S hS hlevel
  have H := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 ha0)
    (mul_le_mul_of_nonneg_left h1 ha1)) (mul_le_mul_of_nonneg_left h2 ha2)
  have heq : (∑ v∈S,‖rho m r n e q a omega k N level v‖*
      (a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ))=
      a0*(∑ v∈S,‖rho m r n e q a omega k N level v‖*(v.divisors.card:ℝ)^0/(v.totient:ℝ))+
      a1*(∑ v∈S,‖rho m r n e q a omega k N level v‖*(v.divisors.card:ℝ)^1/(v.totient:ℝ))+
      a2*(∑ v∈S,‖rho m r n e q a omega k N level v‖*(v.divisors.card:ℝ)^2/(v.totient:ℝ)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  unfold stripMeanSum
  calc
    _≤2*∑ v∈S,‖rho m r n e q a omega k N level v‖*
        (mu*(a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v hv =>
        mul_le_mul_of_nonneg_left (hinner v hv) (norm_nonneg _))) (by norm_num)
    _=2*mu*∑ v∈S,‖rho m r n e q a omega k N level v‖*
        (a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _≤2*mu*((a0+a1+a2)*reciprocalMoment D) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact H.trans_eq (by unfold reciprocalMoment; ring)
    _=_ := by unfold stripMeanBill; dsimp [mu,a0,a1,a2,y]; ring

end
end ImbalancedChen.P4BOriginalSharpStripMean
