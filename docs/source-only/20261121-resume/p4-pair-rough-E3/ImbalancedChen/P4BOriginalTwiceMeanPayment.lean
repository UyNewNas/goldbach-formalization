import ImbalancedChen.P4BOriginalPositiveLongEnvelope

/-! SOURCE ONLY / UNCOMPILED. The two positive gap means are estimated
at each modulus, with their single 1/phi(q), and only then summed with
the actual absolute rho moments. This is the E3 twice-mean invoice. -/
namespace ImbalancedChen.P4BOriginalTwiceMeanPayment
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)
open P4BOriginalBrunCoprimeE1
open P4BOriginalSameRhoCoprimeE1 (pairMean pairMean_factor)
open P4BOriginalPairMeanNorm
open P4BOriginalPositiveLongEnvelope
open P4BOriginalTwoLongExpandedCore (rho actual_modulus_class)
open P4BOriginalFiniteSmoothCount (Q coefficient)

def gapPairMean (F G : ℝ→ℂ) (U V Z : ℝ) (j q short : ℕ) : ℝ :=
  (pairMean F G U V Z j true false q short+pairMean F G U V Z j false true q short).re

/-- The q-dependent main terms are still inside this inequality.
The denominator is exactly the original single phi(q). -/
theorem gapPairMean_point {delta U V Z x eps : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (he : 0≤eps) (he1 : eps≤1) (j q short : ℕ) (hq : 0<q) (hy : Z^(2*j+1)≤x)
    (hgap : ‖density Z j true q 1‖≤eps) :
    let F := envelopeSchwartz hd hs U
    let G := envelopeSchwartz hd hs V
    let y := Z^(2*j+1)
    let T := (q.divisors.card:ℝ)
    let L := densityLog x
    gapPairMean F G U V Z j q short≤
      meanPrice delta U*meanPrice delta V*
        (2*U*V*eps*L+2*L*(U+V)*y*T+2*y^2*T^2)/(q.totient:ℝ) := by
  let F := envelopeSchwartz hd hs U
  let G := envelopeSchwartz hd hs V
  let y := Z^(2*j+1)
  let T : ℝ := q.divisors.card
  let L := densityLog x
  let P1 := meanPrice delta U
  let P2 := meanPrice delta V
  have hP1 := meanPrice_nonneg delta U
  have hP2 := meanPrice_nonneg delta V
  have hL : 1≤L := densityLog_one_le hx
  have hy0 : 0≤y := pow_nonneg (zero_le_one.trans hZ) _
  have hT0 : 0≤T := Nat.cast_nonneg _
  have hphi : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ratio : 0≤(q.totient:ℝ)/q ∧ (q.totient:ℝ)/q≤1 := by
    refine ⟨by positivity,?_⟩
    exact (div_le_one (by exact_mod_cast hq)).mpr (by exact_mod_cast Nat.totient_le q)
  have hsF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) := by
    intro z hz
    apply envelope_support hd hs U
    simpa [F,envelopeSchwartz_apply] using hz
  have hsG : Function.support (G:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) := by
    intro z hz
    apply envelope_support hd hs V
    simpa [G,envelopeSchwartz_apply] using hz
  have per (J : 𝓢(ℝ,ℂ)) (hsJ : Function.support (J:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
      (W P c : ℝ) (hW : 0<W) (hP : 0≤P) (hc : 0≤c)
      (hmass : ‖mass J‖≤P) (hprice : price J≤P) (gap : Bool)
      (hcD : ‖density Z j gap q 1‖≤c) :
      ‖mean J W Z j gap q 1‖≤P*(W*c+y*T) := by
    apply (mean_norm_E1 J hsJ hW hZ j gap q 1 hq).trans
    have H0 : W*((q.totient:ℝ)/q)*‖mass J‖*‖density Z j gap q 1‖≤W*P*c := by
      calc
        _≤W*1*P*c := by gcongr
        _=_ := by ring
    have H1 : price J*(q.divisors.card:ℝ)*Z^(2*j+1)≤P*T*y := by gcongr
    nlinarith only [H0,H1]
  obtain ⟨hmF,hpF⟩ := envelope_prices hd hs U
  obtain ⟨hmG,hpG⟩ := envelope_prices hd hs V
  have Fg := per F hsF U P1 eps hU hP1 he hmF hpF true hgap
  have Gg := per G hsG V P2 eps hV hP2 he hmG hpG true hgap
  have Fu := per F hsF U P1 L hU hP1 (zero_le_one.trans hL) hmF hpF false (density_norm_le_log hZ hx j false q 1 hy)
  have Gu := per G hsG V P2 L hV hP2 (zero_le_one.trans hL) hmG hpG false (density_norm_le_log hZ hx j false q 1 hy)
  have pair (g1 g2 : Bool) :
      ‖pairMean F G U V Z j g1 g2 q short‖≤
        ‖mean F U Z j g1 q 1‖*‖mean G V Z j g2 q 1‖/(q.totient:ℝ) := by
    rw [pairMean_factor]
    split_ifs
    · simp only [norm_mul,norm_inv,Complex.norm_natCast]
      ring_nf
    · simp only [norm_zero]
      positivity
  have hg : gapPairMean F G U V Z j q short≤
      (‖mean F U Z j true q 1‖*‖mean G V Z j false q 1‖+
       ‖mean F U Z j false q 1‖*‖mean G V Z j true q 1‖)/(q.totient:ℝ) := by
    unfold gapPairMean
    rw [Complex.add_re]
    exact (add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)).trans
      ((add_le_add (pair true false) (pair false true)).trans_eq (by ring))
  apply hg.trans
  apply div_le_div_of_nonneg_right _ hphi.le
  have H := add_le_add
    (mul_le_mul Fg Gu (norm_nonneg _) (by positivity))
    (mul_le_mul Fu Gg (norm_nonneg _) (by positivity))
  have hEL : eps+L≤2*L := by linarith
  have hX := mul_le_mul_of_nonneg_left hEL
    (mul_nonneg (mul_nonneg hP1 hP2) (mul_nonneg (mul_nonneg (add_nonneg hU.le hV.le) hy0) hT0))
  nlinarith only [H,hX]

def twiceMeanSum {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U V Z : ℝ) (j : ℕ) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L : ℝ) (S : Finset ℕ) : ℝ :=
  2*∑ v∈S,‖rho m r n e q a omega k N L v‖*
    ∑ short∈Mset,‖alpha short‖*
      gapPairMean (envelopeSchwartz hd hs U) (envelopeSchwartz hd hs V) U V Z j v short

/-- Absolute reciprocal moments are summed only AFTER the per-q E1
pair estimate; both copies of the exact mean remain visible in the 2. -/
theorem twiceMeanSum_bound {delta U V Z x eps : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (he : 0≤eps) (he1 : eps≤1) (j : ℕ) (hy : Z^(2*j+1)≤x)
    (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hgap : ∀ v∈S,‖density Z j true v 1‖≤eps)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    twiceMeanSum hd hs U V Z j Mset alpha m r n e q a omega k N L S≤
      2*(∑ short∈Mset,‖alpha short‖)*meanPrice delta U*meanPrice delta V*
        (4*(1+Real.log (max 1 (D:ℝ))))^16*
        (2*U*V*eps*densityLog x+2*densityLog x*(U+V)*Z^(2*j+1)+2*(Z^(2*j+1))^2) := by
  let M := ∑ short∈Mset,‖alpha short‖
  let P := meanPrice delta U*meanPrice delta V
  let y := Z^(2*j+1)
  let a0 := 2*U*V*eps*densityLog x
  let a1 := 2*densityLog x*(U+V)*y
  let a2 := 2*y^2
  have hM : 0≤M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hP : 0≤P := mul_nonneg (meanPrice_nonneg _ _) (meanPrice_nonneg _ _)
  have ha0 : 0≤a0 := by have := densityLog_one_le hx; dsimp [a0]; positivity
  have ha1 : 0≤a1 := by have := densityLog_one_le hx; dsimp [a1,y]; positivity
  have ha2 : 0≤a2 := by dsimp [a2]; positivity
  have hb : twiceMeanSum hd hs U V Z j Mset alpha m r n e q a omega k N L S≤
      2*M*P*∑ v∈S,‖rho m r n e q a omega k N L v‖*
        (a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ) := by
    have hinner (v : ℕ) (hv : v∈S) :
        (∑ short∈Mset,‖alpha short‖*gapPairMean (envelopeSchwartz hd hs U)
          (envelopeSchwartz hd hs V) U V Z j v short)≤
        M*(P*(a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ)) := by
      calc
        _≤∑ short∈Mset,‖alpha short‖*
            (P*(a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ)) := by
          apply Finset.sum_le_sum
          intro short hshort
          exact mul_le_mul_of_nonneg_left
            (gapPairMean_point hd hs hU hV hZ hx he he1 j v short
              (actual_modulus_class m r n e q a omega k N L (hS hv)).1 hy (hgap v hv)) (norm_nonneg _)
        _=_ := by rw [←Finset.sum_mul]
    unfold twiceMeanSum
    calc
      _≤2*∑ v∈S,‖rho m r n e q a omega k N L v‖*
          (M*(P*(a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v hv =>
          mul_le_mul_of_nonneg_left (hinner v hv) (norm_nonneg _))) (by norm_num)
      _=_ := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
  have h0 := actual_tau_moment 0 (by norm_num) m r n e q a omega k N D L S hS hlevel
  have h1 := actual_tau_moment 1 (by norm_num) m r n e q a omega k N D L S hS hlevel
  have h2 := actual_tau_moment 2 (by norm_num) m r n e q a omega k N D L S hS hlevel
  have heq : (∑ v∈S,‖rho m r n e q a omega k N L v‖*
      (a0+a1*(v.divisors.card:ℝ)+a2*(v.divisors.card:ℝ)^2)/(v.totient:ℝ))=
      a0*(∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^0/(v.totient:ℝ))+
      a1*(∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^1/(v.totient:ℝ))+
      a2*(∑ v∈S,‖rho m r n e q a omega k N L v‖*(v.divisors.card:ℝ)^2/(v.totient:ℝ)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [heq] at hb
  have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 ha0)
    (mul_le_mul_of_nonneg_left h1 ha1)) (mul_le_mul_of_nonneg_left h2 ha2)
  exact hb.trans ((mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*M*P)).trans_eq
    (by dsimp [M,P,a0,a1,a2,y]; ring))

end
end ImbalancedChen.P4BOriginalTwiceMeanPayment
