import ImbalancedChen.P4BOriginalPositiveLongEnvelope
import ImbalancedChen.P1HistoricalTwoLongFiniteRoughData

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
