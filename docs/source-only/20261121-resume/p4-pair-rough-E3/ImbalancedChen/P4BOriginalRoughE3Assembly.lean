import ImbalancedChen.P4BOriginalEnvelopePolynomialPayment

/-! SOURCE ONLY / UNCOMPILED. Finite actual rough two-long invoice:
three polynomial P2 terms and exactly twice the coprime gap mean.
No spectral estimate, rough estimate or aggregate mean hypothesis. -/
namespace ImbalancedChen.P4BOriginalRoughE3Assembly
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalRoughPairFinite
open P4BOriginalEnvelopePolynomialPayment
open P4BOriginalPositiveLongEnvelope
open P4BOriginalTwiceMeanPayment
open P4BOriginalPairMeanNorm (densityLog)
open P4BOriginalBrunCoprimeE1 (density)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open Part3.TwoLongTransitionMellinN2

def roughSum (F G : ℝ→ℂ) (U V Z : ℝ) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ v∈S,rho m r n e q a omega k N L v*
    ∑ short∈Mset,roughDelta F G U V Z short N v (alpha short)

def polyMoment (D : ℕ) : ℝ := ((D:ℝ)*Real.sqrt D+1)*(4*(1+Real.log (max 1 (D:ℝ))))^16
def reciprocalMoment (D : ℕ) : ℝ := (4*(1+Real.log (max 1 (D:ℝ))))^16

theorem finite_rough_invoice (fGap fLog gGap gLog : Bool) {delta U V Z x eps : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (he : 0≤eps) (he1 : eps≤1) (t1 t2 : ℝ) (j : ℕ) (hy : Z^(2*j+1)≤x)
    (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hgap : ∀ v∈S,‖density Z j true v 1‖≤eps)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    let F := profileSchwartz fGap fLog hd hs U t1
    let G := profileSchwartz gGap gLog hd hs V t2
    let E := envelopeSchwartz hd hs U
    let J := envelopeSchwartz hd hs V
    let M := ∑ short∈Mset,‖alpha short‖
    let y := Z^(2*j+1)
    ‖roughSum F G U V Z Mset alpha m r n e q a omega k N L S‖≤
      (p2Price F G+2*p2Price E J)*(y^2*M)*polyMoment D+
      2*M*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*eps*densityLog x+2*densityLog x*(U+V)*y+2*y^2) := by
  let F := profileSchwartz fGap fLog hd hs U t1
  let G := profileSchwartz gGap gLog hd hs V t2
  let E := envelopeSchwartz hd hs U
  let J := envelopeSchwartz hd hs V
  let M := ∑ short∈Mset,‖alpha short‖
  let y := Z^(2*j+1)
  let absAlpha := fun short => (‖alpha short‖:ℂ)
  have hsE : Function.support (E:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) := by
    intro z hz
    exact envelope_support hd hs U (by simpa only [E,envelopeSchwartz_apply,Complex.ofReal_eq_zero] using hz)
  have hsJ : Function.support (J:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) := by
    intro z hz
    exact envelope_support hd hs V (by simpa only [J,envelopeSchwartz_apply,Complex.ofReal_eq_zero] using hz)
  have hA := absolute_polynomial_sum F G (profile_support fGap fLog hd hs U t1)
    (profile_support gGap gLog hd hs V t2) hU hV hZ j false false Mset alpha
    m r n e q a omega k N D L S hS hlevel
  have hB := absolute_polynomial_sum E J hsE hsJ hU hV hZ j true false Mset absAlpha
    m r n e q a omega k N D L S hS hlevel
  have hC := absolute_polynomial_sum E J hsE hsJ hU hV hZ j false true Mset absAlpha
    m r n e q a omega k N D L S hS hlevel
  have hmass : (∑ short∈Mset,‖absAlpha short‖)=M := by
    simp only [absAlpha,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),M]
  rw [hmass] at hB hC
  have hmean := twiceMeanSum_bound hd hs hU hV hZ hx he he1 j hy Mset alpha
    m r n e q a omega k N D L S hS hgap hlevel
  have hpoint (v short : ℕ) :
      ‖roughDelta F G U V Z short N v (alpha short)‖≤
        ‖polyDelta F G U V Z j false false short N v (alpha short)‖+
        ‖polyDelta E J U V Z j true false short N v (absAlpha short)‖+
        ‖polyDelta E J U V Z j false true short N v (absAlpha short)‖+
        2*‖alpha short‖*gapPairMean E J U V Z j v short := by
    have H := actual_pair_E3 fGap fLog gGap gLog hd hs U V t1 t2 Z j short N v (alpha short)
    change ‖roughDelta F G U V Z short N v (alpha short)-polyDelta F G U V Z j false false short N v (alpha short)‖≤_ at H
    have H' := H.trans (add_le_add_right (norm_add_le _ _) _)
    have ht := norm_sub_le (roughDelta F G U V Z short N v (alpha short)-polyDelta F G U V Z j false false short N v (alpha short))
      (-polyDelta F G U V Z j false false short N v (alpha short))
    rw [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
    simp only [F,G,E,J,absAlpha,profileSchwartz_coe,envelopeSchwartz_coe] at H' ht ⊢
    linarith
  have hsummed : ‖roughSum F G U V Z Mset alpha m r n e q a omega k N L S‖≤
      (∑ v∈S,‖rho m r n e q a omega k N L v‖*∑ short∈Mset,‖polyDelta F G U V Z j false false short N v (alpha short)‖)+
      (∑ v∈S,‖rho m r n e q a omega k N L v‖*∑ short∈Mset,‖polyDelta E J U V Z j true false short N v (absAlpha short)‖)+
      (∑ v∈S,‖rho m r n e q a omega k N L v‖*∑ short∈Mset,‖polyDelta E J U V Z j false true short N v (absAlpha short)‖)+
      twiceMeanSum hd hs U V Z j Mset alpha m r n e q a omega k N L S := by
    unfold roughSum
    calc
      _≤∑ v∈S,‖rho m r n e q a omega k N L v‖*∑ short∈Mset,‖roughDelta F G U V Z short N v (alpha short)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _≤∑ v∈S,‖rho m r n e q a omega k N L v‖*
          ∑ short∈Mset,(‖polyDelta F G U V Z j false false short N v (alpha short)‖+
            ‖polyDelta E J U V Z j true false short N v (absAlpha short)‖+
            ‖polyDelta E J U V Z j false true short N v (absAlpha short)‖+
            2*‖alpha short‖*gapPairMean E J U V Z j v short) :=
        Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun short hshort => hpoint v short)) (norm_nonneg _))
      _=_ := by simp only [twiceMeanSum,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]; ring
  exact hsummed.trans ((add_le_add (add_le_add (add_le_add hA hB) hC) hmean).trans_eq
    (by dsimp [polyMoment,reciprocalMoment,M,y]; ring))

end
end ImbalancedChen.P4BOriginalRoughE3Assembly
