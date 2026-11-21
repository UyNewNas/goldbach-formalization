import ImbalancedChen.P4BOriginalSharpStripMean

/-! SOURCE ONLY / UNCOMPILED. Actual sharp-to-upper comparison.
All monotonicity is in the nonnegative count+exact-mean functionals.
The two comparison discrepancies are genuine upper-Brun polynomial
strip terms and use current-q sf P2; the original signed rho is kept. -/
namespace ImbalancedChen.P4BOriginalSharpPairComparison
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open PrimeProducts
open P4BOriginalSharpLongProfiles
open P4BOriginalSharpStripMean
open P4BOriginalRoughPairFinite
open P4BOriginalRoughE3Assembly (roughSum polyMoment)
open P4BOriginalEnvelopePolynomialPayment
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongQuantitativeTransitionProfiles

theorem sharp_pair_point (log1 log2 : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U V t1 t2 Z : ℝ) (j short N q : ℕ) (alpha : ℂ) :
    ‖roughDelta (sharpProfile log1 U t1) (sharpProfile log2 V t2) U V Z short N q alpha-
      roughDelta (profile false log1 delta U t1) (profile false log2 delta V t2) U V Z short N q alpha‖≤
      logSize U*logSize V*
        (‖polyDelta (stripProfile true hd hs U) (stripProfile false hd hs V) U V Z j false false short N q (‖alpha‖:ℂ)+
          polyDelta (stripProfile false hd hs U) (stripProfile true hd hs V) U V Z j false false short N q (‖alpha‖:ℂ)‖+
        2*‖alpha‖*stripPairMean hd hs U V Z j q short) := by
  let T := wideWindow U ×ˢ wideWindow V
  let W := fun p : ℕ×ℕ => alpha*
    (profile false log1 delta U t1 ((p.1:ℝ)/U)*profile false log2 delta V t2 ((p.2:ℝ)/V)-
      sharpProfile log1 U t1 ((p.1:ℝ)/U)*sharpProfile log2 V t2 ((p.2:ℝ)/V))*
    ((roughR Z p.1*roughR Z p.2:ℝ):ℂ)
  let L := logSize U*logSize V
  let A := fun p : ℕ×ℕ => ‖alpha‖*L*stripShape delta ((p.1:ℝ)/U) ((p.2:ℝ)/V)*
    (polyR Z j false p.1*polyR Z j false p.2)
  have hL : 0≤L := mul_nonneg (zero_le_one.trans (logSize_one_le U)) (zero_le_one.trans (logSize_one_le V))
  have hpoint (p : ℕ×ℕ) : ‖W p‖≤A p := by
    have b1 := bounds Z j p.1
    have b2 := bounds Z j p.2
    have hr : 0≤roughR Z p.1*roughR Z p.2 := mul_nonneg b1.1 b2.1
    have hu : roughR Z p.1*roughR Z p.2≤polyR Z j false p.1*polyR Z j false p.2 :=
      mul_le_mul b1.2.1 b2.2.1 b2.1 (b1.1.trans b1.2.1)
    have hs0 := stripShape_nonneg delta ((p.1:ℝ)/U) ((p.2:ℝ)/V)
    have he := sharp_pair_profile_error log1 log2 hd hs U V t1 t2 ((p.1:ℝ)/U) ((p.2:ℝ)/V)
    rw [norm_sub_rev] at he
    dsimp [W,A]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _)) hu hr
      (mul_nonneg (norm_nonneg _) (mul_nonneg hL hs0))
  have H := majorized_E3 T W A (fun _=>0) (fun _=>1) (fun _=>1)
    (fun p=>countKernel q N (short*p.1*p.2)) (fun p=>meanKernel q (short*p.1*p.2))
    (fun p hp=>hpoint p) (by intro p hp; norm_num)
    (by intro p hp; unfold countKernel; split_ifs <;> norm_num)
    (by intro p hp; unfold meanKernel; split_ifs <;> positivity)
  have hleft : (∑ p∈T,W p*((0-1:ℝ):ℂ)*
      ((countKernel q N (short*p.1*p.2)-meanKernel q (short*p.1*p.2):ℝ):ℂ))=
      roughDelta (sharpProfile log1 U t1) (sharpProfile log2 V t2) U V Z short N q alpha-
        roughDelta (profile false log1 delta U t1) (profile false log2 delta V t2) U V Z short N q alpha := by
    simp only [roughDelta,T,Finset.sum_product,←Finset.sum_sub_distrib,kernel_real]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [W]
    push_cast
    ring
  have hright : ((∑ p∈T,A p*1*(countKernel q N (short*p.1*p.2)-meanKernel q (short*p.1*p.2)):ℝ):ℂ)=
      (L:ℂ)*(polyDelta (stripProfile true hd hs U) (stripProfile false hd hs V) U V Z j false false short N q (‖alpha‖:ℂ)+
        polyDelta (stripProfile false hd hs U) (stripProfile true hd hs V) U V Z j false false short N q (‖alpha‖:ℂ)) := by
    simp only [polyDelta,T,Finset.sum_product,Complex.ofReal_sum,Finset.mul_sum,←Finset.sum_add_distrib,
      polynomial_cast,kernel_real,stripProfile_apply,if_true,if_false]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [A,stripShape]
    push_cast
    ring
  have hmean : (∑ p∈T,A p*1*meanKernel q (short*p.1*p.2))=
      L*‖alpha‖*stripPairMean hd hs U V Z j q short := by
    have hphi : (q.totient:ℂ)⁻¹=((1/(q.totient:ℝ)):ℂ) := by simp [one_div]
    simp only [stripPairMean,P4BOriginalSameRhoCoprimeE1.pairMean,T,Finset.sum_product,hphi,
      Complex.add_re,Complex.re_sum,Finset.mul_sum,←Finset.sum_add_distrib,polynomial_cast,
      stripProfile_apply,if_true,if_false]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hc : (short*u*v).Coprime q <;>
      simp [A,stripShape,meanKernel,hc,Complex.mul_re,div_eq_mul_inv] <;> ring
  rw [hleft,hright,hmean,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL] at H
  exact H.trans_eq (by dsimp [L]; ring)

def sharpDifference (log1 log2 : Bool) (delta U V t1 t2 Z : ℝ)
    (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (level : ℝ) (S : Finset ℕ) : ℂ :=
  roughSum (sharpProfile log1 U t1) (sharpProfile log2 V t2) U V Z Mset alpha m r n e q a omega k N level S-
    roughSum (profile false log1 delta U t1) (profile false log2 delta V t2) U V Z Mset alpha m r n e q a omega k N level S

theorem finite_endpoint_invoice (log1 log2 : Bool) {delta U V Z x : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V) (hZ : 1≤Z) (hx : 1≤x)
    (t1 t2 : ℝ) (j : ℕ) (hy : Z^(2*j+1)≤x) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (level : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N level v≠0 → v≤D) :
    let G1 := stripProfile true hd hs U
    let U1 := stripProfile false hd hs U
    let G2 := stripProfile true hd hs V
    let U2 := stripProfile false hd hs V
    let mu := ∑ short∈Mset,‖alpha short‖
    let y := Z^(2*j+1)
    ‖sharpDifference log1 log2 delta U V t1 t2 Z Mset alpha m r n e q a omega k N level S‖≤
      logSize U*logSize V*
        ((p2Price G1 U2+p2Price U1 G2)*(y^2*mu)*polyMoment D+
          stripMeanBill delta U V x y mu D) := by
  let absAlpha := fun short => (‖alpha short‖:ℂ)
  let mu := ∑ short∈Mset,‖alpha short‖
  let L := logSize U*logSize V
  have hL : 0≤L := mul_nonneg (zero_le_one.trans (logSize_one_le U)) (zero_le_one.trans (logSize_one_le V))
  have hA := absolute_polynomial_sum (stripProfile true hd hs U) (stripProfile false hd hs V)
    (stripProfile_support true hd hs U) (stripProfile_support false hd hs V) hU hV hZ j false false Mset absAlpha
    m r n e q a omega k N D level S hS hlevel
  have hB := absolute_polynomial_sum (stripProfile false hd hs U) (stripProfile true hd hs V)
    (stripProfile_support false hd hs U) (stripProfile_support true hd hs V) hU hV hZ j false false Mset absAlpha
    m r n e q a omega k N D level S hS hlevel
  have hmass : (∑ short∈Mset,‖absAlpha short‖)=mu := by simp [absAlpha,mu]
  rw [hmass] at hA hB
  have hMean := stripMeanSum_bound hd hs hU hV hZ hx j hy Mset alpha m r n e q a omega k N D level S hS hlevel
  have Hpoint (v short : ℕ) := (sharp_pair_point log1 log2 hd hs U V t1 t2 Z j short N v (alpha short)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right (norm_add_le _ _) _) hL)
  have H : ‖sharpDifference log1 log2 delta U V t1 t2 Z Mset alpha m r n e q a omega k N level S‖≤
      L*((∑ v∈S,‖rho m r n e q a omega k N level v‖*∑ short∈Mset,
        ‖polyDelta (stripProfile true hd hs U) (stripProfile false hd hs V) U V Z j false false short N v (absAlpha short)‖)+
        (∑ v∈S,‖rho m r n e q a omega k N level v‖*∑ short∈Mset,
        ‖polyDelta (stripProfile false hd hs U) (stripProfile true hd hs V) U V Z j false false short N v (absAlpha short)‖)+
        stripMeanSum hd hs U V Z j Mset alpha m r n e q a omega k N level S) := by
    unfold sharpDifference roughSum
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑ v∈S,‖rho m r n e q a omega k N level v‖*∑ short∈Mset,
          ‖roughDelta (sharpProfile log1 U t1) (sharpProfile log2 V t2) U V Z short N v (alpha short)-
            roughDelta (profile false log1 delta U t1) (profile false log2 delta V t2) U V Z short N v (alpha short)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v hv
        rw [←mul_sub,norm_mul,←Finset.sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _≤∑ v∈S,‖rho m r n e q a omega k N level v‖*∑ short∈Mset,
          L*(‖polyDelta (stripProfile true hd hs U) (stripProfile false hd hs V) U V Z j false false short N v (absAlpha short)‖+
          ‖polyDelta (stripProfile false hd hs U) (stripProfile true hd hs V) U V Z j false false short N v (absAlpha short)‖+
          2*‖alpha short‖*stripPairMean hd hs U V Z j v short) :=
        Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun short hshort => Hpoint v short)) (norm_nonneg _))
      _=_ := by simp only [stripMeanSum,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]; ring
  exact H.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hB) hMean) hL).trans_eq
    (by dsimp [L,mu,polyMoment]; ring))

end
end ImbalancedChen.P4BOriginalSharpPairComparison
