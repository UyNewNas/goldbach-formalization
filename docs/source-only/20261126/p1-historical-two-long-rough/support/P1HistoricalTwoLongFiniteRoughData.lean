import ImbalancedChen.P1HistoricalTwoLongExactPairMeanData
import ImbalancedChen.P4BOriginalPositiveLongEnvelope
import ImbalancedChen.P5ActualHBRoughBrunFinite
import ImbalancedChen.Part3TwoLongBrunComplexGap
import ImbalancedChen.P4BOriginalSquarefreeP2

/-! SOURCE ONLY / UNCOMPILED. Original declaration bytes are preserved;
see EXTRACTION_BINDING.json. No compilation or kernel credit is added. -/
namespace ImbalancedChen.P4BOriginalTwiceMeanPayment
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)
open P4BOriginalBrunCoprimeE1
open P4BOriginalSameRhoCoprimeE1 (pairMean pairMean_factor)
open P4BOriginalPairMeanNorm
open P4BOriginalPositiveLongEnvelope

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

end
end ImbalancedChen.P4BOriginalTwiceMeanPayment

namespace ImbalancedChen.P4BOriginalRoughPairFinite
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open PrimeProducts
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial brunPolynomial_eq_literal)
open Part3.TwoLongActualLowerBrunMoment (brunSupport)
open OriginalOneLongLiteralBrunDictionary (upperCoefficient gapCoefficient actual_B1)
open OriginalOneLongFiniteBrun (polynomial divisorMask actualRough)
open Part3.TwoLongDivisorAxisClosure (chartDivisor)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime)
open Part3.TwoLongTransitionMellinN2
open P4BOriginalPositiveLongEnvelope
open P4BOriginalTwiceMeanPayment (gapPairMean)

def polyR (Z : ℝ) (j : ℕ) (gap : Bool) (n : ℕ) : ℝ :=
  polynomial (brunSupport Z (2*j+1)) divisorMask
    (fun d => if gap then gapCoefficient (smallPrimes Z) (2*j+1) d else upperCoefficient (smallPrimes Z) (2*j) d) n
def roughR (Z : ℝ) (n : ℕ) : ℝ := actualRough (chartDivisor (smallPrimes Z)) n

theorem polynomial_cast (Z : ℝ) (j : ℕ) (gap : Bool) (n : ℕ) :
    brunPolynomial Z j gap n=(polyR Z j gap n:ℂ) :=
  brunPolynomial_eq_literal Z j gap n

theorem rough_slot_cast {Z : ℝ} (hZ : 0≤Z) (n : ℕ) : Part3.roughOneSlot Z n=(roughR Z n:ℂ) := by
  simpa only [roughR,P5Z.ActualHBRoughBrunFinite.chartPrimes,smallPrimes] using
    P5Z.ActualHBRoughBrunFinite.roughOneSlot_eq_actualRough hZ n

theorem bounds (Z : ℝ) (j n : ℕ) :
    0≤roughR Z n ∧ roughR Z n≤polyR Z j false n ∧
      polyR Z j false n-roughR Z n≤polyR Z j true n := by
  have H := actual_B1 j (smallPrimes Z) n (fun p hp => smallPrimes_prime hp)
  have hr : 0≤roughR Z n := by unfold roughR actualRough; split_ifs <;> norm_num
  have hlow : 0≤polyR Z j false n-roughR Z n := by
    simpa only [polyR,if_false,if_true,roughR] using H.1
  exact ⟨hr,sub_nonneg.mp hlow,
    by simpa only [polyR,if_false,if_true,roughR] using H.2⟩

def countKernel (q N n : ℕ) : ℝ := if n%q=N%q then 1 else 0
def meanKernel (q n : ℕ) : ℝ := if n.Coprime q then 1/(q.totient:ℝ) else 0

theorem kernel_real (q N n : ℕ) : MellinInsertion20261028.residueKernel q N n=
    ((countKernel q N n-meanKernel q n:ℝ):ℂ) := by
  by_cases ha : n%q=N%q <;> by_cases hc : n.Coprime q <;>
    simp [MellinInsertion20261028.residueKernel,countKernel,meanKernel,ha,hc,div_eq_mul_inv] <;> ring

theorem majorized_E3 {ι : Type*} (T : Finset ι) (w : ι→ℂ) (A r u g C M : ι→ℝ)
    (hw : ∀ t∈T,‖w t‖≤A t)
    (hB : ∀ t∈T,0≤u t-r t ∧ u t-r t≤g t)
    (hC : ∀ t∈T,0≤C t) (hM : ∀ t∈T,0≤M t) :
    ‖∑ t∈T,w t*((r t-u t:ℝ):ℂ)*((C t-M t:ℝ):ℂ)‖≤
      ‖((∑ t∈T,A t*g t*(C t-M t):ℝ):ℂ)‖+2*∑ t∈T,A t*g t*M t := by
  have hpoint (t) (ht : t∈T) :
      ‖w t*((r t-u t:ℝ):ℂ)*((C t-M t:ℝ):ℂ)‖≤A t*g t*(C t+M t) := by
    have hA0 := (norm_nonneg _).trans (hw t ht)
    have hg0 := (hB t ht).1.trans (hB t ht).2
    have hab : |r t-u t|=u t-r t := by
      rw [abs_of_nonpos (by linarith [(hB t ht).1])]
      ring
    have hcm : |C t-M t|≤C t+M t := by rw [abs_le]; constructor <;> linarith [hC t ht,hM t ht]
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,hab]
    exact mul_le_mul (mul_le_mul (hw t ht) (hB t ht).2 (hB t ht).1 hA0) hcm (abs_nonneg _)
      (mul_nonneg hA0 hg0)
  have hid : (∑ t∈T,A t*g t*(C t+M t))=
      (∑ t∈T,A t*g t*(C t-M t))+2*∑ t∈T,A t*g t*M t := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  calc
    _≤∑ t∈T,‖w t*((r t-u t:ℝ):ℂ)*((C t-M t:ℝ):ℂ)‖ := norm_sum_le _ _
    _≤∑ t∈T,A t*g t*(C t+M t) := Finset.sum_le_sum hpoint
    _=_ := hid
    _≤_ := add_le_add_right (by simpa only [Complex.norm_real,Real.norm_eq_abs] using le_abs_self _) _

def polyDelta (F G : ℝ→ℂ) (U V Z : ℝ) (j : ℕ) (g1 g2 : Bool) (short N q : ℕ) (alpha : ℂ) : ℂ :=
  ∑ u∈wideWindow U,∑ v∈wideWindow V,alpha*F ((u:ℝ)/U)*G ((v:ℝ)/V)*
    (brunPolynomial Z j g1 u*brunPolynomial Z j g2 v)*MellinInsertion20261028.residueKernel q N (short*u*v)

def roughDelta (F G : ℝ→ℂ) (U V Z : ℝ) (short N q : ℕ) (alpha : ℂ) : ℂ :=
  ∑ u∈wideWindow U,∑ v∈wideWindow V,alpha*F ((u:ℝ)/U)*G ((v:ℝ)/V)*
    ((roughR Z u*roughR Z v:ℝ):ℂ)*MellinInsertion20261028.residueKernel q N (short*u*v)

theorem roughDelta_original (F G : ℝ→ℂ) (U V : ℝ) {Z : ℝ} (hZ : 0≤Z)
    (short N q : ℕ) (alpha : ℂ) :
    roughDelta F G U V Z short N q alpha=
      ∑ u∈wideWindow U,∑ v∈wideWindow V,alpha*F ((u:ℝ)/U)*G ((v:ℝ)/V)*
        Part3.roughOneSlot Z u*Part3.roughOneSlot Z v*MellinInsertion20261028.residueKernel q N (short*u*v) := by
  simp only [roughDelta,rough_slot_cast hZ,Complex.ofReal_mul,mul_assoc]

/-- Actual complex profiles and a constructed positive smooth envelope.
The right-hand comparison contains the sum of BOTH Brun gap products. -/
theorem actual_pair_E3 (fGap fLog gGap gLog : Bool) {delta : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (U V t1 t2 Z : ℝ) (j short N q : ℕ) (alpha : ℂ) :
    let F := profile fGap fLog delta U t1
    let G := profile gGap gLog delta V t2
    let E := fun x => (envelope delta U x:ℂ)
    let J := fun x => (envelope delta V x:ℂ)
    ‖roughDelta F G U V Z short N q alpha-polyDelta F G U V Z j false false short N q alpha‖≤
      ‖polyDelta E J U V Z j true false short N q (‖alpha‖:ℂ)+
        polyDelta E J U V Z j false true short N q (‖alpha‖:ℂ)‖+
      2*‖alpha‖*gapPairMean E J U V Z j q short := by
  let T := wideWindow U ×ˢ wideWindow V
  let F := profile fGap fLog delta U t1
  let G := profile gGap gLog delta V t2
  let E := fun x => (envelope delta U x:ℂ)
  let J := fun x => (envelope delta V x:ℂ)
  let A := fun p : ℕ×ℕ => ‖alpha‖*envelope delta U ((p.1:ℝ)/U)*envelope delta V ((p.2:ℝ)/V)
  let r := fun p : ℕ×ℕ => roughR Z p.1*roughR Z p.2
  let u := fun p : ℕ×ℕ => polyR Z j false p.1*polyR Z j false p.2
  let g := fun p : ℕ×ℕ => polyR Z j true p.1*polyR Z j false p.2+polyR Z j false p.1*polyR Z j true p.2
  have h := majorized_E3 T (fun p => alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V)) A r u g
    (fun p => countKernel q N (short*p.1*p.2)) (fun p => meanKernel q (short*p.1*p.2))
    (fun p hp => by
      dsimp [A,F,G]
      simp only [norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (profile_majorant fGap fLog hd hs U t1 _) (norm_nonneg _))
        (profile_majorant gGap gLog hd hs V t2 _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (envelope_nonneg _ _ _)))
    (fun p hp => Part3.TwoLongBrunComplexGap.twoLongSandwich _ _ _ _ _ _
      (bounds Z j p.1).1 (bounds Z j p.2).1 (bounds Z j p.1).2.1 (bounds Z j p.2).2.1
      (bounds Z j p.1).2.2 (bounds Z j p.2).2.2)
    (fun p hp => by unfold countKernel; split_ifs <;> norm_num)
    (fun p hp => by unfold meanKernel; split_ifs <;> positivity)
  have hleft : roughDelta F G U V Z short N q alpha-polyDelta F G U V Z j false false short N q alpha=
      ∑ p∈T,(alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V))*((r p-u p:ℝ):ℂ)*
        ((countKernel q N (short*p.1*p.2)-meanKernel q (short*p.1*p.2):ℝ):ℂ) := by
    simp only [roughDelta,polyDelta,T,Finset.sum_product,←Finset.sum_sub_distrib,polynomial_cast,kernel_real]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [r,u]
    push_cast
    ring
  have hright : ((∑ p∈T,A p*g p*(countKernel q N (short*p.1*p.2)-meanKernel q (short*p.1*p.2)):ℝ):ℂ)=
      polyDelta E J U V Z j true false short N q (‖alpha‖:ℂ)+
        polyDelta E J U V Z j false true short N q (‖alpha‖:ℂ) := by
    simp only [polyDelta,T,Finset.sum_product,Complex.ofReal_sum,←Finset.sum_add_distrib,polynomial_cast,kernel_real]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [A,g,E,J]
    push_cast
    ring
  have hmean : (∑ p∈T,A p*g p*meanKernel q (short*p.1*p.2))=
      ‖alpha‖*gapPairMean E J U V Z j q short := by
    have hphi : (q.totient:ℂ)⁻¹=((1/(q.totient:ℝ)):ℂ) := by simp [one_div]
    simp only [gapPairMean,P4BOriginalSameRhoCoprimeE1.pairMean,T,Finset.sum_product,
      hphi,Complex.add_re,Complex.re_sum,polynomial_cast,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hc : (short*a*b).Coprime q <;>
      simp [A,g,E,J,meanKernel,hc,Complex.mul_re,div_eq_mul_inv] <;> ring
  rw [←hleft,hright,hmean] at h
  simpa only [mul_assoc] using h

end
end ImbalancedChen.P4BOriginalRoughPairFinite

namespace ImbalancedChen.P4BOriginalEnvelopePolynomialPayment
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open PrimeProducts
open P4BOriginalRoughPairFinite (polyDelta)
open Part3.TwoLongLiteralMellinModes (N2 wideWindow)
open Part3.TwoLongFixedMRectangularCore (fixedMCore)
open Part3.TwoLongLiteralBrunSubstitution
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds brunPairCoefficient brunPair_mass)
open Part3.TwoLongNaturalInternalP2 (internalP2Constant internalP2Constant_pos)
open Part3.TwoLongInternalP2Modes (N2_nonneg)
open Part3.TwoLongActualThreeBrunP2Receiver (modulusBudget modulusBudget_nonneg)

def p2Price (F G : 𝓢(ℝ,ℂ)) : ℝ := internalP2Constant*N2 (F:ℝ→ℂ)*N2 (G:ℝ→ℂ)

theorem p2Price_nonneg (F G : 𝓢(ℝ,ℂ)) : 0≤p2Price F G :=
  mul_nonneg (mul_nonneg internalP2Constant_pos.le (N2_nonneg _)) (N2_nonneg _)

theorem polynomial_expansion (F G : ℝ→ℂ)
    (hF : Function.support F⊆Icc (1/2:ℝ) (5/2)) (hG : Function.support G⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (short N q : ℕ) (alpha : ℂ) :
    polyDelta F G U V Z j g1 g2 short N q alpha=
      ∑ d∈(brunSupport Z (2*j+1))×ˢ(brunSupport Z (2*j+1)),
        brunPairCoefficient Z j g1 g2 d *
          fixedMCore (wideWindow (U/d.1)) (wideWindow (V/d.2)) (short*d.1*d.2) N q alpha F G (U/d.1) (V/d.2) := by
  let I := wideWindow U ×ˢ wideWindow V
  let R := brunSupport Z (2*j+1) ×ˢ brunSupport Z (2*j+1)
  calc
    _=∑ p∈I,∑ d∈R,brunPairCoefficient Z j g1 g2 d*
        (alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V)*divisorIndicator d.1 p.1*divisorIndicator d.2 p.2*
          MellinInsertion20261028.residueKernel q N (short*p.1*p.2)) := by
      unfold polyDelta
      simp_rw [polynomial_pair]
      simp only [I,R,Finset.sum_product,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      ring
    _=∑ d∈R,brunPairCoefficient Z j g1 g2 d*
        ∑ p∈I,alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V)*divisorIndicator d.1 p.1*divisorIndicator d.2 p.2*
          MellinInsertion20261028.residueKernel q N (short*p.1*p.2) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _=_ := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      obtain ⟨hd1,hd2⟩ := Finset.mem_product.mp hd
      rw [I,Finset.sum_product,pair_divisor_substitution hU hV
        (brunSupport_bounds hZ _ hd1).1 (brunSupport_bounds hZ _ hd2).1 F G hF hG alpha short,
        ←fixedMCore_eq_kernel]

theorem polynomial_P2 (F G : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    (hG : Function.support (G:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (short N q : ℕ) (hq : 0<q) (hsq : Squarefree q)
    (hN : N.Coprime q) (alpha : ℂ) :
    ‖polyDelta F G U V Z j g1 g2 short N q alpha‖≤
      p2Price F G*((Z^(2*j+1))^2*‖alpha‖)*modulusBudget q := by
  rw [polynomial_expansion F G hF hG hU hV hZ]
  let R := brunSupport Z (2*j+1) ×ˢ brunSupport Z (2*j+1)
  have H (d : ℕ×ℕ) (hd : d∈R) :
      ‖fixedMCore (wideWindow (U/d.1)) (wideWindow (V/d.2)) (short*d.1*d.2) N q alpha F G (U/d.1) (V/d.2)‖≤
        p2Price F G*‖alpha‖*modulusBudget q := by
    have h1 : (0:ℝ)<d.1 := by exact_mod_cast (brunSupport_bounds hZ _ (Finset.mem_product.mp hd).1).1
    have h2 : (0:ℝ)<d.2 := by exact_mod_cast (brunSupport_bounds hZ _ (Finset.mem_product.mp hd).2).1
    have hp := P4BOriginalSquarefreeP2.naturalCore_P2 hsq F G hF hG
      (div_pos hU h1) (div_pos hV h2) (short*d.1*d.2) N hq hN alpha
    simpa only [p2Price,mul_assoc,mul_left_comm,mul_comm] using hp
  calc
    _≤∑ d∈R,‖brunPairCoefficient Z j g1 g2 d‖*(p2Price F G*‖alpha‖*modulusBudget q) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (H d hd) (norm_nonneg _)
    _=(p2Price F G*modulusBudget q)*∑ d∈R,‖brunPairCoefficient Z j g1 g2 d‖*‖alpha‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _≤(p2Price F G*modulusBudget q)*((Z^(2*j+1))^2*‖alpha‖) :=
      mul_le_mul_of_nonneg_left (brunPair_mass hZ j g1 g2 alpha)
        (mul_nonneg (p2Price_nonneg F G) (modulusBudget_nonneg q))
    _=_ := by ring

end
end ImbalancedChen.P4BOriginalEnvelopePolynomialPayment

