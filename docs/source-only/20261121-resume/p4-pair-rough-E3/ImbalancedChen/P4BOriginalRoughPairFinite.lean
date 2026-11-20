import ImbalancedChen.P4BOriginalTwiceMeanPayment
import ImbalancedChen.P5ActualHBRoughBrunFinite
import ImbalancedChen.Part3TwoLongBrunComplexGap

/-! SOURCE ONLY / UNCOMPILED. Actual finite E3, before any q-sum.
The complex source is majorized inside the positive count+mean sum,
THEN split into a signed gap discrepancy and TWICE the exact mean. -/
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
