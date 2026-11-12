import ImbalancedChen.P4BOriginalHigherLowBins
import ImbalancedChen.P4BOriginalMediumScheduledInventory

/-! Regroup the actual unrestricted physical word, preserving its original
small Rosser and its one signed multiplicity. The arithmetic functional
is arbitrary and evaluated at the complete modulus. -/
namespace ImbalancedChen.P4BOriginalHigherLowTensor
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalHigherLowBins (Groups split split_perm)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionThirdFactor (splitAt tensor tensor_eq factor gamma thirdSupport gamma_apply)
open P4BOriginalMediumAtomFamily (support)
open P4BOriginalCollisionTensor (products free)

def restore (P : Params) (J : List ℕ) (S : Groups) : ℝ :=
  P.scalar J*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ)*(-1:ℝ)^J.length

def word (P : Params) (J : List ℕ) (S : Groups) (F : ℕ→ℝ) : ℝ :=
  restore P J S*∑ a∈support P S.1,∑ b∈support P S.2.1,∑ c∈thirdSupport P J S.2.2,
    factor P S.1 a*factor P S.2.1 b*gamma P J S.2.2 c*F (a*b*c)

theorem whole_word (P : Params) (J : List ℕ) (S : Groups)
    (hp : (S.1++(S.2.1++S.2.2)).Perm J) (F : ℕ→ℝ) :
    word P J S F=∑ h∈P.A,∑ ps∈P.bins J,P.scalar J*((-1:ℝ)^J.length*(P.small J h*F (h*ps.prod))) := by
  let f := factor P S.1
  let g := factor P S.2.1
  let k := factor P S.2.2
  let R := restore P J S
  let T := fun (h v : ℕ) => (-1:ℝ)^J.length*(P.small J h*F (h*v))
  have per_h (h : ℕ) :
      (∑ ps∈P.bins J,P.scalar J*T h ps.prod)=
      ∑ a∈support P S.1,∑ b∈support P S.2.1,∑ c∈support P S.2.2,
        R*(f a*g b*(P.small J h*k c*F (a*b*(h*c)))) := by
    rw [←actualPrimeSlotBox_product_sum_perm _ hp (fun v => P.scalar J*T h v),
      actualPrimeSlotBox_product_sum_append]
    simp_rw [actualPrimeSlotBox_product_sum_append]
    conv_lhs => simp only [←Nat.mul_assoc]
    rw [actualPrimeTuple_threeGroup_sum_normalized (P.bins S.1) (P.bins S.2.1) (P.bins S.2.2)
      S.1.length S.2.1.length S.2.2.length (P.scalar J) (T h)]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    dsimp [T,R,restore,f,g,k,factor]
    rw [show h*(a*b*c)=a*b*(h*c) by ring]
    ring
  change _=∑ h∈P.A,∑ ps∈P.bins J,P.scalar J*T h ps.prod
  simp_rw [per_h]
  rw [Finset.sum_comm (s:=P.A) (t:=support P S.1)]
  unfold word; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm (s:=P.A) (t:=support P S.2.1),Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  change R*(∑ c∈thirdSupport P J S.2.2,f a*g b*gamma P J S.2.2 c*F (a*b*c))=_
  have h := gamma_apply P J S.2.2 (fun c => F (a*b*c))
  calc
    _=R*(f a*g b)*(∑ c∈thirdSupport P J S.2.2,gamma P J S.2.2 c*F (a*b*c)) := by
      simp only [Finset.mul_sum,mul_assoc]
    _=_ := by rw [←h]; simp only [support,Finset.mul_sum,k,mul_assoc]

theorem same_word (P : Params) (x U z : ℝ) {J} (hJ : J∈P.words) (F : ℕ→ℝ) :
    word P J (split P x U z J) F=word P J (splitAt P x U z J) F := by
  rw [whole_word P J _ (split_perm P x U z hJ),whole_word P J _ (P4AOriginalFiniteFallbackGroupedAtoms.partition
    P.m P.N _ P.omega P.T x U z _ J (Finset.mem_filter.mp hJ).2)]

theorem complete (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℝ) :
    (∑ J∈P.words,word P J (split P x U z J) F)=∑ q∈products P,free P q*F q :=
  (Finset.sum_congr rfl (fun J hj => same_word P x U z hj F)).trans (tensor_eq P hN x U z F)

theorem complete_signed (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℝ) :
    (∑ J∈P.words,word P J (split P x U z J) F)-(∑ q∈P.S,P.rho q*F q)=
      ∑ q∈products P,P4BOriginalCollisionTensor.error P q*F q := by
  rw [complete P hN]
  exact P4BOriginalCollisionTensor.difference P hN F

theorem complex_complete (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℂ) :
    (∑ q∈products P,(free P q:ℂ)*F q)=
    ∑ J∈P.words,let S := split P x U z J
      (restore P J S:ℂ)*∑ a∈support P S.1,∑ b∈support P S.2.1,∑ c∈thirdSupport P J S.2.2,
        (factor P S.1 a:ℂ)*(factor P S.2.1 b:ℂ)*(gamma P J S.2.2 c:ℂ)*F (a*b*c) := by
  apply Complex.ext
  · simpa only [word,Complex.re_sum,←Complex.ofReal_mul,Complex.re_ofReal_mul]
      using (complete P hN x U z (fun q => (F q).re)).symm
  · simpa only [word,Complex.im_sum,←Complex.ofReal_mul,Complex.im_ofReal_mul]
      using (complete P hN x U z (fun q => (F q).im)).symm

end
end ImbalancedChen.P4BOriginalHigherLowTensor
