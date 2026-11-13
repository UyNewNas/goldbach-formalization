import ImbalancedChen.P4BOriginalHigherLowTensor

/-! A grouping changes only the order of the clipped modulus occurrences.
Its only law is a permutation of the original word. All analytic functions,
weights, modulus support and the signed collision row remain physical. -/
namespace ImbalancedChen.P4BOriginalHigherWordGrouping
noncomputable section
open scoped BigOperators
open Classical
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowBins (Groups)
open P4BOriginalHigherLowTensor (word whole_word restore)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalMediumAtomFamily (support)
open P4BOriginalCollisionThirdFactor (factor gamma thirdSupport)

structure Rule where
  split : Params→ℝ→ℝ→ℝ→List ℕ→Groups
  perm : ∀(P : Params),1<P.N → ∀x U z J,J∈P.words → let S := split P x U z J
    (S.1++(S.2.1++S.2.2)).Perm J

def historical : Rule := ⟨P4BOriginalHigherLowBins.split,by
  intro P _ x U z J hJ; exact P4BOriginalHigherLowBins.split_perm P x U z hJ⟩

namespace Rule
variable (rule : Rule)

theorem complete (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℝ) :
    (∑ J∈P.words,word P J (rule.split P x U z J) F)=∑ q∈products P,free P q*F q := by
  refine Eq.trans ?_ (P4BOriginalHigherLowTensor.complete P hN x U z F)
  apply Finset.sum_congr rfl; intro J hJ
  rw [whole_word P J _ (rule.perm P hN x U z J hJ),whole_word P J _ (P4BOriginalHigherLowBins.split_perm P x U z hJ)]

theorem complex_complete (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℂ) :
    (∑ q∈products P,(free P q:ℂ)*F q)=
    ∑ J∈P.words,let S := rule.split P x U z J
      (restore P J S:ℂ)*∑ a∈support P S.1,∑ b∈support P S.2.1,∑ c∈thirdSupport P J S.2.2,
        (factor P S.1 a:ℂ)*(factor P S.2.1 b:ℂ)*(gamma P J S.2.2 c:ℂ)*F (a*b*c) := by
  apply Complex.ext
  · simpa only [word,Complex.re_sum,←Complex.ofReal_mul,Complex.re_ofReal_mul]
      using (rule.complete P hN x U z (fun q => (F q).re)).symm
  · simpa only [word,Complex.im_sum,←Complex.ofReal_mul,Complex.im_ofReal_mul]
      using (rule.complete P hN x U z (fun q => (F q).im)).symm

end Rule
end
end ImbalancedChen.P4BOriginalHigherWordGrouping
