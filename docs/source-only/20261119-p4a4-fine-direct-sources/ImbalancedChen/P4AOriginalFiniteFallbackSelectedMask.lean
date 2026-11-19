import ImbalancedChen.P4AOriginalFiniteFallbackSelectedSupport

namespace ImbalancedChen.P4AOriginalFiniteFallbackSelectedMask
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackOwnCubeRows (pairPoint)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third)
open P4AFallbackCanonicalBanks (bank second_some_iff third_some_iff meshCell_subset_closedBox)
open P4AFallbackUniformMargins (uniformMargin second_uniform_cap_margin third_uniform_cap_margin)
open P4AOriginalFiniteFallbackSelectedSupport (data_of_word)
open P4AUpperTaggedParityCompiler (rawSupport)
open P5OriginalCommonRefinedConstructor (OriginalData)
open VariableEnvelope

inductive Mask | second | third

def front (p : Fin 3 → ℕ) (tail : List ℕ) := p 0::p 1::p 2::tail
def selected (b : Mask) (p : Fin 3 → ℕ) : List ℕ := match b with
  | .second => [p 1]
  | .third => [p 1,p 2]
def remaining (b : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) : List ℕ := match b with
  | .second => p 0::p 2::tail
  | .third => p 0::tail
def exponent (b : Mask) (t : Fin 3 → ℝ) : ℝ := match b with
  | .second => t 1
  | .third => t 1+t 2
def value (m : ℕ) (b : Mask) (N : ℕ) (p : Fin 3 → ℕ) := match b with
  | .second => read m (bank m).second (pairPoint N p)
  | .third => read m (bank m).third (actualPrimeTupleLog N p)

theorem perm (b : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) :
    (selected b p++remaining b p tail).Perm (front p tail) := by
  cases b
  · exact List.Perm.swap _ _ _
  · exact ((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _)

theorem support (m n N cap u : ℕ) (delta w z : ℝ) (d : OriginalData) (hN : 1<N)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (b : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) (ht : u.primeFactorsList.reverse=front p tail)
    {M : ℚ} (hit : value m b N p=some M) :
    let s := exponent b (actualPrimeTupleLog N p)
    let S := selected b p
    let T := remaining b p tail
    0≤s ∧ s≤1 ∧ 1/2≤(M:ℝ) ∧ (M:ℝ)≤299/500 ∧ (M:ℝ)+uniformMargin m≤v s ∧
    ((N:ℝ)^s=(S.prod:ℝ)) ∧ actualDwellSupport ((N:ℝ)^(M:ℝ)) (front p tail) ∧
      actualDwellSupport (((N:ℝ)^(M:ℝ))/(S.prod:ℝ)) T := by
  dsimp only
  obtain ⟨hp,hs,_⟩ := data_of_word hu p tail ht
  have pos (i : Fin 3) : 0≤actualPrimeTupleLog N p i := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hp i)) (Real.log_nonneg (by exact_mod_cast hN.le))
  have ha := (actualPrimeTupleLog_strictAnti_iff hN p hp).mpr hs
  have hy := ha (by decide : (0:Fin 3)<1)
  have hz := ha (by decide : (1:Fin 3)<2)
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  cases b with
  | second =>
    obtain ⟨j,hj,hr⟩ := read_some_iff.mp hit
    obtain ⟨hg,rfl⟩ := (second_some_iff m j _).mp hr
    have h := second_uniform_cap_margin m j hg _ (meshCell_subset_closedBox _ _ hj)
    have H := selected_second hit
    have hh := H.1.2.1
    change actualPrimeTupleLog N p 0<19/96 at hh
    refine ⟨pos _,by change actualPrimeTupleLog N p 1≤1; linarith,H.2.2.2.2.1.le,H.2.2.2.1.le,h.2.2.2.2.1,?_,?_⟩
    · simpa [exponent,selected] using actualPrimeTupleLog_rpow hN p hp 1
    · simpa [selected,remaining,front] using P4AOriginalFiniteFallbackSelectedSupport.pair hN hu p tail ht hit
  | third =>
    obtain ⟨j,hj,hr⟩ := read_some_iff.mp hit
    obtain ⟨hg,rfl⟩ := (third_some_iff m j _).mp hr
    have h := third_uniform_cap_margin m j hg _ (meshCell_subset_closedBox _ _ hj)
    have H := selected_third hit
    have hh := H.1.2.1
    change actualPrimeTupleLog N p 0<19/96 at hh
    refine ⟨add_nonneg (pos _) (pos _),by change _+_≤(1:ℝ); linarith,H.2.2.2.2.2.1.le,H.2.2.2.2.1.le,h.2.2.2.2.1,?_,?_⟩
    · simp [exponent,selected,Real.rpow_add hNr,actualPrimeTupleLog_rpow hN p hp]
    · simpa [selected,remaining,front] using P4AOriginalFiniteFallbackSelectedSupport.triple hN hu p tail ht hit

end
end ImbalancedChen.P4AOriginalFiniteFallbackSelectedMask
