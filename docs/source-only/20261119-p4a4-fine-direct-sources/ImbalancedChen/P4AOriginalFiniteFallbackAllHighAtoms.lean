import ImbalancedChen.P4AOriginalFiniteFallbackCommonGroups
import ImbalancedChen.P4AOriginalFiniteFallbackPPSchedule

namespace ImbalancedChen.P4AOriginalFiniteFallbackAllHighAtoms
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackPolicy (F)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4AOriginalFiniteFallbackPhysicalSelected (word representative)
open P4AOriginalFiniteFallbackCommonGroups (gap groupsAt)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AHeldTaggedCompilerSupport (J0)
open P4AUpperTaggedParityCompiler (rawSupport cell coefficient)
open P4AOriginalFull87RawChronology (cutoff)

def HighAtoms (m n N : ℕ) (delta w tau ell eta : ℝ) (d : OriginalData) : Prop :=
  let f := F (bank m) delta n d w N
  let W := (N:ℝ)^w
  let z := cutoff N
  let rho := P4AUpperTaggedBetaAttachment.rho f (fun _ => []) N N W z tau ((N:ℝ)^ell)
  ∀ q : ℕ,rho q≠0 → ∃ a b u : ℕ,a*b=q ∧ (a:ℝ)<(N:ℝ)^ell ∧
    coefficient f (fun _ => []) N N W z tau b≠0 ∧ u∈rawSupport f N N W z ∧
    u∈cell (fun _ => []) N N W z tau b ∧ word N tau u=word N tau b ∧
    u=P4AOriginalFiniteFallbackPhysicalSelected.pick f N N W z tau (P4AUpperTaggedParityCompiler.primeWordLabel N tau b) ∧
    ∀ (p : Fin 3 → ℕ) (tail : List ℕ),u.primeFactorsList.reverse=front p tail →
    VariableEnvelope.mu<actualPrimeTupleLog N p 0 → ∀ x kappa U : ℝ,1<x → kappa≤eta →
      x^(1-eta)≤N → (N:ℝ)≤x^(1+eta) → x^(2*eta)≤U → U≤x^(1/3+eta/2) →
        let abc := groupsAt m N d w tau x U eta p (word N tau b)
        let Q3 := abc.2.2*x^(2*ell)
        (a:ℝ)≤x^(2*ell) ∧ abc.1<U*x^(-eta/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(eta/100)) ∧
          x^(7*(1+3*kappa)/32)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(eta/100)) ∧
          U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(eta/100))

theorem high_atoms (m n N : ℕ) (delta w tau ell eta : ℝ) (d : OriginalData) (hd : 0<delta) (he : 0≤d.e)
    (hN : 1<N) (hw : 0<w) (ht : 0<tau) (heta : 0<eta) (hsmall : eta≤gap m d)
    (hbudget : tau*((J0 w:ℝ)+1)≤eta) (hell : 0≤ell) (hell' : 2*ell≤eta/16) :
    HighAtoms m n N delta w tau ell eta d := by
  intro q hq
  obtain ⟨a,b,u,hp,hb,hc,hu,hcell,hword,hpick⟩ := representative m n N N delta w (cutoff N) tau ((N:ℝ)^ell) d hq
  refine ⟨a,b,u,hp,hb,hc,hu,hcell,hword,hpick,?_⟩
  intro p tail hp' hhigh x kappa U hx hk hlo hhi hU0 hU1
  exact P4AOriginalFiniteFallbackCommonGroups.high m n N N u b a delta w tau ell d
    hd he hN hw ht heta hsmall hbudget hu hword hb hell hell' p tail hp' hhigh hx hk hlo hhi hU0 hU1

end
end ImbalancedChen.P4AOriginalFiniteFallbackAllHighAtoms
