import ImbalancedChen.P4AOriginalFiniteFallbackPhysicalSelected
import ImbalancedChen.P4AOriginalFiniteFallbackInheritedFirst

namespace ImbalancedChen.P4AOriginalFiniteFallbackCommonGroups
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackOwnCubeRows (old)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackSelectedMask (Mask front value)
open P4AOriginalFiniteFallbackPhysicalSelected (word upperGroups)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4AOriginalFiniteFallbackLocalScale (slack)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler (rawSupport)
open P4AHeldTaggedCompilerSupport (J0)
open P4BUpperSelectedBoxCapacity (endpoints)

def gap (m : ℕ) (d : OriginalData) := min (slack m) ((d.e:ℝ)/32)
theorem gap_pos (m : ℕ) (d : OriginalData) (he : 0<d.e) : 0<gap m d :=
  lt_min (P4AOriginalFiniteFallbackLocalScale.slack_pos _) (div_pos (by exact_mod_cast he) (by norm_num))

def choice (m N : ℕ) (d : OriginalData) (w : ℝ) (p : Fin 3 → ℕ) : Option Mask × ℝ :=
  match value m .third N p with
  | some c => (some .third,(c:ℝ))
  | none => match value m .second N p with
    | some c => (some .second,(c:ℝ))
    | none => (none,old d w N p)

def groupsAt (m N : ℕ) (d : OriginalData) (w tau x U eta : ℝ) (p : Fin 3 → ℕ) (J : List ℕ) :=
  let g := choice m N d w p
  let D := x^(g.2+4*eta)
  let A := U/x^eta
  match g.1 with
  | some kind => upperGroups N tau D A kind J
  | none => endpoints D A (actualPrimeFineLabelIntegerUpper N tau) (J.take 1) (J.drop 1) J

/-- All high-head words of every rough rank >=3, including both misses.
The last case uses the original whole Gamma box, a selected first
prime, and an inherited margin 2e. The same printed Type II interval
and the primitive beta level apply in all three cases. -/
theorem high (m n N cap u b a : ℕ) (delta w tau ell : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    {eta : ℝ} (heta : 0<eta) (hsmall : eta≤gap m d) (hbudget : tau*((J0 w:ℝ)+1)≤eta)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) ((N:ℝ)^(19/96:ℝ)))
    (hJ : word N tau u=word N tau b) (hbeta : (a:ℝ)<(N:ℝ)^ell) (hell : 0≤ell) (hell' : 2*ell≤eta/16)
    (p : Fin 3 → ℕ) (tail : List ℕ) (hword : u.primeFactorsList.reverse=front p tail)
    (hhigh : VariableEnvelope.mu<actualPrimeTupleLog N p 0)
    {x kappa U : ℝ} (hx : 1<x) (hk : kappa≤eta) (hlo : x^(1-eta)≤N)
    (hhi : (N:ℝ)≤x^(1+eta)) (hU0 : x^(2*eta)≤U) (hU1 : U≤x^(1/3+eta/2)) :
    let abc := groupsAt m N d w tau x U eta p (word N tau b)
    let Q3 := abc.2.2*x^(2*ell)
    (a:ℝ)≤x^(2*ell) ∧ abc.1<U*x^(-eta/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(eta/100)) ∧
      x^(7*(1+3*kappa)/32)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(eta/100)) ∧
      U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(eta/100)) := by
  have hbank : eta≤slack m := hsmall.trans (min_le_left _ _)
  have hR := fun kind (c:ℚ) (hit : value m kind N p=some c) =>
    P4AOriginalFiniteFallbackPhysicalSelected.medium m n N cap u b a delta w ((N:ℝ)^(19/96:ℝ)) tau ell d
      hd he hN hw ht heta hbank hbudget hu hJ hbeta hell hell' kind p tail hword hit hx hk hlo hhi hU0 hU1
  cases h3 : value m .third N p with
  | some c => simpa only [groupsAt,choice,h3] using hR .third c h3
  | none =>
    cases h2 : value m .second N p with
    | some c => simpa only [groupsAt,choice,h3,h2] using hR .second c h2
    | none =>
      let t := actualPrimeTupleLog N p
      let M := old d w N p
      let A := U/x^eta
      let S := [p 0]
      let T := p 1::p 2::tail
      let V := front p tail
      have hx0 := zero_lt_one.trans hx
      have hex := Real.rpow_pos_of_pos hx0 eta
      have hA : 1≤A := (le_div_iff₀ hex).mpr (by
        rw [one_mul]; exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : eta≤2*eta)).trans hU0)
      have hau : A≤x^(1/3-eta/2) := (div_le_iff₀ hex).mpr (by
        rw [←Real.rpow_add hx0,show (1/3:ℝ)-eta/2+eta=1/3+eta/2 by ring]; exact hU1)
      have Ueq : A*x^eta=U := div_mul_cancel₀ _ hex.ne'
      have htol := hbank.trans (min_le_right _ _)
      have hs' : 64*eta≤2*(d.e:ℝ) := by linarith [hsmall.trans (min_le_right _ _)]
      obtain ⟨hs0,hs1,hM,hM',hg,hf,hr⟩ := P4AOriginalFiniteFallbackInheritedFirst.inherited m n N cap u delta w d hN
        (by exact_mod_cast he) hu p tail hword hhigh h2 h3
      obtain ⟨pp,_,_⟩ := P4AOriginalFiniteFallbackSelectedSupport.data_of_word hu p tail hword
      have hpow : (N:ℝ)^(t 0)=(S.prod:ℝ) := by simpa [S,t] using actualPrimeTupleLog_rpow hN p pp 0
      have H := P4AOriginalFiniteFallbackLocalScale.general_local m n N cap u delta w _ tau d hd he hN hw ht
        heta htol hs' hbudget hu S T V hword (List.Perm.refl _) M (t 0) hs0 hs1 hM hM' hg hpow hf
        (by simpa [S,T] using hr) hx hk hlo hhi hA hau hell'
      have J : word N tau b=(front p tail).map (tag N tau) := by rw [←hJ,word,hword]
      dsimp only at H ⊢
      rw [J]
      refine ⟨hbeta.le.trans ?_,?_⟩
      · calc
          (N:ℝ)^ell ≤ (x^(1+eta))^ell := Real.rpow_le_rpow (Nat.cast_nonneg _) hhi hell
          _ = x^((1+eta)*ell) := (Real.rpow_mul hx0.le _ _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le
            (by nlinarith [mul_nonneg (show 0≤1-eta by linarith) hell])
      · simpa only [groupsAt,choice,h3,h2,Ueq] using H

end
end ImbalancedChen.P4AOriginalFiniteFallbackCommonGroups
