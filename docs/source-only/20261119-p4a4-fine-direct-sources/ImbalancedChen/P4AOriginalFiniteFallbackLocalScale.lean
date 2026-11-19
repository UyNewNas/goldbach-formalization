import ImbalancedChen.P4AOriginalFiniteFallbackNaturalEndpoints
import ImbalancedChen.P4AOriginalFiniteFallbackOriginalLength

namespace ImbalancedChen.P4AOriginalFiniteFallbackLocalScale
noncomputable section
open scoped Classical
open VariableEnvelope
open P4AOriginalFiniteFallbackSelectedMask (Mask front selected remaining exponent value perm)
open P4AOriginalFiniteFallbackNaturalEndpoints (upper tag)
open P4AFallbackCanonicalBanks (bank)
open P4AFallbackUniformMargins (uniformMargin uniformMargin_pos)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AUpperTaggedParityCompiler (rawSupport)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AHeldTaggedCompilerSupport (J0)
open P4BUpperSelectedBoxCapacity (endpoint endpoints)

def slack (m : ℕ) := min ((uniformMargin m:ℝ)/64) (1/400)
theorem slack_pos (m : ℕ) : 0<slack m := lt_min (div_pos (by exact_mod_cast uniformMargin_pos m) (by norm_num)) (by norm_num)

theorem bridge {N x M s E eta sigma kappa : ℝ} (hx : 1<x) (hN : 0<N)
    (he : 0<eta) (he' : eta≤1/400) (hmargin : 64*eta≤sigma) (hk : kappa≤eta)
    (hlo : x^(1-eta)≤N) (hhi : N≤x^(1+eta)) (hs : 0≤s) (hs' : s≤1)
    (hM : 1/2≤M) (hM' : M≤299/500) (hgate : M+sigma≤v s)
    (hE : N^s≤E) (hE' : E≤N^(s+eta)) :
    N^(M+eta)≤x^(M+4*eta) ∧
    x^(2*(M+6*eta)-1)≤E ∧ E≤x^actualSelectedSubproductUpper (1+3*kappa) (M+6*eta) := by
  have hx0 := zero_lt_one.trans hx
  have hg := (actualSelectedSubproduct_critical_iff 1 (M+sigma) s).mp (by rwa [actualSelectedSubproductV_one])
  have hsub1 := hg.2.trans (min_le_left _ _)
  have hsub2 := hg.2.trans (min_le_right _ _)
  change s≤(32-39*(M+sigma))/34 at hsub1
  change s≤(2-2*(M+sigma)-7*1/32)/3 at hsub2
  have lo (a b : ℝ) (hb : 0≤b) (hab : a≤(1-eta)*b) : x^a≤N^b := by
    calc
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le hab
      _ = (x^(1-eta))^b := Real.rpow_mul hx0.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hlo hb
  have hi (a b : ℝ) (ha : 0≤a) (hab : (1+eta)*a≤b) : N^a≤x^b := by
    calc
      _ ≤ _ := Real.rpow_le_rpow hN.le hhi ha
      _ = x^((1+eta)*a) := (Real.rpow_mul hx0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le hab
  have e2 : eta*eta≤eta := by nlinarith [mul_nonneg he.le (show 0≤1-eta by linarith)]
  have es : eta*s≤eta := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hs')]
  have eM : eta*M≤eta := by nlinarith [mul_nonneg he.le (show 0≤1-M by linarith)]
  refine ⟨hi _ _ (by linarith) (by nlinarith), (lo _ _ hs (by nlinarith [hg.1])).trans hE, ?_⟩
  apply hE'.trans (hi _ _ (by linarith) ?_)
  apply le_min <;> nlinarith only [hsub1,hsub2,hmargin,hk,es,e2,he.le]

theorem endpoints_map {α β : Type*} (f : α→β) (U : β→ℕ) (D A : ℝ) (S T V : List α) :
    endpoints D A U (S.map f) (T.map f) (V.map f)=endpoints D A (U∘f) S T V := by
  simp only [endpoints,P4BUpperSelectedBoxCapacity.groups,endpoint,List.map_map,Function.comp_def,
    actualTwoCapacityGreedy_map]
  split_ifs <;> simp only [List.map_map,Function.comp_def]

/-- On a real retained representative the selected mask and all initial
and descendant square inequalities are actual. Allocation is run on
the NATURAL fine labels and their integer upper endpoints. -/
theorem general_local (m n N cap u : ℕ) (delta w z tau : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    {e sigma : ℝ} (hepos : 0<e) (hf : e≤1/400) (hm : 64*e≤sigma) (hbudget : tau*((J0 w:ℝ)+1)≤e)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (S T V : List ℕ) (hword : u.primeFactorsList.reverse=V) (perm' : (S++T).Perm V)
    (M s : ℝ) (hs : 0≤s) (hs' : s≤1) (hM : 1/2≤M) (hM' : M≤299/500)
    (hg : M+sigma≤VariableEnvelope.v s) (hpow : (N:ℝ)^s=(S.prod:ℝ))
    (hfull0 : actualDwellSupport ((N:ℝ)^M) V)
    (hrest0 : actualDwellSupport (((N:ℝ)^M)/(S.prod:ℝ)) T)
    {x kappa A ell : ℝ} (hx : 1<x) (hk : kappa≤e) (hlo : x^(1-e)≤N)
    (hhi : (N:ℝ)≤x^(1+e)) (hA : 1≤A) (hAu : A≤x^(1/3-e/2)) (hell : ell≤e/16) :
    let D := x^(M+4*e)
    let label := tag N tau
    let abc := endpoints D A (actualPrimeFineLabelIntegerUpper N tau) (S.map label) (T.map label) (V.map label)
    let U := A*x^e
    let Q3 := abc.2.2*x^ell
    abc.1<U*x^(-e/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(e/100)) ∧
      x^(7*(1+3*kappa)/32)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(e/100)) ∧
      U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(e/100)) := by
  let H := upper N tau
  let E := endpoint H S
  let theta := M+6*e
  let D := x^(M+4*e)
  obtain ⟨hE,hE',hfull,hrem,hpos⟩ := P4AOriginalFiniteFallbackNaturalEndpoints.general_endpoint_support m n N cap u delta w z tau e d hd he hN hw ht hbudget hu
      S T V hword perm' M s hpow hfull0 hrest0
  have hnr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  obtain ⟨hc,h1,h2⟩ := P4AOriginalFiniteFallbackLocalScale.bridge hx hnr hepos hf hm hk hlo hhi hs hs' hM hM' hg hE hE'
  have eqv : theta-2*e=(M:ℝ)+4*e := by dsimp [theta]; ring
  have hEp : 0<E := P4BUpperSelectedBoxCapacity.endpoint_positive H S
    (fun q hq => hpos q (perm'.mem_iff.mp (List.mem_append_left _ hq)))
  have full : actualDwellSupport (x^(theta-2*e)) (V.map H) := by
    rw [eqv]; exact fun i hi => (hfull i hi).trans hc
  have rest : actualDwellSupport (x^(theta-2*e)/E) (T.map H) := by
    rw [eqv]; exact fun i hi => (hrem i hi).trans (div_le_div_of_nonneg_right hc hEp.le)
  have mon := P4BUpperSelectedBoxCapacity.monomials hx hepos (by linarith) (by dsimp [theta]; linarith)
    (by dsimp [theta]; linarith) H S T V perm' hpos hA hAu full rest h1 h2
  rw [eqv] at mon
  let g := P4BUpperSelectedBoxCapacity.groups D A H S T V
  have pg := P4BUpperSelectedBoxCapacity.groups_partition D A H S T V perm'
  have pos' (l : List ℕ) (hl : ∀q∈l,q∈g.1++(g.2.1++g.2.2)) : 0<endpoint H l :=
    P4BUpperSelectedBoxCapacity.endpoint_positive H l (fun q hq => hpos q (pg.mem_iff.mp (hl q hq)))
  have hpa := pos' g.1 (fun q hq => by simp [hq])
  have hpb := pos' g.2.1 (fun q hq => by simp [hq])
  have hpc := pos' g.2.2 (fun q hq => by simp [hq])
  have Hpaid := P4AOriginalFiniteFallbackOriginalLength.beta_and_length hx hepos hell (zero_lt_one.trans_le hA)
    hpa hpb hpc mon.1 mon.2.1 mon.2.2.1 mon.2.2.2
  dsimp only
  rw [P4AOriginalFiniteFallbackLocalScale.endpoints_map]
  exact Hpaid

theorem selected_local (m n N cap u : ℕ) (delta w z tau : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    {eta : ℝ} (heta : 0<eta) (hsmall : eta≤slack m)
    (hbudget : tau*((J0 w:ℝ)+1)≤eta)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (b : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) (hword : u.primeFactorsList.reverse=front p tail)
    {M : ℚ} (hit : value m b N p=some M)
    {x kappa A ell : ℝ} (hx : 1<x) (hk : kappa≤eta) (hlo : x^(1-eta)≤N)
    (hhi : (N:ℝ)≤x^(1+eta)) (hA : 1≤A) (hAu : A≤x^(1/3-eta/2)) (hell : ell≤eta/16) :
    let e := eta
    let D := x^((M:ℝ)+4*e)
    let label := tag N tau
    let S := (selected b p).map label
    let T := (remaining b p tail).map label
    let V := (front p tail).map label
    let abc := endpoints D A (actualPrimeFineLabelIntegerUpper N tau) S T V
    let U := A*x^e
    let Q3 := abc.2.2*x^ell
    abc.1<U*x^(-e/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(e/100)) ∧
      x^(7*(1+3*kappa)/32)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(e/100)) ∧
      U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(e/100)) := by
  obtain ⟨hs,hs1,hM,hM1,hmargin,hpow,hfull,hrest⟩ :=
    P4AOriginalFiniteFallbackSelectedMask.support m n N cap u delta w z d hN hu b p tail hword hit
  apply general_local m n N cap u delta w z tau d hd he hN hw ht heta
    (hsmall.trans (min_le_right _ _)) _ hbudget hu _ _ _ hword
    (perm b p tail) M _ hs hs1 hM hM1 hmargin hpow hfull hrest hx hk hlo hhi hA hAu hell
  linarith [show eta≤(uniformMargin m:ℝ)/64 from hsmall.trans (min_le_left _ _)]

end
end ImbalancedChen.P4AOriginalFiniteFallbackLocalScale
