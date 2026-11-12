import ImbalancedChen.P4AOriginalFiniteFallbackSelectedMask
import ImbalancedChen.OriginalSelectedEndpointQuotientInflation
import ImbalancedChen.P4BUpperCommonBetaMonomials
import ImbalancedChen.P4BUpperSelectedBoxCapacity

namespace ImbalancedChen.P4AOriginalFiniteFallbackNaturalEndpoints
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackSelectedMask (Mask front selected remaining exponent value)
open P4BUpperSelectedBoxCapacity (endpoint)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AFallbackCanonicalBanks (bank)
open P4AFallbackUniformMargins (uniformMargin)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler (rawSupport)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AHeldTaggedCompilerSupport (J0)
open OriginalSelectedEndpointQuotientInflation20261026b (selected_endpoint_quotient_support)

def tag (N : ℕ) (tau : ℝ) (p : ℕ) := (P2LowerFiniteCellRounding.primeLabel N tau p).toNat
def upper (N : ℕ) (tau : ℝ) (p : ℕ) := actualPrimeFineLabelIntegerUpper N tau (tag N tau p)

theorem power_scale {N p : ℕ} (hn : 1<N) (hp : 0<p) :
    (N:ℝ)^(Real.log (p:ℝ)/Real.log (N:ℝ))=(p:ℝ) := by
  simpa [actualPrimeTupleLog] using
    actualPrimeTupleLog_rpow hn (fun _ : Fin 1 => p) (fun _ => hp) 0

theorem interval {N p : ℕ} (hn : 1<N) {tau : ℝ} (ht : 0<tau) (hp : p.Prime) (hc : ¬p∣N) :
    p∈actualPrimeFineLabelFinset N tau (tag N tau p) := by
  let t := Real.log (p:ℝ)/Real.log (N:ℝ)
  have H : 0≤t/tau := div_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hp.pos))
    (Real.log_nonneg (by exact_mod_cast hn.le))) ht.le
  have he : (tag N tau p:ℝ)=(⌊t/tau⌋:ℤ) := by
    dsimp [tag,P2LowerFiniteCellRounding.primeLabel,t]; exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr H)
  have hl := (le_div_iff₀ ht).mp (Int.floor_le (t/tau))
  have hu := (div_lt_iff₀ ht).mp (Int.lt_floor_add_one (t/tau))
  have hNr : (1:ℝ)<N := by exact_mod_cast hn
  apply mem_actualPrimeFineLabelFinset.mpr
  refine ⟨hp,hc,?_,?_⟩
  · rw [←power_scale hn hp.pos,←show t=Real.log (p:ℝ)/Real.log (N:ℝ) from rfl]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    rw [he,mul_comm]; exact hl
  · rw [←power_scale hn hp.pos,←show t=Real.log (p:ℝ)/Real.log (N:ℝ) from rfl]
    apply Real.rpow_lt_rpow_of_exponent_lt hNr
    rw [he,mul_comm]; exact hu

theorem endpoint_bounds {N p : ℕ} (hn : 1<N) {tau : ℝ} (ht : 0<tau) (hp : p.Prime) (hc : ¬p∣N) :
    p≤upper N tau p ∧ (upper N tau p:ℝ)≤(N:ℝ)^tau*(p:ℝ) := by
  have hi := interval hn ht hp hc
  have hx : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  refine ⟨actualPrimeFineLabelFinset_le_integerUpper hi,(actualPrimeFineLabelIntegerUpper_le_power _ _ _).trans ?_⟩
  rw [mul_add,mul_one,Real.rpow_add hx,mul_comm ((N:ℝ)^(_*_))]
  exact mul_le_mul_of_nonneg_left (mem_actualPrimeFineLabelFinset.mp hi).2.2.1 (Real.rpow_nonneg hx.le _)

theorem power_of_slots (S : List ℕ) (N : ℕ) (tau : ℝ) (h : ∀p∈S,(upper N tau p:ℝ)≤(N:ℝ)^tau*(p:ℝ))
    (hN : 0<(N:ℝ)) :
    endpoint (upper N tau) S≤(N:ℝ)^(tau*(S.length:ℝ))*(S.prod:ℝ) := by
  induction S with
  | nil => simp [endpoint]
  | cons p ps ih =>
    have hh := mul_le_mul (h p (by simp)) (ih (fun x hx => h x (by simp [hx])))
      (by rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]; exact Nat.cast_nonneg _) (by positivity)
    simp only [endpoint,List.map_cons,List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_mul,
      mul_add,mul_one,Real.rpow_add hN] at *
    linarith only [show (upper N tau p:ℝ)*(List.map (fun q => (upper N tau q:ℝ)) ps).prod≤
      ((N:ℝ)^tau*(p:ℝ))*((N:ℝ)^(tau*(ps.length:ℝ))*(ps.prod:ℝ)) from hh,
      show ((N:ℝ)^tau*(p:ℝ))*((N:ℝ)^(tau*(ps.length:ℝ))*(ps.prod:ℝ))=
        ((N:ℝ)^(tau*(ps.length:ℝ))*(N:ℝ)^tau)*((p:ℝ)*(ps.prod:ℝ)) by ring]

theorem general_endpoint_support (m n N cap u : ℕ) (delta w z tau eta : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    (hbudget : tau*((J0 w:ℝ)+1)≤eta)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (S T V : List ℕ) (hword : u.primeFactorsList.reverse=V) (hpart : (S++T).Perm V)
    (M s : ℝ) (hpow : (N:ℝ)^s=(S.prod:ℝ)) (hfull : actualDwellSupport ((N:ℝ)^M) V)
    (hrest : actualDwellSupport (((N:ℝ)^M)/(S.prod:ℝ)) T) :
    let E := endpoint (upper N tau) S
    (N:ℝ)^s≤E ∧ E≤(N:ℝ)^(s+eta) ∧
    actualDwellSupport ((N:ℝ)^(M+eta)) (V.map (upper N tau)) ∧
    actualDwellSupport (((N:ℝ)^(M+eta))/E) (T.map (upper N tau)) ∧
    ∀q∈V,0<upper N tau q := by
  obtain ⟨hU,_⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ _ hU).1
  rw [hword] at hsub
  have pri (q : ℕ) (hq : q∈V) := mem_roughPrimeUniverse.mp (hsub.subset hq)
  have bounds (q : ℕ) (hq : q∈V) := endpoint_bounds hN ht (pri q hq).2.1 (pri q hq).2.2.1
  have pos (q : ℕ) (hq : q∈V) := (pri q hq).2.1.pos
  have hr := (P4AOriginalFiniteFallbackRange.raw_range (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m)
    delta hd n d he w N cap (by omega) w z hw hu).1
  have hlen : V.length≤J0 w := by rw [←hword,List.length_reverse]; exact hr.le
  have Hlen : (S++T).length=V.length := hpart.length_eq
  have hl : S.length+T.length≤J0 w := by rw [←List.length_append,Hlen]; exact hlen
  have hST (q : ℕ) (hq : q∈S++T) : q∈V := hpart.mem_iff.mp hq
  have hS (q : ℕ) (hq : q∈S) : q∈V := hST q (List.mem_append_left _ hq)
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hlevel : (M:ℝ)+tau*((J0 w:ℝ)+1)≤M+eta := by linarith
  have H := selected_endpoint_quotient_support hn ht.le S T (upper N tau) (fun q hq => pos q (hS q hq))
    (fun q hq => (bounds q (hS q hq)).1) (fun q hq => (bounds q (hST q hq)).2) hl hrest hlevel
  refine ⟨?_,?_,?_,?_,fun q hq => (pos q hq).trans_le (bounds q hq).1⟩
  · rw [hpow,P4BUpperSelectedBoxCapacity.endpoint_eq_cast]
    exact_mod_cast H.1
  · have hh := power_of_slots S N tau (fun q hq => (bounds q (hS q hq)).2) (zero_lt_one.trans hn)
    have ha : (S.length:ℝ)≤J0 w := by exact_mod_cast (show S.length≤J0 w by omega)
    rw [←hpow,←Real.rpow_add (zero_lt_one.trans hn)] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by nlinarith [ht.le]))
  · exact actualDwellSupport_upper_inflation hn ht.le id (upper N tau) V hlen (fun q hq => (bounds q hq).2)
      (by simpa using hfull) hlevel
  · simpa only [P4BUpperSelectedBoxCapacity.endpoint_eq_cast] using H.2.2

theorem endpoint_support (m n N cap u : ℕ) (delta w z tau eta : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    (hbudget : tau*((J0 w:ℝ)+1)≤eta)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (b : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) (hword : u.primeFactorsList.reverse=front p tail)
    {M : ℚ} (hit : value m b N p=some M) :
    let s := exponent b (actualPrimeTupleLog N p)
    let S := selected b p
    let T := remaining b p tail
    let V := front p tail
    let E := endpoint (upper N tau) S
    0≤s ∧ s≤1 ∧ 1/2≤(M:ℝ) ∧ (M:ℝ)≤299/500 ∧ (M:ℝ)+uniformMargin m≤VariableEnvelope.v s ∧
    (N:ℝ)^s≤E ∧ E≤(N:ℝ)^(s+eta) ∧
    actualDwellSupport ((N:ℝ)^((M:ℝ)+eta)) (V.map (upper N tau)) ∧
    actualDwellSupport (((N:ℝ)^((M:ℝ)+eta))/E) (T.map (upper N tau)) ∧
    ∀q∈V,0<upper N tau q := by
  obtain ⟨hs,hs1,hM,hM1,hmarg,hpow,hfull,hrest⟩ :=
    P4AOriginalFiniteFallbackSelectedMask.support m n N cap u delta w z d hN hu b p tail hword hit
  exact ⟨hs,hs1,hM,hM1,hmarg,general_endpoint_support m n N cap u delta w z tau eta d hd he hN hw ht
    hbudget hu _ _ _ hword (P4AOriginalFiniteFallbackSelectedMask.perm b p tail) M _ hpow hfull hrest⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackNaturalEndpoints
