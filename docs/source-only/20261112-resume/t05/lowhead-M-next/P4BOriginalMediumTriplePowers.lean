import ImbalancedChen.P4BOriginalMediumLowTriple

/-! Natural fine-box endpoints on the actual local HB product scale. -/
namespace ImbalancedChen.P4BOriginalMediumTriplePowers
noncomputable section
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag upper endpoint_bounds)
open P4AOriginalFiniteFallbackOwnCubeRows (old)
open P4AOriginalNewFifthUnion (data)
open P4BOriginalMediumLowTriple (actual_third actual_cap_lower)
open VariableEnvelope (mu)

def power (x a : ℝ) := Real.log a/Real.log x

theorem power_mono {x a b : ℝ} (hx : 1<x) (ha : 0<a) (hab : a≤b) :
    power x a≤power x b :=
  div_le_div_of_nonneg_right (Real.log_le_log ha hab) (Real.log_pos hx).le

theorem power_one (x : ℝ) : power x 1=0 := by simp [power]

theorem power_mul {x a b : ℝ} (ha : 0<a) (hb : 0<b) :
    power x (a*b)=power x a+power x b := by simp only [power,Real.log_mul ha.ne' hb.ne',add_div]

theorem power_pow {x a : ℝ} (n : ℕ) : power x (a^n)=n*power x a := by
  simp only [power,Real.log_pow]
  ring

theorem power_rpow {x a : ℝ} (ha : 0<a) (r : ℝ) : power x (a^r)=r*power x a := by
  simp only [power,Real.log_rpow ha]
  ring

theorem power_base {x : ℝ} (hx : 1<x) (r : ℝ) : power x (x^r)=r := by
  rw [power_rpow (zero_lt_one.trans hx)]
  simp [power,(Real.log_pos hx).ne']

theorem upper_iff {x a r : ℝ} (hx : 1<x) (ha : 0<a) : a≤x^r ↔ power x a≤r :=
  (Real.le_rpow_iff_log_le ha (zero_lt_one.trans hx)).trans (div_le_iff₀ (Real.log_pos hx)).symm

theorem strict_iff {x a r : ℝ} (hx : 1<x) (ha : 0<a) : a<x^r ↔ power x a<r := by
  rw [Real.lt_rpow_iff_log_lt ha (zero_lt_one.trans hx)]
  exact (div_lt_iff₀ (Real.log_pos hx)).symm

theorem cap_power {x U zeta : ℝ} (hx : 1<x) (hU : 0<U) :
    power x (U/x^zeta)=power x U-zeta := by
  have h := power_mul (x:=x) (div_pos hU (Real.rpow_pos_of_pos (zero_lt_one.trans hx) zeta))
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx) zeta)
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hx) zeta).ne',power_base hx] at h
  linarith

theorem positive_le_iff {x a b : ℝ} (hx : 1<x) (ha : 0<a) (hb : 0<b) :
    a≤b ↔ power x a≤power x b := by
  unfold power
  rw [div_le_div_iff_of_pos_right (Real.log_pos hx),Real.log_le_log_iff ha hb]

abbrev hi (P : Params) (p : Fin 3→ℕ) (i : Fin 3) : ℝ := upper P.N P.T (p i)

/-- The strict source cube absorbs rounding of all five occurrences,
including the three copies of the last prime. -/
theorem original_endpoints (P : Params) (hN : 1<P.N) (he : 0≤P.e) {J : List ℕ}
    (hJ : J∈P.words) (h3 : J.length=3) {x zeta kappa : ℝ}
    (hx : 1<x) (hNx : (P.N:ℝ)≤x^(1+kappa)) (hk : kappa≤zeta)
    (hz : zeta≤1/20000) (hT : P.T≤zeta)
    (hl : actualPrimeTupleLog P.N (ownerHead P J) 0≤mu) :
    let p := ownerHead P J
    let t := actualPrimeTupleLog P.N p
    let a := fun i => power x (hi P p i)
    (∀ i,0<hi P p i) ∧ (∀ i,a i≤49/250) ∧ a 0+a 1+3*a 2≤3/5 ∧ a 0≤t 0+1/1000 := by
  let p := ownerHead P J
  let t := actualPrimeTupleLog P.N p
  obtain ⟨_,hprime,hs,hc⟩ := actual_third P hN he hJ h3
  let a := fun i => power x (hi P p i)
  have hNr : (1:ℝ)<P.N := by exact_mod_cast hN
  have ht0 (i : Fin 3) : 0≤t i := div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime i).1.pos))
    (Real.log_pos hNr).le
  have ht1 (i : Fin 3) : t i≤mu := (hs.antitone (Fin.zero_le i)).trans hl
  have close (i : Fin 3) : a i≤t i+1/10000 := by
    have helem := (endpoint_bounds hN P.T_pos (hprime i).1 (hprime i).2).2
    have heq := actualPrimeTupleLog_rpow hN p (fun k => (hprime k).1.pos) i
    have hp : 0<hi P p i := by exact_mod_cast ((hprime i).1.pos.trans_le
      (endpoint_bounds hN P.T_pos (hprime i).1 (hprime i).2).1)
    apply (upper_iff hx hp).mp
    calc
      hi P p i ≤ (P.N:ℝ)^(P.T+t i) := by rw [Real.rpow_add (zero_lt_one.trans hNr),heq]; exact helem
      _ ≤ (x^(1+kappa))^(P.T+t i) := Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (add_nonneg P.T_pos.le (ht0 i))
      _ = x^((1+kappa)*(P.T+t i)) := (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
      _ ≤ x^(t i+1/10000) := by
        apply Real.rpow_le_rpow_of_exponent_le hx.le
        have H := mul_le_mul_of_nonneg_right (hk.trans hz) (add_nonneg P.T_pos.le (ht0 i))
        have Ht := ht1 i
        dsimp only [mu] at Ht
        nlinarith only [H,Ht,hT,hz]
  have sharper (i : Fin 3) : a i≤49/250 := by
    have H := ht1 i
    dsimp only [mu] at H
    linarith only [H,close i]
  have cube : a 0+a 1+3*a 2≤3/5 := by linarith only [close 0,close 1,close 2,hc]
  exact ⟨fun i => by exact_mod_cast ((hprime i).1.pos.trans_le
    (endpoint_bounds hN P.T_pos (hprime i).1 (hprime i).2).1),sharper,cube,by linarith only [close 0]⟩

end
end ImbalancedChen.P4BOriginalMediumTriplePowers
