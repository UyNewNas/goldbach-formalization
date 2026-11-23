import ImbalancedChen.P5OriginalU5AllMarkCosts
import ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches

/-! Produce the independent, smooth original singleton for the full U5
marked coefficient and its actual unpaid complement. The complete
modulus may exceed the target. Beyond that target the prefix has only
its coprime mean, whose total cost is controlled by the full primorial. -/
namespace ImbalancedChen.P5OriginalU5AllMarkSmoothing
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (Policy moduli integerRho paidModuli remainingPrimitive)
open P5OriginalU5AllMarkCosts
open P5OriginalSingletonLowerTrimPaid
open P5OriginalSharpPrime
open P5OriginalPrimeEndpoint
open P5CanonicalTentNarrowSingletonTransfer

def smoothDiscrepancy (t : ℝ) (B N : ℕ) (e : ℝ) (P : Policy) (Q : Finset ℕ) : ℝ :=
  Part3.primeProductSignedError 1 (2*N) N Q (fun q => (integerRho N e P q : ℝ))
    (fullSmoothWeight t B N)

private theorem beyond_target {N Y q : ℕ} (hYN : Y < N) (hq : N < q) (d : ℕ → ℝ) :
    finiteCongruenceMass (chenPrimePrefix Y) d N q = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
  have hlt : p < N := (mem_chenPrimePrefix.mp hp).1.trans_lt hYN
  have hd := (dvd_sub_iff_modEq_of_le hlt.le).mpr hm
  exact False.elim (by have h := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hd; omega)

/-- One constant for the short part and one primorial constant for the
long part. The numerical bound holds for every physical subcarrier. -/
theorem exists_all_mark_prefix_budget {eps : ℝ} (heps : 0 < eps) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {N Y : ℕ}, 2 ≤ N → Even N → Y < N →
      ∀ (e : ℝ) (P : Policy), smallCutoff N e ≤ cutoff N →
      ∀ Q ⊆ moduli N e P, ∀ d : ℕ → ℝ, (∀ p ∈ chenPrimePrefix Y, |d p| ≤ 1) →
      |∑ q ∈ Q, (integerRho N e P q : ℝ) * finitePrimitiveDiscrepancy
        (chenPrimePrefix Y) d N q| ≤ (Y : ℝ) *
          (C*(N : ℝ)^eps + 4 + (4+D)*Real.log (N : ℝ)) := by
  obtain ⟨C, hC, hshort⟩ := exists_prefix_primitive_budget heps
  obtain ⟨D, hD, hmass⟩ := exists_moduli_reciprocal_mass
  refine ⟨C, D, hC, hD, ?_⟩
  intro N Y hN hev hYN e P hw Q hQ d hd
  let rho := fun q => (integerRho N e P q : ℝ)
  let S := Q.filter (fun q => q ≤ N)
  let T := Q \ S
  have hS : S ⊆ Q := Finset.filter_subset _ _
  have hT : T ⊆ Q := Finset.sdiff_subset
  have hr (q : ℕ) (hq : q ∈ Q) : |rho q| ≤ 1 := (full_modulus_data hN P hw (hQ hq)).2.1
  have hNS : ∀ q ∈ S, q ∈ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (full_modulus_data hN P hw (hQ (hS hq))).1,
      (Finset.mem_filter.mp hq).2⟩
  have hlo := hshort N Y N (chenPrimePrefix Y) S rho d hYN
    (fun _ hp => Finset.mem_Icc.mpr ⟨(mem_chenPrimePrefix.mp hp).2.pos,
      (mem_chenPrimePrefix.mp hp).1⟩) hNS (fun q hq => hr q (hS hq)) hd
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  rw [max_eq_right hNr] at hlo
  have hrec : (∑ q ∈ T, |rho q|/(Nat.totient q : ℝ)) ≤ D * Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ q ∈ T, 1/(Nat.totient q : ℝ) := Finset.sum_le_sum (fun q hq =>
        div_le_div_of_nonneg_right (hr q (hT hq)) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ moduli N e P, 1/(Nat.totient q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun _ hq => hQ (hT hq)) (by intros; positivity)
      _ ≤ _ := hmass N hN hev e P hw
  have hlong : |∑ q ∈ T, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix Y) d N q| ≤
      (Y : ℝ)*(D*Real.log (N : ℝ)) := by
    have heq : (∑ q ∈ T, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix Y) d N q) =
        -(∑ q ∈ T, rho q*(finiteCoprimeMass (chenPrimePrefix Y) d q/(Nat.totient q : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hqN : N < q := by
        by_contra! hn
        exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨hT hq, hn⟩)
      simp only [finitePrimitiveDiscrepancy, beyond_target hYN hqN d, zero_sub, mul_neg]
    rw [heq, abs_neg]
    refine (abs_signed_coprime_mean_le _ T rho d hd).trans ?_
    exact mul_le_mul (by exact_mod_cast primePrefix_card_le Y) hrec
      (Finset.sum_nonneg fun q _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  change |∑ q ∈ Q, rho q * _| ≤ _
  rw [← Finset.sum_sdiff (f := fun q => rho q * finitePrimitiveDiscrepancy
    (chenPrimePrefix Y) d N q) hS]
  exact (abs_add_le _ _).trans ((add_le_add hlong hlo).trans_eq (by ring))

theorem eventually_lower_mark_reserve (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (p : ℕ) (tol : ℝ) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
    ∀ Q ⊆ moduli N e P, ∀ B : ℕ, |lowerReserve t B N Q (fun q => (integerRho N e P q : ℝ))| ≤
      tol*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C, D, hC, hD, hprefix⟩ := exists_all_mark_prefix_budget (show 0 < t/2 by positivity)
  filter_upwards [eventually_originalLowerCut_lt t ht ht1, eventually_ge_atTop (2 : ℕ),
    eventually_powerLog_le_logAccuracy (3*C) (1-t/2) 0 p (by linarith) (tol/3) (by positivity),
    eventually_powerLog_le_logAccuracy 12 (1-t) 0 p (by linarith) (tol/3) (by positivity),
    eventually_powerLog_le_logAccuracy (3*(4+D)) (1-t) 1 p (by linarith) (tol/3)
      (by positivity)] with N hY hN ha hb hc
  intro hev e he he8 P Q hQ B
  let Y := originalLowerCut t N
  let d := lowerTrim N Y (smoothNatural t B N)
  have hlow := hprefix hN hev hY.1 e P (attachment_gates hN he he8).2.2 Q hQ d (by
    intro l hl
    have h := lowerTrim_range_of_le N Y l (smoothNatural t B N) hY.1.le (smooth_range t B N l)
    simpa only [d, abs_of_nonneg h.1] using h.2)
  unfold lowerReserve
  rw [lowerTrim_singleton_eq_prefix (2*N) N Y (hY.1.le.trans (by omega))]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNr := zero_lt_one.trans_le hN1
  have hl := Real.log_nonneg hN1
  have hmul : (N : ℝ)^(1-t) * (N : ℝ)^(t/2) = (N : ℝ)^(1-t/2) := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  calc
    _ ≤ 3*(N : ℝ)^(1-t)*(C*(N : ℝ)^(t/2) + 4 + (4+D)*Real.log (N : ℝ)) :=
      hlow.trans (mul_le_mul_of_nonneg_right hY.2 (by positivity))
    _ = 3*C*(N : ℝ)^(1-t/2) + 12*(N : ℝ)^(1-t) +
        3*(4+D)*(N : ℝ)^(1-t)*Real.log (N : ℝ) := by rw [← hmul]; ring
    _ ≤ _ := by
      simp only [pow_zero, pow_one, mul_one] at ha hb hc
      linarith only [ha, hb, hc]

theorem exists_upper_mark_reserve (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N →
    ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ Q ⊆ moduli N e P, ∀ t : ℝ,
    |upperReserve t (p+3) N Q (fun q => (integerRho N e P q : ℝ))| ≤
      C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨D,hD,hmass⟩ := exists_moduli_reciprocal_mass
  refine ⟨8*(1+D), by positivity, ?_⟩
  filter_upwards [eventually_log_window_cost_le p, eventually_ge_atTop (4 : ℕ)] with N hwin hN
  intro hev e he he8 P Q hQ t
  let B := p+3
  let w := upperWidth B N
  let S := endpointCarrier (2*N) N w
  let Y := originalLowerCut t N
  let sm := smoothNatural t B N
  let rho := fun q => (integerRho N e P q : ℝ)
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl := Real.log_nonneg hN1
  have hw := (attachment_gates hN2 he he8).2.2
  have hW := hwin w (upperWidth_le_original_endpoint B hN2)
  have hlogw : Real.log (w : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases h : w = 0
    · simpa only [h,Nat.cast_zero,Real.log_zero] using hl
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by exact_mod_cast hW.1)
  have hs : S ⊆ chenPrimePrefix (2*N) := Finset.filter_subset _ _
  have hsD (l : ℕ) (hlS : l ∈ S) : l ≠ N ∧ distance N l ≤ w := by
    refine ⟨?_, (Finset.mem_filter.mp hlS).2⟩
    intro hh
    exact chen_not_prime_of_even_four_le hev hN (hh ▸ (mem_chenPrimePrefix.mp (hs hlS)).2)
  have hr (q : ℕ) (hq : q ∈ Q) : |rho q| ≤ 1 := (full_modulus_data hN2 P hw (hQ hq)).2.1
  have hrec : (∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ)) ≤ D * Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ q ∈ Q, 1/(Nat.totient q : ℝ) := Finset.sum_le_sum (fun q hq =>
        div_le_div_of_nonneg_right (hr q hq) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ moduli N e P, 1/(Nat.totient q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hQ (by intros; positivity)
      _ ≤ _ := hmass N hN2 hev e P hw
  have hAP := mul_le_mul_of_nonneg_left ((sum_divisors_card_le_log w).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hlogw 1) (Nat.cast_nonneg _)))
    (by norm_num : (0 : ℝ) ≤ 2)
  have hmean := mul_le_mul (endpoint_card_le S N w hsD) hrec
    (Finset.sum_nonneg fun q _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    (by positivity : 0 ≤ 2*(w : ℝ))
  have hbound := abs_signed_primitive_endpoint_le S Q rho
    (fun l => sharp N l - patched N Y sm l) N w hsD hr (fun l _ =>
      abs_sharp_sub_patched_le_one N Y l sm (smooth_range t B N l))
  have hident := singleton_test_difference_eq_endpoint (2*N) N S Q rho (sharp N)
    (patched N Y sm) hs (sharp_eq_patched_off_endpoint (2*N) N w Y sm
      (fun l _ hlo hd => original_middle hN2 t B l hlo (by omega))
      (fun l _ hhi => original_upper_tail hN2 t B l hhi))
  change |Part3.primeProductSignedError 1 (2*N) N Q rho _ -
    Part3.primeProductSignedError 1 (2*N) N Q rho _| ≤ _
  rw [hident]
  calc
    _ ≤ 2*((w : ℝ)*(1+Real.log (N : ℝ))) + 2*(w : ℝ)*(D*Real.log (N : ℝ)) :=
      hbound.trans (add_le_add hAP hmean)
    _ ≤ ((1+D)/5)*(10*(w : ℝ)*(1+Real.log (N : ℝ))) := by
      nlinarith only [mul_nonneg (Nat.cast_nonneg w) hD.le]
    _ ≤ ((1+D)/5)*(40*(N : ℝ)/(Real.log (N : ℝ))^p) :=
      mul_le_mul_of_nonneg_left hW.2 (by positivity)
    _ = _ := by ring

/-- Both smooth endpoints are paid at the same reported all-mark
coefficient. The cap 2N includes the entire support of the narrow collar. -/
theorem exists_all_mark_smoothing (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N →
    ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ Q ⊆ moduli N e P,
    |Part3.primeProductSignedError 1 N N Q (fun q => (integerRho N e P q : ℝ))
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) - smoothDiscrepancy t (p+3) N e P Q| ≤
      C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C,hC,hup⟩ := exists_upper_mark_reserve p
  refine ⟨1+C,by positivity,?_⟩
  filter_upwards [eventually_lower_mark_reserve t ht ht1 p 1 zero_lt_one,hup] with N hlo hhi
  intro hev e he he8 P Q hQ
  have hl := hlo hev e he he8 P Q hQ (p+3)
  have hu := hhi hev e he he8 P Q hQ t
  have hid := original_source_exact_reserves t (p+3) N Q (fun q => (integerRho N e P q : ℝ))
  unfold smoothDiscrepancy
  rw [hid, show ∀ x a b : ℝ, x+a+b-x = a+b by intros; ring]
  exact (abs_add_le _ _).trans ((add_le_add hl hu).trans_eq (by ring))

/-- The original medium/no-medium HB rows on the whole genuinely smooth
support, with all ordered roles, true products and the original integer rho. -/
theorem smooth_original_atlas (t : ℝ) (B N K : ℕ) (tau zeta e : ℝ) (P : Policy) (Q : Finset ℕ) :
    let L := actualLicence t B N
    let rho := fun q => ((integerRho N e P q : ℝ) : ℂ)
    (smoothDiscrepancy t B N e P Q : ℂ) =
      P5Z.OriginalPrimeAllGroupHBDiscrepancy.trimReserve L (2*N) N tau Q rho +
      ∑ js ∈ P5Z.ExactOriginalSmoothDyadicPartition.chartBank (2*N) 1,
        (P5Z.OriginalPrimeAtlasReserveBranches.mediumAtlas L K (2*N) N tau
          (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow zeta js)
          (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumHigh zeta js) Q rho js +
        P5Z.OriginalPrimeAtlasReserveBranches.noMediumAtlas L K (2*N) N tau
          (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow zeta js)
          (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumHigh zeta js) Q rho js -
        P5Z.OriginalPrimeAllGroupHBDiscrepancy.properPowerReserve L K (2*N) N tau Q rho js +
        P5Z.OriginalPrimeAllGroupHBDiscrepancy.roughPrimeReserve L K (2*N) N tau Q rho js) := by
  exact P5Z.OriginalPrimeAtlasReserveBranches.original_prime_discrepancy_mode_carriers
    (actualLicence t B N) K (2*N) N tau zeta Q (fun q => (integerRho N e P q : ℝ))

/-- The production count with a smooth singleton on its actual unpaid
complement. The rank-one family fields are given by actual_family_fields. -/
theorem exists_original_smooth_count_paid (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (p : ℕ) {eta eMax : ℝ} (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ D : ℝ, 0 < D ∧ ∃ e : ℝ, 0 < e ∧ e < 1/8 ∧ e < eMax ∧
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → Even N → ∀ P : Policy,
      fullProjectedMainSum N P - projectionReserve N eta +
        smoothDiscrepancy t (p+3) N e P (moduli N e P \ paidModuli N e P) -
        D*(N : ℝ)/(Real.log (N : ℝ))^p ≤ currentChenUpsilon5 N := by
  obtain ⟨C, hC, e, he, he8, heMax, M, hM, hold⟩ := exists_original_count_paid p heta hMax
  obtain ⟨F,hF,hpaid⟩ := exists_all_mark_smoothing t ht ht1 p
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hpaid
  refine ⟨C+F, by linarith, e, he, he8, heMax, max J M, hM.trans (le_max_right _ _), ?_⟩
  intro N hN hev P
  have h := hold N ((le_max_right _ _).trans hN) hev P
  have hs := hJ N ((le_max_left _ _).trans hN) hev e he he8 P _ Finset.sdiff_subset
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq] at hs
  change |remainingPrimitive N e P - _| ≤ _ at hs
  linarith only [h, (abs_le.mp hs).1]

end
end ImbalancedChen.P5OriginalU5AllMarkSmoothing

