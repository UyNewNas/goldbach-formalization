import ImbalancedChen.P5OriginalU5PhysicalRho
import ImbalancedChen.P2GammaU5PlateauGeometry
import ImbalancedChen.P2OriginalPairBufferedRootProvenance
import ImbalancedChen.P4BPositiveUpperPrimeBV
import ImbalancedChen.RealPhysicalUpperWeightBridge

/-!
The lower U5 prime receiver on the original constant-level rectangle. The
gcd of the complete modulus with the original strict sieve product recovers
the quotient, hence the ordered marked pair determines rectangle membership
on the physical carrier. The existing signed integer pushforward and prime
BV then apply to the same count and exact coprime mean. The original lower
count retains the complement and the two outer prime corrections.

Source only. Elaboration and kernel verification are pending.
-/
namespace ImbalancedChen.P5OriginalU5PlateauPrimeBV

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P5OriginalU5CausalFinite
open P2GammaU5PlateauGeometry (rectangle plateauLevel plateauQ)
open P3ActualEvenLowerIntegerRho (actualEvenLowerIntegerRho actualEvenLowerIntegerRho_cast)
open P3ActualU6PhysicalRhoPushforward (taggedPhysicalModuli taggedPhysicalIntegerRho
  tagged_physical_mem tagged_physical_pushforward_identity)

abbrev shortCap (N : ℕ) := Nat.floor ((N : ℝ) ^ (9/20 : ℝ))

/-- Select the genuine rectangle by the rough factor of the complete
modulus. The cutoff in the BV test also applies to the complete modulus. -/
def paidModuli (N : ℕ) (e : ℝ) (P : Policy) : Finset ℕ :=
  (moduli N e P).filter (fun q => q ≤ shortCap N ∧
    q / Nat.gcd q (primorial N) ∈ (rectangle N).image markedProduct)

theorem paid_iff_original_box {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) {t : ℕ × ℕ} {k : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ support N e (P t)) :
    fullModulus t k ∈ paidModuli N e P ↔
      fullModulus t k ≤ shortCap N ∧ t ∈ rectangle N := by
  have hdiv := quotient_mem_primorial (P t) hw hk
  have hg : Nat.gcd (fullModulus t k) (primorial N) = k :=
    chenQuotient_product_gcd_sieveProduct (chenY5PrimeSelector_sieve_data ht).2.2
      (Nat.dvd_of_mem_divisors hdiv)
  have hdecode : fullModulus t k / Nat.gcd (fullModulus t k) (primorial N) = markedProduct t := by
    rw [hg]
    exact Nat.mul_div_cancel _ (Nat.pos_of_mem_divisors hdiv)
  have hbox : markedProduct t ∈ (rectangle N).image markedProduct ↔ t ∈ rectangle N := by
    constructor
    · intro hm
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hm
      have hut : u = t := chenY5PrimeSelector_multiplier_injOn N _ _
        (P2GammaU5PlateauGeometry.rectangle_subset_pairSupport hN hu) ht heq
      exact hut ▸ hu
    · exact fun h => Finset.mem_image_of_mem _ h
  have hmem : fullModulus t k ∈ moduli N e P := tagged_physical_mem _ _ _ ht hk
  simp only [paidModuli, Finset.mem_filter, hmem, true_and, hdecode, hbox]

/-- Every actual active atom in the rectangle with at most two rough
quotient primes is included, with its complete small Rosser factor. The
two external marked primes are counted separately in the size calculation. -/
theorem two_rough_primes_mem_paid {N : ℕ} (hN : 2 ≤ N) {e : ℝ}
    (he : 0 < e) (he8 : e < 1/8) (P : Policy) {t : ℕ × ℕ} (ht : t ∈ rectangle N)
    {x : ℕ × ℕ} (hx : x ∈ P5CausalRhoFactorization.activePairs (P t) N (Nat.ceil (cutoff N))
      (smallCutoff N e) (cutoff N) (smallLevel N e)) (hrank : x.2.primeFactors.card ≤ 2) :
    fullModulus t (x.1 * x.2) ∈ paidModuli N e P := by
  have hpair := (Finset.mem_filter.mp hx).1
  have hr := (Finset.mem_product.mp hpair).2
  have hsf := fixedEvenRoughSupport_squarefree _ _ _ _ _ hr
  have hs := (P5CausalRhoFactorization.active_small_factor_lt _ _ _ _ _ _ hx).le
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hz : 1 ≤ cutoff N := Real.one_le_rpow hNr (by norm_num : (0 : ℝ) ≤ 417/5000)
  have hrough : (x.2 : ℝ) ≤ cutoff N ^ 2 := by
    calc
      _ = ∏ p ∈ x.2.primeFactors, (p : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
      _ ≤ ∏ _p ∈ x.2.primeFactors, cutoff N :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p) (fun p hp =>
            (mem_roughPrimeUniverse_upper (fixedEvenRoughSupport_primeFactors_mem _ _ _ _ _ hr hp)).le)
      _ = cutoff N ^ x.2.primeFactors.card := by simp
      _ ≤ _ := pow_le_pow_right₀ hz hrank
  have hp := mem_actualPrimeBoxTuples_iff.mp ((P2GammaU5PlateauGeometry.mem_rectangle N t).mp ht)
  have h1 : (t.1 : ℝ) ≤ (N : ℝ)^(11/100 : ℝ) := by
    simpa only [P2GammaU5PlateauGeometry.boxHi, Matrix.cons_val_zero] using (hp 0).2.2.2.le
  have h2 : (t.2 : ℝ) ≤ (N : ℝ)^(13/100 : ℝ) := by
    simpa only [P2GammaU5PlateauGeometry.boxHi, Matrix.cons_val_one] using (hp 1).2.2.2.le
  have hsize : (fullModulus t (x.1*x.2) : ℝ) ≤ (N : ℝ)^(9/20 : ℝ) := by
    calc
      _ = ((t.1 : ℝ)*t.2)*((x.1 : ℝ)*x.2) := by simp only [fullModulus, markedProduct, Nat.cast_mul]
      _ ≤ ((N : ℝ)^(11/100 : ℝ)*(N : ℝ)^(13/100 : ℝ))*(smallLevel N e*cutoff N^2) :=
          mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _))
            (mul_le_mul hs hrough (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _))
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (mul_nonneg (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _))
      _ = (N : ℝ)^((11/100 + 13/100) + (attachmentNu*e + (417/5000 + 417/5000)) : ℝ) := by
          simp only [smallLevel, cutoff, pow_two, Real.rpow_add hNp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr (by dsimp [attachmentNu]; linarith)
  have hk : x.1*x.2 ∈ support N e (P t) := Finset.mem_image.mpr ⟨x, hpair, rfl⟩
  exact (paid_iff_original_box hN P (attachment_gates hN he he8).2.2
    (P2GammaU5PlateauGeometry.rectangle_subset_pairSupport hN ht) hk).mpr ⟨Nat.le_floor hsize, ht⟩

private theorem modulus_data {N : ℕ} {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) {q : ℕ} (hq : q ∈ moduli N e P) :
    0 < q ∧ Squarefree q ∧ N.Coprime q ∧ |(integerRho N e P q : ℝ)| ≤ 1 := by
  obtain ⟨t, ht, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hm := chenY5PrimeSelector_sieve_data ht
  have hd := quotient_mem_primorial (P t) hw hk
  have hkd := Nat.dvd_of_mem_divisors hd
  have hsf : Squarefree (fullModulus t k) :=
    (Nat.squarefree_mul (chenQuotient_allowed_coprime hm.2.2 hkd)).mpr
      ⟨chenY5PrimeSelector_multiplier_squarefree ht,
        (sieveProduct_squarefree N (Nat.ceil (cutoff N))).squarefree_of_dvd hkd⟩
  refine ⟨Nat.pos_of_ne_zero hsf.ne_zero, hsf, chenQuotient_allowed_primitive hm.2.1 hkd, ?_⟩
  rw [integerRho_at_original P hw ht hk]
  change |(actualEvenLowerIntegerRho _ _ _ _ _ _ _ : ℝ)| ≤ 1
  rw [actualEvenLowerIntegerRho_cast]
  exact actualLowerSmallRoughRho_abs_le_one _ _ _ _ _ _ _

/-- The same integer coefficient used on all of U5 pays the short marked
rectangle. The threshold precedes the policy and attachment precision. -/
theorem eventually_paid_prime_discrepancy (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      |∑ q ∈ paidModuli N e P, (integerRho N e P q : ℝ) *
        (finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N q -
          finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) q / (Nat.totient q : ℝ))| ≤
        C * (N : ℝ) / Real.log (N : ℝ)^A := by
  obtain ⟨C, hC, hBV⟩ := P4BPositiveUpperPrimeBV.eventually_primeError_log_saving A
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro e he he8 P
  have hw := (attachment_gates hN he he8).2.2
  have hd (q : ℕ) (hq : q ∈ paidModuli N e P) :=
    modulus_data P hw (Finset.mem_filter.mp hq).1
  have hsub : paidModuli N e P ⊆ Finset.Icc 1 (shortCap N) := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(hd q hq).1, (Finset.mem_filter.mp hq).2.1⟩
  have hh := hBVN (paidModuli N e P) hsub
    (fun q hq => (hd q hq).2.1) (fun _ => N) (fun _ => N)
    (fun _ _ => le_rfl) (fun q hq => (hd q hq).2.2.1)
  change |∑ q ∈ paidModuli N e P,
    (integerRho N e P q : ℝ) * P4BPositiveUpperPrimeBV.primeError N N q| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum ?_).trans hh)
  intro q hq
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (hd q hq).2.2.2 (abs_nonneg _)).trans_eq (one_mul _)

/-- The original native selector runs one root plan on the whole rectangle.
The prefix parameters and subsequent checked decisions still depend on
the incoming word. Both source-level square conditions remain in force. -/
theorem native_plan_on_rectangle (R : P2OriginalPairSourceReceiver.PairRange)
    {mesh : ℕ} (bank : P2OriginalLowerWholeBoxBranchSelect.CandidateBank mesh)
    {buffer : ℚ} (hb : 0 ≤ buffer) (hb' : buffer ≤ 1/1000)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ rectangle N) :
    let seed := plateauLevel - 2*(buffer : ℝ)
    let slots := [(t.2, true), (t.1, true)]
    P2OriginalU5SmallPartnerRootPayment.rootQ N t = plateauQ N ∧
    P2OriginalSelectedPairNativeData.selectedPolicy R bank buffer false N t =
      P2OriginalPairRootRoughProducer.pairPolicy
        (P2OriginalPairSourceReceiver.pairPlan R bank (2*buffer) seed)
        (R.epsilon : ℝ) (P2OriginalPairSourceReceiver.ceiling : ℝ) seed N t ∧
    P2OriginalSelectedIntegerPrefixSquares.IntegerSquareGates N seed 1 (slots.map Prod.fst) ∧
    P2OriginalSelectedIntegerPrefixSquares.IntegerSquareGates N seed
      (P2OriginalSelectedIntegerPrefixSquares.selectedPrimes slots).prod
      (P2OriginalSelectedIntegerPrefixSquares.remainingPrimes slots) := by
  have hu := P2GammaU5PlateauGeometry.rectangle_coordinates hN ht 0
  have hv := P2GammaU5PlateauGeometry.rectangle_coordinates hN ht 1
  simp only [P2GammaU5PlateauGeometry.boxLo, P2GammaU5PlateauGeometry.boxHi,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
  have hlevel := P2GammaU5PlateauGeometry.original_level_on_box hu.1 hu.2.le hv.1 hv.2.le
  have hseed : P2OriginalSelectedPairNativeData.rootSeed false buffer N t =
      plateauLevel - 2*(buffer : ℝ) := by
    change Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1) - _ = _
    rw [hlevel]
  have hs := P2OriginalPairBufferedRootProvenance.fifth_selector_root_gates buffer hb hb' hN
    (P2GammaU5PlateauGeometry.rectangle_subset_pairSupport hN ht)
  dsimp only
  refine ⟨P2GammaU5PlateauGeometry.rectangle_rootQ hN ht, ?_, ?_⟩
  · simp only [P2OriginalSelectedPairNativeData.selectedPolicy, hseed]
  · simpa only [hseed] using hs

theorem paid_modulus_le_buffered_root {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (P : Policy)
    {buffer : ℚ} (hb : buffer ≤ 1/1000) {q : ℕ} (hq : q ∈ paidModuli N e P) :
    (q : ℝ) ≤ (N : ℝ)^(plateauLevel - 2*(buffer : ℝ)) := by
  have hqcap : q ≤ shortCap N := (Finset.mem_filter.mp hq).2.1
  have hbr : (buffer : ℝ) ≤ 1/1000 := by exact_mod_cast hb
  have hexp : (9/20 : ℝ) ≤ plateauLevel - 2*(buffer : ℝ) := by
    rw [P2GammaU5PlateauGeometry.plateauLevel_exact]
    linarith
  exact (show (q : ℝ) ≤ (shortCap N : ℝ) by exact_mod_cast hqcap).trans
    ((Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (9/20 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hexp))

/-- The retained ledger indexes the original global coefficient on the
physical set difference. This keeps all long moduli in the rectangle and
every modulus from the complementary ordered labels. -/
def remainingPrimitive (N : ℕ) (e : ℝ) (P : Policy) : ℝ :=
  ∑ q ∈ moduli N e P \ paidModuli N e P, (integerRho N e P q : ℝ) *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q

theorem original_account_partition (N : ℕ) (e : ℝ) (P : Policy) :
    signedPrimitiveSum N e P = remainingPrimitive N e P +
      ∑ q ∈ paidModuli N e P, (integerRho N e P q : ℝ) *
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q := by
  have hall := tagged_physical_pushforward_identity (pairSupport N)
    (fun t => support N e (P t)) fullModulus (rowInteger N e P)
    (fun q => finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q)
  have hfull : signedPrimitiveSum N e P = ∑ q ∈ moduli N e P,
      (integerRho N e P q : ℝ) * finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q := by
    simpa only [signedPrimitiveSum, rowSignedPrimitive, rho, rowInteger, actualEvenLowerIntegerRho_cast,
      integerRho, moduli, fullModulus, markedProduct] using hall.symm
  rw [hfull]
  exact (Finset.sum_sdiff (f := fun q => (integerRho N e P q : ℝ) *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q)
    (show paidModuli N e P ⊆ moduli N e P from Finset.filter_subset _ _)).symm

/-- Apply the signed payment inside the production U5 lower-count caller,
including its full outer prime and centre costs under the original policy. -/
theorem eventually_original_count_lower (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      mainSum N e P + remainingPrimitive N e P - C * (N : ℝ) / Real.log (N : ℝ)^A -
        primeCostSum N e P - centreCostSum N e P ≤ currentChenUpsilon5 N := by
  obtain ⟨C, hC, hpaid⟩ := eventually_paid_prime_discrepancy A
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpaid, eventually_ge_atTop (2 : ℕ)] with N hpay hN
  intro e he he8 P
  have h := originalU5_causal_lower hN he he8 P
  rw [original_account_partition] at h
  have hlo := (abs_le.mp (hpay e he he8 P)).1
  change -(C * (N : ℝ) / Real.log (N : ℝ)^A) ≤
    ∑ q ∈ paidModuli N e P, (integerRho N e P q : ℝ) *
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q at hlo
  linarith only [h, hlo]

/-- The projected-density caller chooses the original attachment precision
from its reserve. Its common threshold also pays the short boxed terms. -/
theorem exists_projected_count_lower (A : ℕ) {eta eMax : ℝ} (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, 0 < e ∧ e < 1/8 ∧ e < eMax ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ P : Policy,
        fullProjectedMainSum N P - projectionReserve N eta + remainingPrimitive N e P -
          C * (N : ℝ) / Real.log (N : ℝ)^A - primeCostSum N e P - centreCostSum N e P ≤
          currentChenUpsilon5 N := by
  obtain ⟨C, hC, hpaid⟩ := eventually_paid_prime_discrepancy A
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hpaid
  obtain ⟨e, he, he8, heMax, N₂, hN₂, hproj⟩ :=
    exists_originalU5_full_density_causal_lower eta eMax heta hMax
  refine ⟨C, hC, e, he, he8, heMax, max N₁ N₂, hN₂.trans (le_max_right _ _), ?_⟩
  intro N hN hev P
  have h := hproj N ((le_max_right _ _).trans hN) hev P
  rw [original_account_partition] at h
  have hlo := (abs_le.mp (hN₁ N ((le_max_left _ _).trans hN) e he he8 P)).1
  change -(C * (N : ℝ) / Real.log (N : ℝ)^A) ≤
    ∑ q ∈ paidModuli N e P, (integerRho N e P q : ℝ) *
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q at hlo
  linarith only [h, hlo]

end
end ImbalancedChen.P5OriginalU5PlateauPrimeBV
