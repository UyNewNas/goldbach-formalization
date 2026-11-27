import ImbalancedChen.P3ExactCoprimePrimeBV
import ImbalancedChen.P3OriginalU5RoundedPrimeCorrection

/-! The literal rounded U5 coefficient, pooled at its complete physical
modulus. Classical BV pays precisely its below-cutoff part. The full signed
complement remains in the exact partition. -/

namespace ImbalancedChen.P3OriginalU5RoundedClassicalPayment

noncomputable section
open Filter
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P5OriginalU5CausalFinite (pairSupport cutoff smallCutoff smallLevel attachment_gates)
open P5OriginalU5PlateauPrimeBV (Policy fullModulus)
open P3OriginalU5RoundedCountInsertion (roundedSupport roundedRho rowSignedPrimitive)
open P3OriginalU5RoundedPrimeCorrection (roundedSupport_pos)

/-- Even zero-coefficient members of the actual rounded carrier divide the
original strict primorial. -/
theorem rounded_quotient_mem_primorial {N : ℕ} {epsilon : ℝ}
    (hw : smallCutoff N epsilon ≤ cutoff N) {k : ℕ}
    (hk : k ∈ roundedSupport N epsilon) : k ∈ (P5OriginalU5PlateauPrimeBV.primorial N).divisors := by
  obtain ⟨⟨s, r⟩, hsr, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hsr
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hs)
    (P2LowerFiniteCellRounding.universe_rough _ _ _ _ hr)
  have hprod : P2LowerFiniteCellRounding.roughProduct N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) ∣ P5OriginalU5PlateauPrimeBV.primorial N := by
    have heq : (∏ p ∈ (roughPrimeUniverse N (Nat.ceil (cutoff N))
        (smallCutoff N epsilon) (cutoff N)).toFinset, p) =
        P2LowerFiniteCellRounding.roughProduct N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N) := by
      simpa [P2LowerFiniteCellRounding.roughProduct] using
        List.prod_toFinset (fun p : ℕ => p)
          (roughPrimeUniverse_nodup N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N))
    rw [← heq]
    unfold P5OriginalU5PlateauPrimeBV.primorial sieveProduct
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have hm := List.mem_toFinset.mp hp
    exact mem_sievePrimes.mpr ⟨Nat.lt_ceil.mpr (mem_roughPrimeUniverse_upper hm),
      mem_roughPrimeUniverse_prime hm, mem_roughPrimeUniverse_not_dvd hm⟩
  have hrdiv := (Nat.mem_divisors.mp hr).1.trans hprod
  exact Nat.mem_divisors.mpr ⟨hcop.mul_dvd_of_dvd_of_dvd
    (actualSmallRosserSupport_dvd_sieveProduct_ceil _ _ _ _ hw hs) hrdiv,
    (sieveProduct_squarefree N (Nat.ceil (cutoff N))).ne_zero⟩

/-- The ordered outer labels and the quotient are recovered from the full
modulus of the rounded coefficient, without replacing it by native rho. -/
theorem rounded_fibre_unique {N : ℕ} {epsilon : ℝ}
    (hw : smallCutoff N epsilon ≤ cutoff N) {t u : ℕ × ℕ} {k l : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ roundedSupport N epsilon)
    (hu : u ∈ pairSupport N) (hl : l ∈ roundedSupport N epsilon)
    (heq : fullModulus t k = fullModulus u l) : t = u ∧ k = l := by
  obtain ⟨hprod, hkl⟩ := chenQuotient_product_factors_unique
    (chenY5PrimeSelector_sieve_data ht).2.2 (chenY5PrimeSelector_sieve_data hu).2.2
    (rounded_quotient_mem_primorial hw hk) (rounded_quotient_mem_primorial hw hl) heq
  exact ⟨chenY5PrimeSelector_multiplier_injOn N _ _ ht hu hprod, hkl⟩

def physicalModuli (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  (pairSupport N).biUnion (fun t => (roundedSupport N epsilon).image (fullModulus t))

def physicalRho (N : ℕ) (epsilon tau : ℝ) (P : Policy) (q : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
    if fullModulus t k = q then roundedRho N epsilon tau (P t) k else 0

theorem physical_mem {N : ℕ} {epsilon : ℝ} {t : ℕ × ℕ} {k : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ roundedSupport N epsilon) :
    fullModulus t k ∈ physicalModuli N epsilon :=
  Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩

theorem physicalRho_at_original {N : ℕ} {epsilon tau : ℝ} (P : Policy)
    (hw : smallCutoff N epsilon ≤ cutoff N) {t : ℕ × ℕ} {k : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ roundedSupport N epsilon) :
    physicalRho N epsilon tau P (fullModulus t k) = roundedRho N epsilon tau (P t) k := by
  unfold physicalRho
  calc
    _ = ∑ l ∈ roundedSupport N epsilon,
        if fullModulus t l = fullModulus t k then roundedRho N epsilon tau (P t) l else 0 := by
      apply Finset.sum_eq_single_of_mem t ht
      intro u hu hne
      apply Finset.sum_eq_zero
      intro l hl
      exact if_neg (fun h => hne (rounded_fibre_unique hw hu hl ht hk h).1)
    _ = (if fullModulus t k = fullModulus t k then roundedRho N epsilon tau (P t) k else 0) := by
      apply Finset.sum_eq_single_of_mem k hk
      intro l hl hne
      exact if_neg (fun h => hne (rounded_fibre_unique hw ht hl ht hk h).2)
    _ = _ := if_pos rfl

theorem physicalRho_abs_le_one {N : ℕ} {epsilon tau : ℝ} (P : Policy)
    (hw : smallCutoff N epsilon ≤ cutoff N) {q : ℕ} (hq : q ∈ physicalModuli N epsilon) :
    |physicalRho N epsilon tau P q| ≤ 1 := by
  obtain ⟨t, ht, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  rw [physicalRho_at_original P hw ht hk]
  exact P2LowerFiniteCellBetaCompiler.rho_abs_le_one _ _ _ _ _ _ _ _

theorem physical_data {N : ℕ} {epsilon : ℝ}
    (hw : smallCutoff N epsilon ≤ cutoff N) {q : ℕ} (hq : q ∈ physicalModuli N epsilon) :
    0 < q ∧ N.Coprime q := by
  obtain ⟨t, ht, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hd := chenY5PrimeSelector_sieve_data ht
  exact ⟨Nat.mul_pos (Nat.zero_lt_one.trans hd.1) (roundedSupport_pos hk),
    chenQuotient_allowed_primitive hd.2.1 (Nat.mem_divisors.mp
      (rounded_quotient_mem_primorial hw hk)).1⟩

/-- Exact real signed reindexing, before any discrepancy estimate. -/
theorem physical_pushforward (N : ℕ) (epsilon tau : ℝ) (P : Policy) (F : ℕ → ℝ) :
    (∑ q ∈ physicalModuli N epsilon, physicalRho N epsilon tau P q * F q) =
      ∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
        roundedRho N epsilon tau (P t) k * F (fullModulus t k) := by
  unfold physicalRho
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single_of_mem (fullModulus t k) (physical_mem ht hk)]
  · simp
  · intro q _ hne
    simp only [if_neg (Ne.symm hne), zero_mul]

def lowModuli (N : ℕ) (epsilon : ℝ) (Q : ℕ) : Finset ℕ :=
  (physicalModuli N epsilon).filter (fun q => q ≤ Q)

def lowPrimitive (N : ℕ) (epsilon tau : ℝ) (P : Policy) (Q : ℕ) : ℝ :=
  ∑ q ∈ lowModuli N epsilon Q, physicalRho N epsilon tau P q *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q

def highPrimitive (N : ℕ) (epsilon tau : ℝ) (P : Policy) (Q : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N, ∑ k ∈ (roundedSupport N epsilon).filter (fun k => Q < fullModulus t k),
    roundedRho N epsilon tau (P t) k *
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (fullModulus t k)

theorem lowPrimitive_eq_rows (N : ℕ) (epsilon tau : ℝ) (P : Policy) (Q : ℕ) :
    lowPrimitive N epsilon tau P Q =
      ∑ t ∈ pairSupport N, ∑ k ∈ (roundedSupport N epsilon).filter (fun k => fullModulus t k ≤ Q),
        roundedRho N epsilon tau (P t) k *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (fullModulus t k) := by
  have h := physical_pushforward N epsilon tau P
    (fun q => if q ≤ Q then finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q else 0)
  simpa only [lowPrimitive, lowModuli, Finset.sum_filter, mul_ite, mul_zero] using h

/-- The unchanged high-modulus signed complement is explicit. -/
theorem original_signed_primitive_split (N : ℕ) (epsilon tau : ℝ) (P : Policy) (Q : ℕ) :
    (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (P t) t) =
      lowPrimitive N epsilon tau P Q + highPrimitive N epsilon tau P Q := by
  rw [lowPrimitive_eq_rows]
  unfold highPrimitive
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold rowSignedPrimitive
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : fullModulus t k ≤ Q
  · simp only [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · simp only [if_neg h, if_pos (lt_of_not_ge h), zero_add]

/-- Classical BV for the same rounded coefficients at the complete
physical modulus. The cutoff and threshold precede every allowed rounding
parameter and every row policy. -/
theorem exists_original_rounded_classical_payment (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ epsilon tau : ℝ, 0 < epsilon → epsilon < 1 / 8 → ∀ P : Policy,
        |lowPrimitive N epsilon tau P (panModulusCutoff N B)| ≤
          C * (N : ℝ) / Real.log (N : ℝ)^A := by
  obtain ⟨B, hB, C, hC, hBV⟩ := P3ExactCoprimePrimeBV.exists_signed_classical_payment A
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro epsilon tau he he8 P
  have hw := (attachment_gates hN he he8).2.2
  apply hBVN (lowModuli N epsilon (panModulusCutoff N B))
    (fun q hq => Finset.mem_Icc.mpr ⟨(physical_data hw (Finset.mem_filter.mp hq).1).1,
      (Finset.mem_filter.mp hq).2⟩) (fun _ => N)
    (fun _ hq => (physical_data hw (Finset.mem_filter.mp hq).1).2)
    (physicalRho N epsilon tau P)
    (fun _ hq => physicalRho_abs_le_one P hw (Finset.mem_filter.mp hq).1)

end
end ImbalancedChen.P3OriginalU5RoundedClassicalPayment
