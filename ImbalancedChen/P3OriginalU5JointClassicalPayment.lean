import ImbalancedChen.P3OriginalU5JointBetaAttachment
import ImbalancedChen.P3OriginalU5RoundedClassicalPayment

/-! At every selected set of original marked pairs, the jointly rounded
coefficient is pooled at its actual complete modulus. The genuine sifted
counts permit restriction to a rectangle before the signed estimator is
inserted. Classical BV pays the exact-coprime discrepancy below its cutoff. -/

namespace ImbalancedChen.P3OriginalU5JointClassicalPayment

noncomputable section
open Filter
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5JointBetaAttachment (rho rho_abs_le_one rho_minorant)
open P3OriginalU5RoundedClassicalPayment (rounded_fibre_unique rounded_quotient_mem_primorial
  physical_mem physical_data)
open P3OriginalU5RoundedCountInsertion (roundedSupport)
open P5OriginalU5CausalFinite (pairSupport cutoff smallCutoff attachment_gates)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

abbrev primitive (N q : ℕ) : ℝ :=
  finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q

abbrev correctionKernel (N q : ℕ) : ℝ :=
  chenPrimeDivisorCount N q / (q.totient : ℝ) + chenCentrePrimeAPCount N N q

abbrev moduliOn (T : Finset (ℕ × ℕ)) (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  chenPooledQuotientModuli T markedProduct (fun _ => roundedSupport N epsilon)

variable (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
  (m N : ℕ) (epsilon tau : ℝ)

def physicalRho (q : ℕ) : ℝ :=
  ∑ x ∈ ((pairSupport N ×ˢ roundedSupport N epsilon).filter
    (fun x => fullModulus x.1 x.2 = q)), rho R bank b m N epsilon tau x.1 x.2

/-- Recover the actual joint coefficient from the full physical modulus,
including the original two marked primes and the unique small/rough quotient. -/
theorem physicalRho_at_original {N : ℕ} {epsilon : ℝ}
    (hw : smallCutoff N epsilon ≤ cutoff N) (tau : ℝ) {t : ℕ × ℕ} {k : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ roundedSupport N epsilon) :
    physicalRho R bank b m N epsilon tau (fullModulus t k) = rho R bank b m N epsilon tau t k := by
  unfold physicalRho
  have htk : (t, k) ∈ (pairSupport N ×ˢ roundedSupport N epsilon).filter
      (fun x => fullModulus x.1 x.2 = fullModulus t k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, hk⟩, rfl⟩
  apply Finset.sum_eq_single_of_mem (t, k) htk
  intro x hx hne
  obtain ⟨hmem,heq⟩ := Finset.mem_filter.mp hx
  obtain ⟨hu,hl⟩ := Finset.mem_product.mp hmem
  obtain ⟨htu,hkl⟩ := rounded_fibre_unique hw hu hl ht hk heq
  exact False.elim (hne (Prod.ext htu hkl))

def rowTest (T : Finset (ℕ × ℕ)) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ T, ∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k * F (fullModulus t k)

theorem physical_pushforward {N : ℕ} {epsilon : ℝ} (hw : smallCutoff N epsilon ≤ cutoff N)
    (tau : ℝ) {T : Finset (ℕ × ℕ)} (hT : T ⊆ pairSupport N) (F : ℕ → ℝ) :
    (∑ q ∈ moduliOn T N epsilon, physicalRho R bank b m N epsilon tau q * F q) =
      rowTest R bank b m N epsilon tau T F := by
  have h := sum_chenPooledQuotientModuli T markedProduct (fun _ => roundedSupport N epsilon)
    (P5OriginalU5PlateauPrimeBV.primorial N) (fun _ ht => (chenY5PrimeSelector_sieve_data (hT ht)).2.2)
    (fun _ ht _ hu heq => chenY5PrimeSelector_multiplier_injOn N _ _ (hT ht) (hT hu) heq)
    (fun _ _ _ hk => rounded_quotient_mem_primorial hw hk)
    (fun q => physicalRho R bank b m N epsilon tau q * F q)
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro k hk
  rw [physicalRho_at_original R bank b m hw tau (hT ht) hk]

theorem physical_data_on {N : ℕ} {epsilon : ℝ} (hw : smallCutoff N epsilon ≤ cutoff N)
    (tau : ℝ) {T : Finset (ℕ × ℕ)} (hT : T ⊆ pairSupport N) {q : ℕ}
    (hq : q ∈ moduliOn T N epsilon) :
    0 < q ∧ N.Coprime q ∧ |physicalRho R bank b m N epsilon tau q| ≤ 1 := by
  obtain ⟨⟨t,k⟩, htag, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ht,hk⟩ := Finset.mem_sigma.mp htag
  obtain ⟨hp,hc⟩ := physical_data hw (physical_mem (hT ht) hk)
  exact ⟨hp,hc, (physicalRho_at_original R bank b m hw tau (hT ht) hk).symm ▸
    rho_abs_le_one R bank b m N epsilon tau t k⟩

def lowPrimitive (T : Finset (ℕ × ℕ)) (Q : ℕ) : ℝ :=
  ∑ q ∈ (moduliOn T N epsilon).filter (fun q => q ≤ Q),
    physicalRho R bank b m N epsilon tau q * primitive N q

def highPrimitive (T : Finset (ℕ × ℕ)) (Q : ℕ) : ℝ :=
  ∑ t ∈ T, ∑ k ∈ (roundedSupport N epsilon).filter (fun k => Q < fullModulus t k),
    rho R bank b m N epsilon tau t k * primitive N (fullModulus t k)

theorem signed_split {N : ℕ} {epsilon : ℝ} (hw : smallCutoff N epsilon ≤ cutoff N)
    (tau : ℝ) {T : Finset (ℕ × ℕ)} (hT : T ⊆ pairSupport N) (Q : ℕ) :
    rowTest R bank b m N epsilon tau T (primitive N) =
      lowPrimitive R bank b m N epsilon tau T Q + highPrimitive R bank b m N epsilon tau T Q := by
  have h := physical_pushforward R bank b m hw tau hT (fun q => if q ≤ Q then primitive N q else 0)
  have hlo : lowPrimitive R bank b m N epsilon tau T Q =
      ∑ t ∈ T, ∑ k ∈ (roundedSupport N epsilon).filter (fun k => fullModulus t k ≤ Q),
        rho R bank b m N epsilon tau t k * primitive N (fullModulus t k) := by
    simpa only [lowPrimitive, rowTest, Finset.sum_filter, mul_ite, mul_zero] using h
  rw [hlo]
  unfold rowTest highPrimitive
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hq : fullModulus t k ≤ Q
  · simp only [if_pos hq, if_neg (not_lt.mpr hq), add_zero]
  · simp only [if_neg hq, if_pos (lt_of_not_ge hq), zero_add]

/-- Restrict the nonnegative original sifted counts before inserting the
signed estimator at the selected pairs. -/
theorem subset_count_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (tau : ℝ) {T : Finset (ℕ × ℕ)}
    (hT : T ⊆ pairSupport N) :
    rowTest R bank b m N epsilon tau T (fun q => chenPrimeAPCount N N q -
      chenCentrePrimeAPCount N N q) ≤ currentChenUpsilon5 N := by
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  calc
    _ ≤ ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (markedProduct t) (cutoff N)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      change (∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k *
        (chenPrimeAPCount N N (markedProduct t*k) - chenCentrePrimeAPCount N N (markedProduct t*k))) ≤ _
      rw [← P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum]
      calc
        _ ≤ ∑ q ∈ chenQuotientPrimeSource N (markedProduct t),
            if ChenPrimeRough (cutoff N) q then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro q hq
          have hh := rho_minorant R bank b m hN he he8 tau (hT ht) (q : ℤ)
          rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at hh
          have hr := chenPrimeRough_iff_coprime_sieveProduct (cutoff N) (chenQuotientPrimeSource_data hq).2.2
          simpa only [Int.natAbs_natCast, ← hr] using hh
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => Nat.cast_nonneg _)

def density (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, ∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k /
    ((fullModulus t k).totient : ℝ)

def correction (T : Finset (ℕ × ℕ)) : ℝ :=
  rowTest R bank b m N epsilon tau T (correctionKernel N)

private theorem prime_account (N q : ℕ) :
    chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q =
      ((chenPrimePrefix N).card : ℝ) / (q.totient : ℝ) + primitive N q - correctionKernel N q := by
  have ha : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N q = chenPrimeAPCount N N q := by
    simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [primitive, finitePrimitiveDiscrepancy, ha, chenPrimePrefix_coprime_mass, correctionKernel]
  ring

theorem count_account {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (tau : ℝ) {T : Finset (ℕ × ℕ)}
    (hT : T ⊆ pairSupport N) (Q : ℕ) :
    ((chenPrimePrefix N).card : ℝ) * density R bank b m N epsilon tau T +
      (lowPrimitive R bank b m N epsilon tau T Q + highPrimitive R bank b m N epsilon tau T Q) -
      correction R bank b m N epsilon tau T ≤ currentChenUpsilon5 N := by
  rw [← signed_split R bank b m (attachment_gates hN he he8).2.2 tau hT]
  have h := subset_count_lower R bank b m hN he he8 tau hT
  apply le_trans (le_of_eq ?_) h
  simp only [density, correction, rowTest, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  rw [prime_account]
  ring

/-- The cutoff and threshold precede all geometric data, both meshes,
the marked set and the genuine signed coefficient on the complete moduli. -/
theorem exists_joint_classical_payment (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) (m : ℕ)
        (epsilon tau : ℝ), 0 < epsilon → epsilon < 1/8 → ∀ T : Finset (ℕ × ℕ),
        T ⊆ pairSupport N → |lowPrimitive R bank b m N epsilon tau T (panModulusCutoff N B)| ≤
          C * (N : ℝ) / Real.log (N : ℝ)^A := by
  obtain ⟨B,hB,C,hC,hBV⟩ := P3ExactCoprimePrimeBV.exists_signed_classical_payment A
  refine ⟨B,hB,C,hC,?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro R mesh bank b m epsilon tau he he8 T hT
  have hd {q : ℕ} (hq : q ∈ moduliOn T N epsilon) :=
    physical_data_on R bank b m (attachment_gates hN he he8).2.2 tau hT hq
  apply hBVN ((moduliOn T N epsilon).filter (fun q => q ≤ panModulusCutoff N B))
    (fun q hq => Finset.mem_Icc.mpr ⟨(hd (Finset.mem_filter.mp hq).1).1,
      (Finset.mem_filter.mp hq).2⟩) (fun _ => N)
    (fun _ hq => (hd (Finset.mem_filter.mp hq).1).2.1)
    (physicalRho R bank b m N epsilon tau)
    (fun _ hq => (hd (Finset.mem_filter.mp hq).1).2.2)

theorem eventually_joint_count_lower (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) (m : ℕ)
        (epsilon tau : ℝ), 0 < epsilon → epsilon < 1/8 → ∀ T : Finset (ℕ × ℕ),
        T ⊆ pairSupport N →
          ((chenPrimePrefix N).card : ℝ) * density R bank b m N epsilon tau T +
            highPrimitive R bank b m N epsilon tau T (panModulusCutoff N B) -
            correction R bank b m N epsilon tau T - C * (N : ℝ) / Real.log (N : ℝ)^A ≤
              currentChenUpsilon5 N := by
  obtain ⟨B,hB,C,hC,hBV⟩ := exists_joint_classical_payment A
  refine ⟨B,hB,C,hC,?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro R mesh bank b m epsilon tau he he8 T hT
  have hlow := (abs_le.mp (hBVN R bank b m epsilon tau he he8 T hT)).1
  have hcount := count_account R bank b m hN he he8 tau hT (panModulusCutoff N B)
  linarith only [hlow, hcount]

end
end ImbalancedChen.P3OriginalU5JointClassicalPayment
