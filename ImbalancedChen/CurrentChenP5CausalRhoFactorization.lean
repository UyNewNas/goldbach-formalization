import ImbalancedChen.CurrentChenP5CausalRhoQuotientBridge
import ImbalancedChen.ChenPooledQuotientAP

/-!
# Actual signed small/rough convolution for the sixth quotient rows

The coefficient is the genuine even-exit actualLowerSmallRoughRho. Its
rough sign selects actualSmallRosserMinus for a nonnegative rough atom
and actualSmallRosserPlus for a negative atom. No multiplicativity of
rho is assumed. The unique strict-small/inclusive-rough factorization
and physical prefix b=p1*p2 are retained as actual labels for P3.

SOURCE ONLY: uncompiled. Total enhanced support licensing remains open;
no bound on b*s*r is inferred from the small factor's own bound s<L.
-/

namespace ImbalancedChen.P5CausalRhoFactorization

open scoped BigOperators
open Classical
open P5SelectedMaskTransport

noncomputable section

def pairs (policy : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : Finset (ℕ × ℕ) :=
  actualSmallRosserSupport N cap w ×ˢ fixedEvenRoughSupport policy N cap w z

/-- The actual LOWER sign attachment: the two small Rosser signs are
chosen by the sign of the literal retained rough coefficient. -/
def coefficient (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (x : ℕ × ℕ) : ℝ :=
  fixedEvenRoughCoefficient policy N cap w z x.2 *
    (if 0 ≤ fixedEvenRoughCoefficient policy N cap w z x.2 then
      actualSmallRosserMinus N cap w L x.1 else actualSmallRosserPlus N cap w L x.1)

theorem pair_product_injOn (policy : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
      (pairs policy N cap w z : Set (ℕ × ℕ)) := by
  exact smallRough_mul_injOn
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt policy N cap w z hd)

theorem rho_at_pair (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {x : ℕ × ℕ} (hx : x ∈ pairs policy N cap w z) :
    actualLowerSmallRoughRho policy N cap w z L (x.1 * x.2) =
      coefficient policy N cap w z L x := by
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hx
  exact smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt policy N cap w z hd)
    (fixedEvenRoughCoefficient policy N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) hs hr

/-- Exact finite convolution, including zero coefficients. -/
theorem rho_eq_fibre_convolution (policy : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (k : ℕ) :
    actualLowerSmallRoughRho policy N cap w z L k =
      ∑ x ∈ (pairs policy N cap w z).filter (fun x => x.1 * x.2 = k),
        coefficient policy N cap w z L x := by
  rfl

def activePairs (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset (ℕ × ℕ) :=
  (pairs policy N cap w z).filter (fun x => coefficient policy N cap w z L x ≠ 0)

theorem active_eq_image (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    P5CausalRhoQuotientBridge.active policy N cap w z L =
      (activePairs policy N cap w z L).image (fun x => x.1 * x.2) := by
  ext k
  constructor
  · intro hk
    obtain ⟨hbase, hnonzero⟩ := Finset.mem_filter.mp hk
    obtain ⟨x, hx, hprod⟩ := Finset.mem_image.mp hbase
    have hrho := rho_at_pair policy N cap w z L hx
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hprod⟩
    rw [← hrho, hprod]
    exact hnonzero
  · intro hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hpair, hnonzero⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨x, hpair, rfl⟩
    · rw [rho_at_pair policy N cap w z L hpair]
      exact hnonzero

/-- Every active scalar modulus has exactly one active small/rough label. -/
theorem active_unique_factors (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {k : ℕ} (hk : k ∈ P5CausalRhoQuotientBridge.active policy N cap w z L) :
    ∃! x : ℕ × ℕ, x ∈ activePairs policy N cap w z L ∧ x.1 * x.2 = k := by
  rw [active_eq_image] at hk
  obtain ⟨x, hx, hprod⟩ := Finset.mem_image.mp hk
  refine ⟨x, ⟨hx, hprod⟩, ?_⟩
  intro y hy
  exact pair_product_injOn policy N cap w z
    (Finset.mem_filter.mp hy.1).1 (Finset.mem_filter.mp hx).1 (hy.2.trans hprod.symm)

theorem coefficient_abs_le_one (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {x : ℕ × ℕ} (hx : x ∈ pairs policy N cap w z) :
    |coefficient policy N cap w z L x| ≤ 1 := by
  rw [← rho_at_pair policy N cap w z L hx]
  exact actualLowerSmallRoughRho_abs_le_one policy N cap w z L (x.1 * x.2)

theorem active_small_factor_lt (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {x : ℕ × ℕ} (hx : x ∈ activePairs policy N cap w z L) : (x.1 : ℝ) < L := by
  have hn := (Finset.mem_filter.mp hx).2
  change fixedEvenRoughCoefficient policy N cap w z x.2 *
    (if 0 ≤ fixedEvenRoughCoefficient policy N cap w z x.2 then
      actualSmallRosserMinus N cap w L x.1 else actualSmallRosserPlus N cap w L x.1) ≠ 0 at hn
  have hbeta := (mul_ne_zero_iff.mp hn).2
  by_cases hsign : 0 ≤ fixedEvenRoughCoefficient policy N cap w z x.2
  · rw [if_pos hsign] at hbeta
    exact (actualSmallRosserMinus_active hbeta).2.1
  · rw [if_neg hsign] at hbeta
    exact (actualSmallRosserPlus_active hbeta).2.1

theorem pair_block_data (policy : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {x : ℕ × ℕ} (hx : x ∈ pairs policy N cap w z) :
    Squarefree x.1 ∧ Squarefree x.2 ∧ Nat.Coprime x.1 x.2 ∧
      Nat.Coprime x.1 N ∧ Nat.Coprime x.2 N := by
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hx
  exact ⟨actualSmallRosserSupport_squarefree N cap w hs,
    fixedEvenRoughSupport_squarefree policy N cap w z hr,
    smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w hs)
      (fixedEvenRoughSupport_roughPrimeSupportedAt policy N cap w z hr),
    actualSmallRosserSupport_coprime_target N cap w hs,
    fixedEvenRoughSupport_coprime_target policy N cap w z hr⟩

/-- Exact signed error Fubini with physical modulus b*s*r. This is a
reindexing of the same coefficient, never a product rho(s)*rho(r). -/
theorem signed_physical_sum_fubini (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ k ∈ actualLowerSmallRoughModuli policy N cap w z,
      actualLowerSmallRoughRho policy N cap w z L k * F (b * k)) =
      ∑ x ∈ pairs policy N cap w z,
        coefficient policy N cap w z L x * F ((b * x.1) * x.2) := by
  simpa only [Nat.mul_assoc] using sum_smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt policy N cap w z hd)
    (fixedEvenRoughCoefficient policy N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)
    (fun k => F (b * k))

theorem signed_physical_sum_nested (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ k ∈ actualLowerSmallRoughModuli policy N cap w z,
      actualLowerSmallRoughRho policy N cap w z L k * F (b * k)) =
      ∑ s ∈ actualSmallRosserSupport N cap w,
        ∑ r ∈ fixedEvenRoughSupport policy N cap w z,
          coefficient policy N cap w z L (s, r) * F ((b * s) * r) := by
  rw [signed_physical_sum_fubini, pairs, Finset.sum_product]

/-- After attaching a positive prefix, the physical modulus still
determines its small/rough label uniquely. -/
theorem physical_label_injOn (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z : ℝ) (hb : 0 < b) :
    Set.InjOn (fun x : ℕ × ℕ => (b * x.1) * x.2)
      (pairs policy N cap w z : Set (ℕ × ℕ)) := by
  intro x hx y hy hprod
  apply pair_product_injOn policy N cap w z hx hy
  apply Nat.eq_of_mul_eq_mul_left hb
  simpa only [Nat.mul_assoc] using hprod

def physicalActive (policy : List ℕ → Bool) (N cap b : ℕ) (w z L : ℝ) : Finset ℕ :=
  (activePairs policy N cap w z L).image (fun x => (b * x.1) * x.2)

theorem physicalActive_unique_label (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) (hb : 0 < b) {m : ℕ}
    (hm : m ∈ physicalActive policy N cap b w z L) :
    ∃! x : ℕ × ℕ, x ∈ activePairs policy N cap w z L ∧ (b * x.1) * x.2 = m := by
  obtain ⟨x, hx, hprod⟩ := Finset.mem_image.mp hm
  refine ⟨x, ⟨hx, hprod⟩, ?_⟩
  intro y hy
  exact physical_label_injOn policy N cap b w z hb
    (Finset.mem_filter.mp hy.1).1 (Finset.mem_filter.mp hx).1 (hy.2.trans hprod.symm)

/-- The primitive discrepancy passed to a signed P3 kernel is evaluated
at the actual three-block modulus, with the same signed lower rho. -/
theorem signed_primitive_sum_nested (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) :
    (∑ k ∈ actualLowerSmallRoughModuli policy N cap w z,
      actualLowerSmallRoughRho policy N cap w z L k *
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (b * k)) =
      ∑ s ∈ actualSmallRosserSupport N cap w,
        ∑ r ∈ fixedEvenRoughSupport policy N cap w z,
          coefficient policy N cap w z L (s, r) *
            finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((b * s) * r) := by
  exact signed_physical_sum_nested policy N cap b w z L
    (finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N)

/-- All three P3 blocks have their actual coprimality, squarefree and
centre-primitive properties on an original sixth-row prefix. -/
theorem original_U6_three_block_data {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ sixthSupport N) (policy : List ℕ → Bool) (cap : ℕ) (w : ℝ)
    (hwz : w ≤ P5CausalRhoQuotientBridge.cutoff N) {x : ℕ × ℕ}
    (hx : x ∈ pairs policy N cap w (P5CausalRhoQuotientBridge.cutoff N)) :
    Nat.Coprime (t.1 * t.2) x.1 ∧ Nat.Coprime (t.1 * t.2) x.2 ∧
      Nat.Coprime x.1 x.2 ∧ Squarefree (((t.1 * t.2) * x.1) * x.2) ∧
      Nat.Coprime (((t.1 * t.2) * x.1) * x.2) N := by
  have hblocks := pair_block_data policy N cap w _ hx
  have hbrough := P5CausalRhoQuotientBridge.row_multiplier_rough ht
  have hk : x.1 * x.2 ∈ actualLowerSmallRoughModuli policy N cap w
      (P5CausalRhoQuotientBridge.cutoff N) := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hbcop := P5CausalRhoQuotientBridge.moduli_coprime_multiplier
    policy N cap (t.1 * t.2) w _ hwz hbrough hk
  have hbparts := Nat.coprime_mul_iff_right.mp hbcop
  have hbsf := chenY6PrimeSelector_multiplier_squarefree ht
  have hksf := (Nat.squarefree_mul hblocks.2.2.1).mpr ⟨hblocks.1, hblocks.2.1⟩
  have htotalSF := (Nat.squarefree_mul hbcop).mpr ⟨hbsf, hksf⟩
  have hbN := (chenY6PrimeSelector_sieve_data ht).2.1
  have htotalN := Nat.coprime_mul_iff_left.mpr
    ⟨hbN, Nat.coprime_mul_iff_left.mpr ⟨hblocks.2.2.2.1, hblocks.2.2.2.2⟩⟩
  exact ⟨hbparts.1, hbparts.2, hblocks.2.2.1,
    by simpa only [Nat.mul_assoc] using htotalSF,
    by simpa only [Nat.mul_assoc] using htotalN⟩

/-- The actual signed AP rows read by a spectral kernel have these
factorized labels, with the original pair mask and corrected product gate. -/
theorem original_retained_signed_AP_fubini (N : ℕ) (eta M : ℝ)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (E : ℕ × ℕ → Prop) :
    (∑ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      ∑ k ∈ actualLowerSmallRoughModuli (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
          (P5CausalRhoQuotientBridge.cutoff N),
        actualLowerSmallRoughRho (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
          (P5CausalRhoQuotientBridge.cutoff N) (L t) k *
            chenQuotientPrimeAPError N M ((t.1 * t.2) * k)) =
    ∑ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      ∑ s ∈ actualSmallRosserSupport N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t),
        ∑ r ∈ fixedEvenRoughSupport (policy t) N
            (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
            (P5CausalRhoQuotientBridge.cutoff N),
          coefficient (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
            (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) (s, r) *
              chenQuotientPrimeAPError N M (((t.1 * t.2) * s) * r) := by
  apply Finset.sum_congr rfl
  intro t ht
  exact signed_physical_sum_nested (policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (t.1 * t.2)
    (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) (chenQuotientPrimeAPError N M)

end

end ImbalancedChen.P5CausalRhoFactorization
