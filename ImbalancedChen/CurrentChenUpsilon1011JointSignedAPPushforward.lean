import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.SingletonPrimeProductTransportP5
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The original joint signed AP error on full product moduli

Every mark consists of the original four-prime label and an actually
nonzero Rosser divisor coefficient at its original level. Grouping marks
by q=b*d produces one signed coefficient A(q). This grouping precedes
every absolute value. The original complement mask and all multiplicities
remain inside A. Overlapping p₁ factors and squareful q are retained.

The exact singleton Part3 target is connected with its genuine primitive
mean, keeping both the prime-count/li centring correction and the modulus-
prime correction explicit. No factorized distribution licence is asserted.
SOURCE-WRITTEN, UNCOMPILED. Earlier sources remain frozen.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical
open P5U10OriginalMean P5U1011JointOverlap
open Part3 P5S1SingletonPP

namespace P5U1011JointSignedAP

abbrev Mark := Σ _ : Label, ℕ

def activeRows (N : ℕ) (L : Label → ℝ) (t : Label) : Finset ℕ :=
  (support N t).filter (fun d => coefficient N t (L t) d ≠ 0)

def markedCarrier (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) : Finset Mark :=
  (jointSelector N E).sigma (activeRows N L)

def physicalModulus (x : Mark) : ℕ := multiplier x.1 * x.2

def markWeight (N : ℕ) (L : Label → ℝ) (x : Mark) : ℝ :=
  coefficient N x.1 (L x.1) x.2

def modulusSupport (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) : Finset ℕ :=
  (markedCarrier N E L).image physicalModulus

def modulusFibre (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) (q : ℕ) : Finset Mark :=
  (markedCarrier N E L).filter (fun x => physicalModulus x = q)

/-- The coefficient is a signed FIBRE SUM, not a unit indicator. -/
def fibreCoefficient (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ modulusFibre N E L q, markWeight N L x

def jointSignedAPError (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) (M : ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, signedAPError N M t (L t)

/-- Exact finite signed Fubini with the original level-zero tests. -/
theorem jointSignedAPError_eq_marks (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (M : ℝ) :
    jointSignedAPError N E L M =
      ∑ x ∈ markedCarrier N E L,
        markWeight N L x * chenQuotientPrimeAPError N M (physicalModulus x) := by
  rw [jointSignedAPError, markedCarrier, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  unfold signedAPError activeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  change coefficient N t (L t) d * chenQuotientPrimeAPError N M (multiplier t * d) =
    if coefficient N t (L t) d ≠ 0 then
      coefficient N t (L t) d * chenQuotientPrimeAPError N M (multiplier t * d) else 0
  by_cases hz : coefficient N t (L t) d = 0 <;> simp [hz]

/-- Exact pushforward against an arbitrary signed test, before norms. -/
theorem signed_weighted_pushforward (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (F : ℕ → ℝ) :
    (∑ x ∈ markedCarrier N E L, markWeight N L x * F (physicalModulus x)) =
      ∑ q ∈ modulusSupport N E L, fibreCoefficient N E L q * F q := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := markedCarrier N E L) (t := modulusSupport N E L) (g := physicalModulus)
    (fun x hx => Finset.mem_image_of_mem physicalModulus hx)
    (fun x => markWeight N L x * F (physicalModulus x))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q _
  unfold fibreCoefficient modulusFibre
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

theorem jointSignedAPError_eq_modulus_sum (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (M : ℝ) :
    jointSignedAPError N E L M =
      ∑ q ∈ modulusSupport N E L,
        fibreCoefficient N E L q * chenQuotientPrimeAPError N M q := by
  rw [jointSignedAPError_eq_marks]
  exact signed_weighted_pushforward N E L (chenQuotientPrimeAPError N M)

/-- Only after exact signed regrouping is the norm taken. -/
theorem abs_jointSignedAPError_eq_modulus_norm (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (M : ℝ) :
    |jointSignedAPError N E L M| =
      |∑ q ∈ modulusSupport N E L,
        fibreCoefficient N E L q * chenQuotientPrimeAPError N M q| :=
  congrArg abs (jointSignedAPError_eq_modulus_sum N E L M)

theorem fibreCoefficient_eq_zero_off_support {N q : ℕ} {E : ℕ × ℕ → Prop}
    {L : Label → ℝ} (hq : q ∉ modulusSupport N E L) : fibreCoefficient N E L q = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hxf := Finset.mem_filter.mp hx
  exact (hq (Finset.mem_image.mpr ⟨x, hxf.1, hxf.2⟩)).elim

theorem fibreCoefficient_ne_zero_mem_support {N q : ℕ} {E : ℕ × ℕ → Prop}
    {L : Label → ℝ} (hq : fibreCoefficient N E L q ≠ 0) : q ∈ modulusSupport N E L := by
  by_contra hnot
  exact hq (fibreCoefficient_eq_zero_off_support hnot)

/-- Unit bounds on marked coefficients give a fibre-cardinality bound.
No unit bound on the aggregated coefficient A(q) is inferred. -/
theorem abs_fibreCoefficient_le_card (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (q : ℕ) :
    |fibreCoefficient N E L q| ≤ ((modulusFibre N E L q).card : ℝ) := by
  unfold fibreCoefficient
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ x ∈ modulusFibre N E L q, |markWeight N L x|) ≤
        ∑ _x ∈ modulusFibre N E L q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact coefficient_abs_le_one N x.1 (L x.1) x.2
    _ = _ := by simp

theorem marked_modulus_pos {N : ℕ} {E : ℕ × ℕ → Prop} {L : Label → ℝ} {x : Mark}
    (hx : x ∈ markedCarrier N E L) : 0 < physicalModulus x := by
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hx
  have hactive := actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2
  exact mul_pos (joint_multiplier_pos ht) (Nat.pos_of_mem_divisors hactive.1)

theorem marked_modulus_coprime_target {N : ℕ} {E : ℕ × ℕ → Prop}
    {L : Label → ℝ} {x : Mark} (hx : x ∈ markedCarrier N E L) :
    Nat.Coprime (physicalModulus x) N := by
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hx
  obtain ⟨h1, h2, h3, h4, _⟩ := joint_carrier_order ht
  have hb : Nat.Coprime (multiplier x.1) N :=
    Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
      ⟨Nat.coprime_mul_iff_left.mpr
        ⟨(mem_chenAdditivePrimeCarrier.mp h1).2.2,
          (mem_chenAdditivePrimeCarrier.mp h2).2.2⟩,
        (mem_chenAdditivePrimeCarrier.mp h3).2.2⟩,
      (mem_chenAdditivePrimeCarrier.mp h4).2.2⟩
  have hdN := actualSmallRosserSupport_coprime_target N x.1.1.2
    (x.1.1.2 : ℝ) (Finset.mem_filter.mp hd).1
  exact Nat.coprime_mul_iff_left.mpr ⟨hb, hdN⟩

/-- Actual overlap marks retain the repeated first-prime factor in q. -/
theorem marked_first_sq_dvd {x : Mark} (hd : x.1.1.1 ∣ x.2) :
    x.1.1.1 ^ 2 ∣ physicalModulus x := first_sq_dvd_physical hd

theorem marked_modulus_lt_physical_cap {N : ℕ} {E : ℕ × ℕ → Prop}
    {L : Label → ℝ} {x : Mark} (hx : x ∈ markedCarrier N E L) (nu : ℝ)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    (physicalModulus x : ℝ) < (N : ℝ) ^ nu := by
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hx
  have hactive := (actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2).2.1
  have hb : (0 : ℝ) < (multiplier x.1 : ℝ) := Nat.cast_pos.mpr (joint_multiplier_pos ht)
  have hlt := (lt_div_iff₀ hb).mp (hactive.trans_le (hcap x.1 ht))
  simpa only [physicalModulus, Nat.cast_mul, mul_comm] using hlt

/-- Primitive support and its genuine physical cap follow from marked
source membership, with no factorization/distribution premise. -/
theorem modulusSupport_data {N : ℕ} {E : ℕ × ℕ → Prop} {L : Label → ℝ} {q : ℕ}
    (hq : q ∈ modulusSupport N E L) (nu : ℝ)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    0 < q ∧ Nat.Coprime N q ∧ (q : ℝ) < (N : ℝ) ^ nu := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨marked_modulus_pos hx, (marked_modulus_coprime_target hx).symm,
    marked_modulus_lt_physical_cap hx nu hcap⟩

theorem modulusSupport_subset_primitive_physical (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (nu : ℝ)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    modulusSupport N E L ⊆ (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ nu))).filter
      (fun q => Nat.Coprime N q) := by
  intro q hq
  obtain ⟨hqpos, hcop, hqcap⟩ := modulusSupport_data hq nu hcap
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqpos,
    (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) nu)).mpr hqcap.le⟩, hcop⟩

/-- The original natural residue N is primitive on every active full
modulus. This permits the exact singleton primitive-mean dictionary. -/
theorem modulusSupport_primitive {N : ℕ} {E : ℕ × ℕ → Prop} {L : Label → ℝ} {q : ℕ}
    (hq : q ∈ modulusSupport N E L) : Nat.Coprime N q := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact (marked_modulus_coprime_target hx).symm

theorem fibreCoefficient_nonzero_physical_data {N q : ℕ} {E : ℕ × ℕ → Prop}
    {L : Label → ℝ} (hq : fibreCoefficient N E L q ≠ 0) (nu : ℝ)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    0 < q ∧ Nat.Coprime N q ∧ (q : ℝ) < (N : ℝ) ^ nu :=
  modulusSupport_data (fibreCoefficient_ne_zero_mem_support hq) nu hcap

/-- The rank-one PP term is centred at actual coprime prime mass. Its
conversion to the caller's M-centred AP error keeps BOTH signed corrections. -/
theorem jointSignedAPError_eq_singletonPP (N : ℕ) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (M : ℝ) :
    jointSignedAPError N E L M =
      primeProductSignedError 1 N N (modulusSupport N E L) (fibreCoefficient N E L)
        (singletonWeight N (fun _ => 1)) +
      (((chenPrimePrefix N).card : ℝ) - M) *
        physicalDensitySum (modulusSupport N E L) (fibreCoefficient N E L) -
      ∑ q ∈ modulusSupport N E L, fibreCoefficient N E L q *
        (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
  have hPP := primeProductSignedError_singleton_unit_eq_AP N
    (modulusSupport N E L) (fibreCoefficient N E L)
  have hmodel : jointSignedAPError N E L M =
      (∑ q ∈ modulusSupport N E L, fibreCoefficient N E L q *
        (chenPrimeAPCount N N q - ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ))) +
        (((chenPrimePrefix N).card : ℝ) - M) *
          physicalDensitySum (modulusSupport N E L) (fibreCoefficient N E L) := by
    rw [jointSignedAPError_eq_modulus_sum]
    unfold physicalDensitySum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    unfold chenQuotientPrimeAPError
    ring
  linarith only [hPP, hmodel]

end P5U1011JointSignedAP

end

end ImbalancedChen
