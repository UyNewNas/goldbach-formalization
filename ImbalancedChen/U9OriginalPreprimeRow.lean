import ImbalancedChen.U9SemiprimeSwitchedPrimeAP

/-!
# The actual U9 row before primality of its original second factor

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Both original complementary factors p₁ and q remain parameters. Only the
primality of the original p₂ slot is removed. Its positivity, centre mask,
old bands, moving square-root gate and strict product endpoints remain.
The derived interval has explicit factor-dependent floor/ceiling endpoints.
This is an upstream integer model, not a replacement prime AP estimate.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def factorAllowed (N p q : ℕ) : Prop :=
  p ∈ chenAdditivePrimeCarrier N ∧ q ∈ chenAdditivePrimeCarrier N ∧
    (N : ℝ) ^ (19 / 125 : ℝ) ≤ (p : ℝ) ∧
    (p : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ)

/-- Every old row gate except primality of r is retained explicitly. -/
def preprimeRow (N : ℕ) (X : ℝ) (p q : ℕ) : Finset ℕ :=
  if factorAllowed N p q then
    (Finset.range N).filter fun r =>
      0 < r ∧ Nat.Coprime r N ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (r : ℝ) ∧
      (r : ℝ) < Real.sqrt ((N : ℝ) / (p : ℝ)) ∧
      p * r * q < N ∧
      Real.sqrt ((N : ℝ) / ((p : ℝ) * (r : ℝ))) ≤ (q : ℝ) ∧
      Nat.Coprime (N - p * r * q) N ∧ X < (p * r * q : ℕ)
  else ∅

/-- Restoring precisely the removed prime condition recovers the original
marked triple source, with its exact original first/last factor labels. -/
theorem preprimeRow_prime_iff {N p q r : ℕ} {X : ℝ} :
    r ∈ preprimeRow N X p q ∧ Nat.Prime r ↔
      (⟨(p, r), q⟩ : P5zU9Triple) ∈ labels N X := by
  constructor
  · rintro ⟨hr, hprime⟩
    have hf : factorAllowed N p q := by
      by_contra hn
      simpa only [preprimeRow, if_neg hn, Finset.notMem_empty] using hr
    obtain ⟨hp, hq, hpH, hpD⟩ := hf
    rw [preprimeRow, if_pos hf] at hr
    obtain ⟨hrN, hrpos, hrcop, hrD, hrcap, hprod, hcut, hcentre, hX⟩ :=
      Finset.mem_filter.mp hr
    have hrCarrier : r ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier.mpr ⟨Finset.mem_range.mp hrN, hprime, hrcop⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_p5z_u9_switchedLabels_iff.mpr ⟨?_, ?_, ?_, hprod, hcut, hcentre⟩, hX⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp, hrCarrier⟩, hpH, hpD, hrD, hrcap⟩
    · exact Nat.lt_succ_of_le (mem_chenAdditivePrimeCarrier.mp hq).1.le
    · exact (mem_chenAdditivePrimeCarrier.mp hq).2.1
  · intro ht
    obtain ⟨hs, hX⟩ := Finset.mem_filter.mp ht
    obtain ⟨hpair, hqN, hqprime, hprod, hcut, hcentre⟩ :=
      mem_p5z_u9_switchedLabels_iff.mp hs
    obtain ⟨hpairCarrier, hpH, hpD, hrD, hrcap⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hp, hr⟩ := Finset.mem_product.mp hpairCarrier
    have hpData := mem_chenAdditivePrimeCarrier.mp hp
    have hrData := mem_chenAdditivePrimeCarrier.mp hr
    have hqle : q ≤ p * r * q := Nat.le_mul_of_pos_left q (mul_pos hpData.2.1.pos hrData.2.1.pos)
    have hqcop : Nat.Coprime q N :=
      (Nat.coprime_mul_iff_left.mp (p5z_u9_order_product_coprime hs)).2
    have hq : q ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier.mpr ⟨hqle.trans_lt hprod, hqprime, hqcop⟩
    have hf : factorAllowed N p q := ⟨hp, hq, hpH, hpD⟩
    refine ⟨?_, hrData.2.1⟩
    rw [preprimeRow, if_pos hf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrData.1,
      hrData.2.1.pos, hrData.2.2, hrD, hrcap, hprod, hcut, hcentre, hX⟩

def rowLower (N : ℕ) (X : ℝ) (p q : ℕ) : ℕ :=
  max 1 (max (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)))
    (max (Nat.ceil ((N : ℝ) / ((p : ℝ) * (q : ℝ) ^ 2)))
      (Nat.floor (X / ((p : ℝ) * (q : ℝ))) + 1)))

def rowUpper (N p q : ℕ) : ℕ :=
  min N (min (Nat.ceil (Real.sqrt ((N : ℝ) / (p : ℝ))))
    (Nat.ceil ((N : ℝ) / ((p : ℝ) * (q : ℝ)))))

private theorem sqrt_gate_iff {N p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    Real.sqrt ((N : ℝ) / ((p : ℝ) * (r : ℝ))) ≤ (q : ℝ) ↔
      (N : ℝ) / ((p : ℝ) * (q : ℝ) ^ 2) ≤ (r : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.sqrt_le_iff]
  simp only [Nat.cast_nonneg, true_and]
  rw [div_le_iff₀ (mul_pos hpR hrR), div_le_iff₀ (mul_pos hpR (sq_pos_of_pos hqR))]
  constructor <;> intro h <;> nlinarith only [h]

/-- Exact intervalization, including strict upper product and square-root
endpoints and the strict old near-cap endpoint X. No boundary is discarded. -/
theorem preprimeRow_eq_interval {N p q : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) :
    preprimeRow N X p q =
      (Finset.Ico (rowLower N X p q) (rowUpper N p q)).filter
        (fun r => Nat.Coprime r N ∧ Nat.Coprime (N - p * r * q) N) := by
  have hp := (mem_chenAdditivePrimeCarrier.mp hf.1).2.1.pos
  have hq := (mem_chenAdditivePrimeCarrier.mp hf.2.1).2.1.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR := mul_pos hpR hqR
  have hXdiv : 0 ≤ X / ((p : ℝ) * (q : ℝ)) := div_nonneg hX hmR.le
  ext r
  rw [preprimeRow, if_pos hf]
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    rowLower, rowUpper, max_le_iff, lt_min_iff, Nat.ceil_le, Nat.lt_ceil,
    Nat.add_one_le_iff, Nat.floor_lt hXdiv]
  have hprod : p * r * q < N ↔ (r : ℝ) < (N : ℝ) / ((p : ℝ) * (q : ℝ)) := by
    rw [lt_div_iff₀ hmR]
    constructor <;> intro h
    · have hh : (p : ℝ) * (r : ℝ) * (q : ℝ) < N := by exact_mod_cast h
      nlinarith only [hh]
    · have hh : (p : ℝ) * (r : ℝ) * (q : ℝ) < N := by nlinarith only [h]
      exact_mod_cast hh
  have hcap : X < (p * r * q : ℕ) ↔ X / ((p : ℝ) * (q : ℝ)) < (r : ℝ) := by
    rw [div_lt_iff₀ hmR]
    push_cast
    constructor <;> intro h <;> nlinarith only [h]
  by_cases hr : 0 < r
  · have hs := sqrt_gate_iff hp hq hr
    have hr1 : 1 ≤ r := hr
    rw [hprod, hcap, hs]
    tauto
  · have hr1 : ¬1 ≤ r := by omega
    simp only [hr, hr1, false_and, and_false]

theorem interval_product_lt {N p q r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hr : r < rowUpper N p q) : p * r * q < N := by
  have hmR : (0 : ℝ) < (p : ℝ) * (q : ℝ) := by positivity
  have hupper : rowUpper N p q ≤ Nat.ceil ((N : ℝ) / ((p : ℝ) * (q : ℝ))) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hquot : r < Nat.ceil ((N : ℝ) / ((p : ℝ) * (q : ℝ))) :=
    hr.trans_le hupper
  have hreal := (lt_div_iff₀ hmR).mp (Nat.lt_ceil.mp hquot)
  have hprod : (p : ℝ) * (r : ℝ) * (q : ℝ) < N := by nlinarith only [hreal]
  exact_mod_cast hprod

/-- The old centre mask is redundant only after the actual strict product
bound and the centre-coprimality of BOTH complementary factors are proved.
This identity makes its periodic residue implementation legitimate. -/
theorem preprimeRow_eq_interval_coprime {N p q : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) :
    preprimeRow N X p q =
      (Finset.Ico (rowLower N X p q) (rowUpper N p q)).filter
        (fun r => Nat.Coprime r N) := by
  rw [preprimeRow_eq_interval hf hX]
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, hcop, _⟩
    exact ⟨hr, hcop⟩
  · rintro ⟨hr, hcop⟩
    have hp := mem_chenAdditivePrimeCarrier.mp hf.1
    have hq := mem_chenAdditivePrimeCarrier.mp hf.2.1
    have hprod := interval_product_lt hp.2.1.pos hq.2.1.pos (Finset.mem_Ico.mp hr).2
    refine ⟨hr, hcop, ?_⟩
    exact (Nat.coprime_self_sub_left hprod.le).mpr
      (Nat.coprime_mul_iff_left.mpr
        ⟨Nat.coprime_mul_iff_left.mpr ⟨hp.2.2, hcop⟩, hq.2.2⟩)

end
end ImbalancedChen.U9SemiprimeSwitch
