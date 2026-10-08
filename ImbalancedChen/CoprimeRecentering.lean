import ImbalancedChen.CurvedRegionDiscrepancy
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp

/-!
# Exact finite recentering over reduced residue classes

For a positive modulus, the actual congruence masses summed over the
canonical reduced residues equal the actual coprime mass. There are exactly
`Nat.totient d` such residues, including the single class `0` when `d = 1`.

Subtracting the average error relative to any residue-independent main term
therefore gives exactly `finitePrimitiveDiscrepancy`. A uniform error bound
`ε` for that main term gives the bound `2 * ε` for the coprime-normalized
discrepancy. All weights may have either sign. No distribution estimate or
analytic assumption is supplied by these finite identities.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Canonical representatives of the reduced residue classes. The lower
bound `0 ≤ a` is automatic because these representatives are natural numbers. -/
def finiteReducedResidues (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun a => Nat.Coprime a d)

@[simp] theorem mem_finiteReducedResidues (a d : ℕ) :
    a ∈ finiteReducedResidues d ↔ a < d ∧ Nat.Coprime a d := by
  simp [finiteReducedResidues]

/-- This is the genuine Euler totient, with no substitute normalizer. -/
@[simp] theorem card_finiteReducedResidues (d : ℕ) :
    (finiteReducedResidues d).card = Nat.totient d := by
  simp only [finiteReducedResidues, Nat.totient_eq_card_coprime,
    Nat.coprime_comm]

@[simp] theorem finiteReducedResidues_one :
    finiteReducedResidues 1 = {0} := by
  simp [finiteReducedResidues]

/-- Reduction modulo `d` preserves the literal coprimality mask. -/
theorem mod_mem_finiteReducedResidues_iff (m d : ℕ) (hd : 0 < d) :
    m % d ∈ finiteReducedResidues d ↔ Nat.Coprime m d := by
  rw [mem_finiteReducedResidues, and_iff_right (Nat.mod_lt m hd)]
  change Nat.gcd (m % d) d = 1 ↔ Nat.gcd m d = 1
  rw [(Nat.mod_modEq m d).gcd_eq]

/-- A single integer belongs to exactly one canonical reduced class if
and only if it is coprime to the modulus. -/
theorem sum_reducedResidues_congruence_indicator
    (m d : ℕ) (c : ℝ) (hd : 0 < d) :
    (∑ a ∈ finiteReducedResidues d,
      if Nat.ModEq d m a then c else 0) =
      if Nat.Coprime m d then c else 0 := by
  classical
  by_cases hcop : Nat.Coprime m d
  · rw [if_pos hcop]
    have hmem : m % d ∈ finiteReducedResidues d :=
      (mod_mem_finiteReducedResidues_iff m d hd).mpr hcop
    calc
      (∑ a ∈ finiteReducedResidues d,
          if Nat.ModEq d m a then c else 0) =
          if Nat.ModEq d m (m % d) then c else 0 := by
        apply Finset.sum_eq_single_of_mem (m % d) hmem
        intro a ha hane
        apply if_neg
        intro hma
        exact hane (Nat.mod_eq_of_modEq hma
          ((mem_finiteReducedResidues a d).mp ha).1).symm
      _ = c := if_pos (Nat.mod_modEq m d).symm
  · rw [if_neg hcop]
    apply Finset.sum_eq_zero
    intro a ha
    apply if_neg
    intro hma
    apply hcop
    change Nat.gcd m d = 1
    rw [hma.gcd_eq]
    exact ((mem_finiteReducedResidues a d).mp ha).2

/-- Exact partition of the actual coprime mass, valid for signed weights. -/
theorem sum_finiteCongruenceMass_reducedResidues
    (S : Finset ℕ) (w : ℕ → ℝ) (d : ℕ) (hd : 0 < d) :
    (∑ a ∈ finiteReducedResidues d, finiteCongruenceMass S w a d) =
      finiteCoprimeMass S w d := by
  classical
  simp only [finiteCongruenceMass, finiteCoprimeMass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact sum_reducedResidues_congruence_indicator m d (w m) hd

/-- Error relative to one common, arbitrary real main term. The main term
is an argument, not a residue-dependent function. -/
def finiteCommonMainError
    (S : Finset ℕ) (w : ℕ → ℝ) (M : ℝ) (a d : ℕ) : ℝ :=
  finiteCongruenceMass S w a d - M

/-- The exact sum of errors relative to a common main term. -/
theorem sum_finiteCommonMainError
    (S : Finset ℕ) (w : ℕ → ℝ) (M : ℝ) (d : ℕ) (hd : 0 < d) :
    (∑ a ∈ finiteReducedResidues d, finiteCommonMainError S w M a d) =
      finiteCoprimeMass S w d - (Nat.totient d : ℝ) * M := by
  simp only [finiteCommonMainError, Finset.sum_sub_distrib,
    sum_finiteCongruenceMass_reducedResidues S w d hd,
    Finset.sum_const, nsmul_eq_mul, card_finiteReducedResidues]

/-- Recenter an error around its reduced-residue average. The arbitrary
common main term cancels exactly, even for a selected noncanonical residue. -/
theorem finiteCommonMainError_sub_average
    (S : Finset ℕ) (w : ℕ → ℝ) (M : ℝ) (a d : ℕ) (hd : 0 < d) :
    finiteCommonMainError S w M a d -
        (∑ b ∈ finiteReducedResidues d, finiteCommonMainError S w M b d) /
          (Nat.totient d : ℝ) =
      finitePrimitiveDiscrepancy S w a d := by
  have hphi : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  rw [sum_finiteCommonMainError S w M d hd]
  unfold finiteCommonMainError finitePrimitiveDiscrepancy
  field_simp [hphi]
  <;> ring

/-- The actual coprime-normalized discrepancies have mean zero over the
canonical reduced classes. -/
theorem sum_finitePrimitiveDiscrepancy_reducedResidues
    (S : Finset ℕ) (w : ℕ → ℝ) (d : ℕ) (hd : 0 < d) :
    (∑ a ∈ finiteReducedResidues d, finitePrimitiveDiscrepancy S w a d) = 0 := by
  have hphi : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  simp only [finitePrimitiveDiscrepancy, Finset.sum_sub_distrib,
    sum_finiteCongruenceMass_reducedResidues S w d hd,
    Finset.sum_const, nsmul_eq_mul, card_finiteReducedResidues]
  field_simp [hphi]
  <;> ring

/-- The average error cannot exceed a uniform absolute error bound.
No sign condition on the weights or the common main term is needed. -/
theorem abs_average_finiteCommonMainError_le
    (S : Finset ℕ) (w : ℕ → ℝ) (M ε : ℝ) (d : ℕ) (hd : 0 < d)
    (hE : ∀ a ∈ finiteReducedResidues d,
      |finiteCommonMainError S w M a d| ≤ ε) :
    |(∑ a ∈ finiteReducedResidues d, finiteCommonMainError S w M a d) /
      (Nat.totient d : ℝ)| ≤ ε := by
  have hphi : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hd
  rw [abs_div, abs_of_pos hphi]
  calc
    |∑ a ∈ finiteReducedResidues d, finiteCommonMainError S w M a d| /
        (Nat.totient d : ℝ) ≤
        (∑ a ∈ finiteReducedResidues d, |finiteCommonMainError S w M a d|) /
          (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hphi.le
    _ ≤ (∑ _a ∈ finiteReducedResidues d, ε) / (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hE) hphi.le
    _ = ε := by
      rw [Finset.sum_const, nsmul_eq_mul, card_finiteReducedResidues]
      field_simp [hphi.ne']
      <;> ring

/-- The selected primitive class costs at most twice any uniform
common-main-term error bound over the canonical reduced classes. -/
theorem abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_commonMainError
    (S : Finset ℕ) (w : ℕ → ℝ) (M ε : ℝ) (a d : ℕ) (hd : 0 < d)
    (ha : a ∈ finiteReducedResidues d)
    (hE : ∀ b ∈ finiteReducedResidues d,
      |finiteCommonMainError S w M b d| ≤ ε) :
    |finitePrimitiveDiscrepancy S w a d| ≤ 2 * ε := by
  rw [← finiteCommonMainError_sub_average S w M a d hd]
  calc
    |finiteCommonMainError S w M a d -
        (∑ b ∈ finiteReducedResidues d, finiteCommonMainError S w M b d) /
          (Nat.totient d : ℝ)| ≤
        |finiteCommonMainError S w M a d| +
          |(∑ b ∈ finiteReducedResidues d, finiteCommonMainError S w M b d) /
            (Nat.totient d : ℝ)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (finiteCommonMainError S w M a d) 0
          ((∑ b ∈ finiteReducedResidues d, finiteCommonMainError S w M b d) /
            (Nat.totient d : ℝ)))
    _ ≤ ε + ε := add_le_add (hE a ha)
      (abs_average_finiteCommonMainError_le S w M ε d hd hE)
    _ = 2 * ε := by ring

/-- An application-facing form with the literal error expression and
explicit canonical primitive-residue conditions. -/
theorem abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform
    (S : Finset ℕ) (w : ℕ → ℝ) (M ε : ℝ) (a d : ℕ) (hd : 0 < d)
    (ha : a < d) (hcop : Nat.Coprime a d)
    (hE : ∀ b : ℕ, b < d → Nat.Coprime b d →
      |finiteCongruenceMass S w b d - M| ≤ ε) :
    |finitePrimitiveDiscrepancy S w a d| ≤ 2 * ε := by
  apply abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_commonMainError
    S w M ε a d hd ((mem_finiteReducedResidues a d).mpr ⟨ha, hcop⟩)
  intro b hb
  obtain ⟨hb, hbcop⟩ := (mem_finiteReducedResidues b d).mp hb
  exact hE b hb hbcop

/-- Reducing a selected residue does not change either literal mass. -/
@[simp] theorem finitePrimitiveDiscrepancy_residue_mod
    (S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S w (a % d) d =
      finitePrimitiveDiscrepancy S w a d := by
  simp only [finitePrimitiveDiscrepancy, finiteCongruenceMass, Nat.ModEq,
    Nat.mod_mod]
  rfl

/-- The canonical uniform bound also controls any primitive residue,
such as the original center `N`, without assuming that it is less than `d`. -/
theorem abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_primitive
    (S : Finset ℕ) (w : ℕ → ℝ) (M ε : ℝ) (a d : ℕ) (hd : 0 < d)
    (hcop : Nat.Coprime a d)
    (hE : ∀ b : ℕ, b < d → Nat.Coprime b d →
      |finiteCongruenceMass S w b d - M| ≤ ε) :
    |finitePrimitiveDiscrepancy S w a d| ≤ 2 * ε := by
  have hmod := (mod_mem_finiteReducedResidues_iff a d hd).mpr hcop
  have hmodcop := ((mem_finiteReducedResidues (a % d) d).mp hmod).2
  simpa only [finitePrimitiveDiscrepancy_residue_mod] using
    abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform
      S w M ε (a % d) d hd (Nat.mod_lt a hd) hmodcop hE

/-- Modulus one is included: its only canonical class is zero and every
integer is coprime to one, so its actual discrepancy vanishes. -/
@[simp] theorem finitePrimitiveDiscrepancy_modulus_one
    (S : Finset ℕ) (w : ℕ → ℝ) (a : ℕ) :
    finitePrimitiveDiscrepancy S w a 1 = 0 := by
  simp [finitePrimitiveDiscrepancy, finiteCongruenceMass, finiteCoprimeMass,
    Nat.ModEq]
  simp only [Nat.mod_one, eq_self_iff_true, Finset.filter_true, sub_self]

end

end ImbalancedChen
