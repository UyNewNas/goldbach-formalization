import ImbalancedChen.P2ActualResidualUniverseMass
import ImbalancedChen.P2SourceFormPairRoundedSigmaLevel
import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.ActualPrimeBoxMass

/-!
# Actual canonical-prefix wall payment after the entire residual sum

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Each modulus is split at its actual canonical decreasing prime prefix. The
remaining divisor is summed over the complete target-deleted rough universe.
Squarefreeness derives prefix/tail coprimality and distinct prefix labels;
the reciprocal totient then factors exactly. The finite product image is
majorized before applying the proved full residual Euler-mass envelope.
Thus a true prime wall-strip reserve pays ALL residual moduli, uniformly
in cap, policy and fine mesh. It is not a single-modulus entry estimate.

The still-missing geometric statement is that every mixed warm fibre is
covered by a finite union of these genuine coarse/admission/SourceForm
prefix-wall sets. This file does not assume or declare that coverage, nor
infer full same-rho convergence from a continuous null-set statement.
-/

namespace ImbalancedChen.P2CanonicalWallFullResidualPayment

noncomputable section
open scoped Classical BigOperators
open Set Filter Topology
open P2LowerFiniteCellRounding P2LowerCanonicalRetainedTrace
open P2ActualResidualUniverseMass

abbrev Prefix (j : ℕ) := Fin j → ℕ

def wallTuples {j k : ℕ} (N : ℕ) (a b : Fin j → ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    Finset (Prefix j) :=
  (actualPrimeBoxTuples N a b).filter fun p =>
    actualPrimeTupleLog N p ∈ primeAffineWallStrip L c delta

def wallPairs {j k : ℕ} (N cap : ℕ) (a b : Fin j → ℝ) (w z : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    Finset (Prefix j × ℕ) :=
  (wallTuples N a b L c delta ×ˢ universe N cap w z).filter fun x =>
    Function.Injective x.1 ∧ Nat.Coprime (∏ i, x.1 i) x.2

def pairProduct {j : ℕ} (x : Prefix j × ℕ) : ℕ := (∏ i, x.1 i) * x.2

def liftedModuli {j k : ℕ} (N cap : ℕ) (a b : Fin j → ℝ) (w z : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : Finset ℕ :=
  (wallPairs N cap a b w z L c delta).image pairProduct

private theorem sum_image_le_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) :
    (∑ y ∈ s.image g, f y) ≤ ∑ x ∈ s, f (g x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.image_insert]
      by_cases hg : g x ∈ s.image g
      · rw [Finset.insert_eq_of_mem hg, Finset.sum_insert hx]
        exact ih.trans (le_add_of_nonneg_left (hf (g x)))
      · rw [Finset.sum_insert hg, Finset.sum_insert hx]
        exact add_le_add_left ih _

/-- The full reciprocal-totient modulus sum is paid only after an exact
arithmetic prefix/tail factorization. Product collisions safely overcount. -/
theorem lifted_mass_le_strip_mul_residual {j k : ℕ}
    (N cap : ℕ) (a b : Fin j → ℝ) (w z : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    (∑ q ∈ liftedModuli N cap a b w z L c delta, 1 / (Nat.totient q : ℝ)) ≤
      actualPrimeAffineWallStripMass N a b L c delta * mass N cap w z := by
  have hfactor (x : Prefix j × ℕ) (hx : x ∈ wallPairs N cap a b w z L c delta) :
      1 / (Nat.totient (pairProduct x) : ℝ) =
        (∏ i, 1 / ((x.1 i : ℝ) - 1)) * (1 / (Nat.totient x.2 : ℝ)) := by
    obtain ⟨hxpair, hinj, hcop⟩ := Finset.mem_filter.mp hx
    have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hxpair).1).1
    rw [pairProduct, Nat.totient_mul hcop, Nat.cast_mul, ← one_div_mul_one_div]
    rw [actualPrimeBoxTuple_reciprocalTotient hp hinj]
  calc
    _ ≤ ∑ x ∈ wallPairs N cap a b w z L c delta,
        1 / (Nat.totient (pairProduct x) : ℝ) :=
      sum_image_le_of_nonneg _ _ _ (fun _ => by positivity)
    _ = ∑ x ∈ wallPairs N cap a b w z L c delta,
        (∏ i, 1 / ((x.1 i : ℝ) - 1)) * (1 / (Nat.totient x.2 : ℝ)) :=
      Finset.sum_congr rfl hfactor
    _ ≤ ∑ x ∈ wallTuples N a b L c delta ×ˢ universe N cap w z,
        (∏ i, 1 / ((x.1 i : ℝ) - 1)) * (1 / (Nat.totient x.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x hx _
      have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).1
      exact mul_nonneg (actualPrimeBoxWeight_nonneg hp) (by positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [wallTuples, actualPrimeAffineWallStripMass, mass,
        Finset.sum_mul, Finset.mul_sum]

/-- The prefix is the first j primes in the actual canonical decreasing
word. The construction is total, but its data theorems retain j<=rank. -/
def canonicalPrefix (j r : ℕ) : Prefix j :=
  primeHistoryTuple j ((r.primeFactorsList.reverse.take j).reverse)

def canonicalTail (j r : ℕ) : ℕ := (r.primeFactorsList.reverse.drop j).prod

private theorem prefix_ofFn {j r : ℕ} (hj : j ≤ r.primeFactorsList.length) :
    List.ofFn (canonicalPrefix j r) = r.primeFactorsList.reverse.take j := by
  apply (primeHistoryTuple_ofFn (by
    simp only [List.length_reverse, List.length_take, Nat.min_eq_left hj])).trans
  simp

/-- No arithmetic mass is defined by a proxy image: this set filters the
actual complete rough-modulus carrier by its own canonical prefix wall. -/
def canonicalWallModuli {j k : ℕ} (N cap : ℕ) (omega v : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : Finset ℕ :=
  (universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)).filter fun r =>
    j ≤ r.primeFactorsList.length ∧
      actualPrimeTupleLog N (canonicalPrefix j r) ∈ primeAffineWallStrip L c delta

/-- Canonical decomposition itself supplies the true tuple carrier,
distinct prime labels, complete residual divisor and coprimality. -/
theorem canonical_prefix_tail_data {N cap j r : ℕ} {omega v : ℝ}
    (hr : r ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hj : j ≤ r.primeFactorsList.length) :
    canonicalPrefix j r ∈ actualPrimeBoxTuples N (fun _ => omega) (fun _ => v) ∧
      Function.Injective (canonicalPrefix j r) ∧
      canonicalTail j r ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) ∧
      Nat.Coprime (∏ i, canonicalPrefix j r i) (canonicalTail j r) ∧
      (∏ i, canonicalPrefix j r i) * canonicalTail j r = r := by
  obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe N cap _ _ hr
  have hpref := prefix_ofFn hj
  have hprefixSub : List.ofFn (canonicalPrefix j r) <+
      roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) := by
    rw [hpref]
    exact (List.take_sublist j _).trans hsub
  have htuple : canonicalPrefix j r ∈ actualPrimeBoxTuples N (fun _ => omega) (fun _ => v) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    have hm := mem_roughPrimeUniverse.mp
      (hprefixSub.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))
    exact hm.2
  have hsort : (List.ofFn (canonicalPrefix j r)).Pairwise (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N cap _ _).sublist hprefixSub
  have hinj : Function.Injective (canonicalPrefix j r) :=
    (List.pairwise_ofFn.mp hsort).injective
  have hrec : (∏ i, canonicalPrefix j r i) * canonicalTail j r = r := by
    rw [← List.prod_ofFn, hpref]
    change (r.primeFactorsList.reverse.take j).prod *
      (r.primeFactorsList.reverse.drop j).prod = r
    rw [← List.prod_append, List.take_append_drop]
    exact hprod
  have htaildiv : canonicalTail j r ∣ roughProduct N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) := by
    apply dvd_trans (show canonicalTail j r ∣ r from by
      rw [← hrec]
      exact dvd_mul_left _ _)
    exact (Nat.mem_divisors.mp hr).1
  have htail : canonicalTail j r ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) :=
    Nat.mem_divisors.mpr ⟨htaildiv, (roughProduct_squarefree N cap _ _).ne_zero⟩
  have hsf := universe_squarefree N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) hr
  rw [← hrec] at hsf
  exact ⟨htuple, hinj, htail, Nat.coprime_of_squarefree_mul hsf, hrec⟩

/-- A canonical wall atom maps to a genuine coprime prefix/tail pair.
The residual product and its mass are not discarded. -/
theorem canonicalWallModuli_subset_lifted {j k : ℕ} (N cap : ℕ)
    (omega v : ℝ) (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ)
    (c : Fin k → ℝ) (delta : ℝ) :
    canonicalWallModuli N cap omega v L c delta ⊆
      liftedModuli N cap (fun _ => omega) (fun _ => v)
        ((N : ℝ) ^ omega) ((N : ℝ) ^ v) L c delta := by
  intro r hr
  obtain ⟨hrU, hj, hwall⟩ := Finset.mem_filter.mp hr
  obtain ⟨hp, hinj, hd, hcop, hrec⟩ := canonical_prefix_tail_data hrU hj
  apply Finset.mem_image.mpr
  refine ⟨(canonicalPrefix j r, canonicalTail j r), ?_, hrec⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, hwall⟩, hd⟩, hinj, hcop⟩

/-- Entire canonical-wall reciprocal-totient mass, with every residual
modulus summed. This is the arithmetic estimate needed AFTER wall coverage. -/
theorem canonical_wall_mass_le_strip_mul_full_residual {j k : ℕ}
    (N cap : ℕ) (omega v : ℝ) (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ)
    (c : Fin k → ℝ) (delta : ℝ) :
    (∑ r ∈ canonicalWallModuli N cap omega v L c delta, 1 / (Nat.totient r : ℝ)) ≤
      actualPrimeAffineWallStripMass N (fun _ => omega) (fun _ => v) L c delta *
        mass N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) := by
  calc
    _ ≤ ∑ r ∈ liftedModuli N cap (fun _ => omega) (fun _ => v)
        ((N : ℝ) ^ omega) ((N : ℝ) ^ v) L c delta,
        1 / (Nat.totient r : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalWallModuli_subset_lifted N cap omega v L c delta)
      intro r _ _
      positivity
    _ ≤ _ := lifted_mass_le_strip_mul_residual N cap _ _ _ _ L c delta

/-- Literal coefficient error, using the ACTUAL rounded and raw lower
constructors, restricted to a canonical-prefix wall. -/
def wallRoundingCharge {j k : ℕ} (keep : List ℕ → Bool) (N cap : ℕ)
    (omega v tau : ℝ) (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ)
    (c : Fin k → ℝ) (delta : ℝ) : ℝ :=
  ∑ r ∈ canonicalWallModuli N cap omega v L c delta,
    |P2LowerFiniteCellRounding.coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau r -
      P2LowerFiniteCellRounding.raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) r| /
        (Nat.totient r : ℝ)

theorem wallRoundingCharge_le_two_mass {j k : ℕ}
    (keep : List ℕ → Bool) (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    wallRoundingCharge keep N cap omega v tau L c delta ≤
      2 * (actualPrimeAffineWallStripMass N (fun _ => omega) (fun _ => v) L c delta *
        mass N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)) := by
  apply le_trans ?_ (mul_le_mul_of_nonneg_left
    (canonical_wall_mass_le_strip_mul_full_residual N cap omega v L c delta) (by norm_num))
  unfold wallRoundingCharge
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hc := coefficient_abs_le_one keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau r
  have hr := fixedEvenRoughCoefficient_abs_le_one keep N cap
    ((N : ℝ) ^ omega) ((N : ℝ) ^ v) r
  have ha : |coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau r -
      raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) r| ≤ 2 := by
    have ht := abs_sub_le (coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau r)
      0 (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) r)
    have hraw : |raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) r| ≤ 1 := hr
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (by linarith)
  simpa only [mul_one_div] using div_le_div_of_nonneg_right ha (Nat.cast_nonneg (Nat.totient r))

/-- Reserve -> one fixed positive strip width -> one target threshold,
AFTER the entire residual-modulus sum. The result is uniform in every
later cap, causal policy and rounding mesh, with true arithmetic wall mass. -/
theorem exists_uniform_full_residual_wall_payment {j k : ℕ}
    (omega v : ℝ) (homega : 0 < omega) (hov : omega < v)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
        wallRoundingCharge keep N cap omega v tau L c delta < eta := by
  obtain ⟨C, hC, Nm, hNm, hmass⟩ :=
    exists_eventual_uniform_mass_bound omega v homega hov
  obtain ⟨delta, hdelta, Ns, hNs, hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt homega hov L c hL
      (eta / (2 * C)) (by positivity)
  refine ⟨delta, hdelta, max Nm Ns, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap keep tau
  have hm := hmass N ((le_max_left _ _).trans hN) hEven cap
  have hs := hstrip N ((le_max_right _ _).trans hN)
  have hS0 : 0 ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin j => omega) (fun _ => v) L c delta := by
    unfold actualPrimeAffineWallStripMass
    apply Finset.sum_nonneg
    intro p hp
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  have hupper := mul_le_mul_of_nonneg_left hm hS0
  have hs' :
      actualPrimeAffineWallStripMass N (fun _ : Fin j => omega) (fun _ => v) L c delta *
        (2 * C) < eta := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hs
  have hb := wallRoundingCharge_le_two_mass keep N cap omega v tau L c delta
  nlinarith

end
end ImbalancedChen.P2CanonicalWallFullResidualPayment
