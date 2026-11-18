import ImbalancedChen.P3ActualMarkedOddHBTargetSupport

/-!
P3.6 — exact 2-primary support of the genuine marked/rough HB full-target fibre.

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (HB) and §4 (F), especially the separately paid product=T exception;
paper/source/manuscript-body.tex eq:current-PP.

The predecessor only removed ODD external marked integers for an EVEN target.
The literal strict rough projector at z >= 2 actually removes every term
whose marked integer r has a DIFFERENT 2-adic divisibility profile from N.
Indeed, if r*n=N and the original HB occurrence is nonzero, then n must
be odd; coprime cancellation yields 2^k | r iff 2^k | N for every k.
This is an exact finite support theorem, not a divisor-moment estimate,
a new source selection condition, or an admission of every PP compiler word.
All original HB occurrences, per-slot Mobius/log/unit factors, the
+3,-3,+1 coefficients, full physical product, positional W, signed
integer rho(q), physical Q and exact coprime mean remain unchanged.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualMarkedTwoAdicHBTargetSupport

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualMarkedOddHBTargetSupport
open ImbalancedChen.P3HBEvenRoughTarget
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- The entire 2-primary divisibility profile agrees, including k=0.
This is arithmetic data on the original marked integer, not a PP estimate. -/
def sameTwoProfile (N r : ℕ) : Prop :=
  ∀ k : ℕ, ((2 : ℕ) ^ k ∣ N) ↔ ((2 : ℕ) ^ k ∣ r)

/-- An odd HB cofactor in an exact physical product cannot change the
2-primary profile. Uses the prime-2 coprimality theorem and cancellation,
not an assumed valuation identity or a new coefficient hypothesis. -/
theorem sameTwoProfile_of_odd_cofactor
    (N r n : ℕ) (hfull : r * n = N) (hn : Odd n) :
    sameTwoProfile N r := by
  have hnNotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  have hnot2 : ¬ (2 : ℕ) ∣ n := by
    intro htwo
    exact hnNotEven (even_iff_two_dvd.mpr htwo)
  have hcop2 : Nat.Coprime 2 n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2
  intro k
  have hcop : Nat.Coprime ((2 : ℕ) ^ k) n := hcop2.pow_left k
  change ((2 : ℕ) ^ k ∣ N) ↔ ((2 : ℕ) ^ k ∣ r)
  rw [← hfull]
  exact hcop.dvd_mul_right

/-- For a fixed original physical q, any mismatched 2-primary marked
integer has zero exact-target contribution. The proof does not restrict
W, rho, modulus coprimality, HB tuple length, or log-slot multiplicity. -/
theorem literalMarkedHBTargetAtQ_zero_of_twoProfile_mismatch
    (N r j q : ℕ) (z y : ℝ) (M : Finset ℕ)
    (W : ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hmismatch : ¬ sameTwoProfile N r) :
    literalMarkedHBTargetAtQ N r j q z y M W = 0 := by
  unfold literalMarkedHBTargetAtQ
  apply Finset.sum_eq_zero
  intro n hn
  have hfull : r * n = N := (Finset.mem_filter.mp hn).2
  by_cases hnEven : Even n
  · apply Finset.sum_eq_zero
    intro hb hhb
    have hzero : roughTupleWeight z y (roles j) hb = 0 :=
      literal_occurrence_target_zero z y j n hz hnEven hb hhb
    simp [hzero]
  · have hnOdd : Odd n := Nat.not_even_iff_odd.mp hnEven
    exact (hmismatch (sameTwoProfile_of_odd_cofactor N r n hfull hnOdd)).elim

/-- The genuine signed three-term HB sum uses one unchanged integer rho
for congruence minus the exact coprime mean. A mismatched 2-primary
marked integer contributes zero at every physical modulus. -/
theorem literalMarkedSameRhoDiagonal_zero_of_twoProfile_mismatch
    (N r : ℕ) (z y : ℝ) (M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hmismatch : ¬ sameTwoProfile N r) :
    literalMarkedSameRhoDiagonal N r z y M Q rho W = 0 := by
  unfold literalMarkedSameRhoDiagonal
  apply Finset.sum_eq_zero
  intro q hq
  have hterms :
      (∑ j ∈ Finset.range 3,
        (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          literalMarkedHBTargetAtQ N r j q z y M (W j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [literalMarkedHBTargetAtQ_zero_of_twoProfile_mismatch
      N r j q z y M (W j) hz hmismatch]
    simp
  simp [hterms]

/-- Exact finite-source restriction, with no positivity condition on rho
and no geometric or asymptotic error. For an even N this is strictly
stronger than merely retaining all even marked integers. -/
theorem fullMarkedSameRhoDiagonal_restrict_twoProfile
    (N : ℕ) (z y : ℝ) (R M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) :
    (∑ r ∈ R,
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) =
    (∑ r ∈ R.filter (sameTwoProfile N),
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hprofile : sameTwoProfile N r
  · simp [hprofile]
  · have hzero := literalMarkedSameRhoDiagonal_zero_of_twoProfile_mismatch
      N r z y M Q rho (W r) hz hprofile
    simp [hprofile, hzero]

end
end ImbalancedChen.P3ActualMarkedTwoAdicHBTargetSupport
