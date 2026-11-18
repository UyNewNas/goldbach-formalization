import ImbalancedChen.P3ActualMarkedTwoAdicHBTargetSupport

/-!
P3.6 — complete small-prime profile support of the literal rough HB
exact-target fibre. Frozen paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (HB strict rough mask), §4 (F, complete-product=T exceptional term).

The preceding two-adic restriction is only the p=2 instance. In a
genuine nonzero ordered rough HB occurrence, the complete HB cofactor n
has NO prime divisor p with p <= z. Thus, when r*n=N, EVERY power of
EVERY such prime has the same divisibility status in r and N. This
removes entire exact-target fibres at the actual rough cutoff, not just
a fixed prime-2 mismatch, while preserving the signed original HB
occurrences, original q, integer rho, and exact coprime mean.

No claim that the full PP source compiler emits only this finite
carrier; no estimate for surviving r, no external input and no axiom.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualMarkedAllSmallPrimeHBTargetSupport

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.Part3
open ImbalancedChen.P3ActualMarkedOddHBTargetSupport
open ImbalancedChen.P3ActualMarkedTwoAdicHBTargetSupport
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Every prime at or below the ORIGINAL strict rough cutoff has
identical power-divisibility profile in the physical target and
the external marked integer. There is no floor(z) substitution. -/
def sameSmallPrimeProfiles (z : ℝ) (N r : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ z →
    ∀ k : ℕ, (p ^ k ∣ N) ↔ (p ^ k ∣ r)

/-- An actually nonzero original rough HB occurrence supplies ALL
small-prime profiles. The proof obtains coprimality of the literal
HB cofactor from the existing roughOneSlot support theorem, not from
an assumed "admitted coefficient" field. -/
theorem sameSmallPrimeProfiles_of_literal_occurrence
    (N r n j : ℕ) (z y : ℝ) (hb : List ℕ)
    (hfull : r * n = N)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hweight : roughTupleWeight z y (roles j) hb ≠ 0) :
    sameSmallPrimeProfiles z N r := by
  intro p hp hpz k
  have hz0 : (0 : ℝ) ≤ z :=
    (Nat.cast_nonneg p).trans hpz
  have hmask : roughOneSlot z n ≠ 0 := by
    intro hzero
    apply hweight
    rw [actual_word_mask (z := z) hz0 y j n hb hhb, hzero]
    simp
  have hsupport := roughOneSlot_support z n hmask
  have hnotdiv : ¬ p ∣ n := by
    intro hd
    exact (not_lt_of_ge hpz) (hsupport p hp hd)
  have hcop : Nat.Coprime p n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdiv
  have hcopPow : Nat.Coprime (p ^ k) n := hcop.pow_left k
  change (p ^ k ∣ N) ↔ (p ^ k ∣ r)
  rw [← hfull]
  exact hcopPow.dvd_mul_right

/-- The target fibre at one unchanged physical modulus q vanishes when
the external marked integer misses ANY original small-prime power. -/
theorem literalMarkedHBTargetAtQ_zero_of_smallPrime_mismatch
    (N r j q : ℕ) (z y : ℝ) (M : Finset ℕ)
    (W : ℕ → List ℕ → ℂ)
    (hmismatch : ¬ sameSmallPrimeProfiles z N r) :
    literalMarkedHBTargetAtQ N r j q z y M W = 0 := by
  unfold literalMarkedHBTargetAtQ
  apply Finset.sum_eq_zero
  intro n hn
  have hfull : r * n = N := (Finset.mem_filter.mp hn).2
  apply Finset.sum_eq_zero
  intro hb hhb
  by_cases hw : roughTupleWeight z y (roles j) hb = 0
  · simp [hw]
  · have hprofile : sameSmallPrimeProfiles z N r :=
      sameSmallPrimeProfiles_of_literal_occurrence
        N r n j z y hb hfull hhb hw
    exact (hmismatch hprofile).elim

/-- Sum the EXACT original three signed HB occurrence terms with the
same integer rho(q) and original count-minus-coprime-mean fineKernel.
No positivity or density assumption on rho is made. -/
theorem literalMarkedSameRhoDiagonal_zero_of_smallPrime_mismatch
    (N r : ℕ) (z y : ℝ) (M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → List ℕ → ℂ)
    (hmismatch : ¬ sameSmallPrimeProfiles z N r) :
    literalMarkedSameRhoDiagonal N r z y M Q rho W = 0 := by
  unfold literalMarkedSameRhoDiagonal
  apply Finset.sum_eq_zero
  intro q hq
  have hterms :
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          literalMarkedHBTargetAtQ N r j q z y M (W j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [literalMarkedHBTargetAtQ_zero_of_smallPrime_mismatch
      N r j q z y M (W j) hmismatch]
    simp
  simp [hterms]

/-- An arbitrary finite carrier of external marked INTEGERS is
restricted exactly to the SAME complete small-prime power profiles as
the original target N, uniformly in the varying real cutoff z.
Every surviving occurrence, signed coefficient, physical q, rho(q)
and exact coprime mean is left untouched. -/
theorem fullMarkedSameRhoDiagonal_restrict_smallPrimeProfiles
    (N : ℕ) (z y : ℝ) (R M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → ℕ → List ℕ → ℂ) :
    (∑ r ∈ R,
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) =
    (∑ r ∈ R.filter (sameSmallPrimeProfiles z N),
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : sameSmallPrimeProfiles z N r
  · simp [hp]
  · have hzero :=
      literalMarkedSameRhoDiagonal_zero_of_smallPrime_mismatch
        N r z y M Q rho (W r) hp
    simp [hp, hzero]

end
end ImbalancedChen.P3ActualMarkedAllSmallPrimeHBTargetSupport
