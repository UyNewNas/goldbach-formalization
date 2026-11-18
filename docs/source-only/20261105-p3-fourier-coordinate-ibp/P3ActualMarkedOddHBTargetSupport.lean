import ImbalancedChen.P3ActualLiteralHBOnlySameRhoEvenDiagonal

/-!
P3.6 — exact even-target diagonal with a separately retained OUTSIDE
integer marked factor, and the genuine order-three rough HB occurrence.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (HB), §4 (F), complete product = T;
manuscript-body.tex eq:current-PP.

The preceding HB-only source eliminates the exact even target because
every HB position has the original strict rough mask at z >= 2.
Here the outside integer r is NOT declared rough or a prime. For an odd r,
an equality r*n=N with even N forces the HB complete product n even, and
the literal rough HB occurrence vanishes. Thus an arbitrary finite
marked-integer sum can be restricted exactly to NON-ODD outside factors
without changing any coefficient, tuple-dependent weight, q, rho or
the exact coprime mean.

This is a support reduction, NOT an upper bound for the remaining EVEN
outside marked factors. No admission of the full actual compiler,
no empty Gamma mother-word claim, and no shifted divisor moment.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualMarkedOddHBTargetSupport

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBEvenRoughTarget
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- If the external integer is odd, the HB part of an even exact
physical product must be even. This is a genuine integer parity fact,
not a roughness or source-compiler admission assumption. -/
theorem hb_even_of_odd_marked
    (N r n : ℕ) (hN : Even N) (hr : Odd r)
    (hfull : r * n = N) : Even n := by
  have htwo : 2 ∣ r * n := by
    rw [hfull]
    exact even_iff_two_dvd.mp hN
  have hrnot : ¬ (2 ∣ r) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hr
  exact even_iff_two_dvd.mpr
    ((Nat.prime_two.dvd_mul.mp htwo).resolve_left hrnot)

/-- One exact-target physical-q fibre with an arbitrary outside marked
integer r. The HB factor n is enumerated separately from the genuine
ordered 2(j+1)-slot HB tuple, with every individual original mask intact.
The original complex arithmetic occurrence and arbitrary positional W
are retained; fineKernel is the exact count-minus-coprime-mean. -/
def literalMarkedHBTargetAtQ
    (N r j q : ℕ) (z y : ℝ) (M : Finset ℕ)
    (W : ℕ → List ℕ → ℂ) : ℂ :=
  ∑ n ∈ M.filter (fun n => r * n = N),
    ∑ hb ∈ factorTuples (2 * (j + 1)) n,
      (W n hb * roughTupleWeight z y (roles j) hb) *
        (((fineKernel N q (r * n) : ℝ) : ℂ))

/-- Any odd outside marked integer cannot sustain an even-target
diagonal if EVERY genuine HB occurrence slot remains strictly rough.
No coprimality condition on q, and no positive/signed bound on W. -/
theorem literalMarkedHBTargetAtQ_zero_odd
    (N r j q : ℕ) (z y : ℝ) (M : Finset ℕ)
    (W : ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) (hr : Odd r) :
    literalMarkedHBTargetAtQ N r j q z y M W = 0 := by
  unfold literalMarkedHBTargetAtQ
  apply Finset.sum_eq_zero
  intro n hn
  have hfull : r * n = N := (Finset.mem_filter.mp hn).2
  have hnEven : Even n := hb_even_of_odd_marked N r n hN hr hfull
  apply Finset.sum_eq_zero
  intro hb hhb
  have hzero : roughTupleWeight z y (roles j) hb = 0 :=
    literal_occurrence_target_zero z y j n hz hnEven hb hhb
  simp [hzero]

/-- The original three signed HB coefficients and one unchanged signed
physical rho(q) accompany the exact full-product=N marked diagonal.
No Mobius of the total physical product is substituted for the actual
occurrence-level Mobius/log/one factors. -/
def literalMarkedSameRhoDiagonal
    (N r : ℕ) (z y : ℝ) (M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → List ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, (rho q : ℂ) *
    (∑ j ∈ Finset.range 3,
      (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        literalMarkedHBTargetAtQ N r j q z y M (W j))

theorem literalMarkedSameRhoDiagonal_zero_odd
    (N r : ℕ) (z y : ℝ) (M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) (hr : Odd r) :
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
    rw [literalMarkedHBTargetAtQ_zero_odd N r j q z y M (W j) hz hN hr]
    simp
  simp [hterms]

/-- Exact reduction of a FINITE genuine marked-integer carrier.
Only non-odd outside integers can contribute to an even exact target;
they are NOT proved small. Every marked integer and its positional W
remain in their original occurrence, with one physical rho. -/
theorem fullMarkedSameRhoDiagonal_restrict_nonodd
    (N : ℕ) (z y : ℝ) (R M Q : Finset ℕ)
    (rho : ℕ → ℤ) (W : ℕ → ℕ → ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ r ∈ R,
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) =
    (∑ r ∈ R.filter (fun r => ¬ Odd r),
      literalMarkedSameRhoDiagonal N r z y M Q rho (W r)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hodd : Odd r
  · have hzero := literalMarkedSameRhoDiagonal_zero_odd
      N r z y M Q rho (W r) hz hN hodd
    simp [hodd, hzero]
  · simp [hodd]

end
end ImbalancedChen.P3ActualMarkedOddHBTargetSupport
