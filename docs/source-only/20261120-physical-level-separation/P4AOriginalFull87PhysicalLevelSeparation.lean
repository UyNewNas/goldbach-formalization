import ImbalancedChen.P4AOriginalFull87UpperRoomNoProperMultiple
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A necessary correction to the proposed connection with manuscript
eq:current-PP. The modulus Q=a*(p::pre).prod of the ORIGINAL reflected
one-shell AP identity is > N/2. A physical sieve coefficient whose
support is bounded by B with 2*B <= N therefore CANNOT be evaluated
on any such Q. The support cutoffs and the reflected quotient are two
DIFFERENT roles; the latter must not be silently substituted for the
physical small/rough sieve modulus.

These are exact finite arithmetic and support-separation statements
on the original room. They do not define a substitute rho, change the
actual fifth/sixth policy, assign a fake smooth W_N, or apply PP.
The final physical level B and its bound must be proved separately
for the frozen physical coefficient. No statement about the original
unweighted full-Q AP ledger being zero is made.
-/

namespace ImbalancedChen.P4AOriginalFull87PhysicalLevelSeparation
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom)
open P4AOriginalFull87UpperRoomNoProperMultiple
  (actual_upper_room_modulus_exceeds_half)
open P4AOriginalFull87OneShellAPGap
  (actualFullQPrimitiveAPFibre)

/-- On the actual (not enlarged or re-filtered) PLUS-Rosser room, the
full reflected shell modulus lies strictly beyond EVERY cutoff B
that satisfies 2*B <= N. This is a support contradiction, not an
analytic large-modulus estimate. -/
theorem actual_upper_full_q_exceeds_any_half_level
    (N cap B : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (hB : 2 * B ≤ N)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    B < a * (p :: pre).prod := by
  have hhalf :=
    actual_upper_room_modulus_exceeds_half
      N cap w L X pre p a ha
  omega

/-- The IMAGE of the actual quotient room under a ↦ a*b is disjoint
from an independently supplied physical support of level B. The
support must be the REAL physical coefficient support in applications,
not a surrogate selected to make this statement true. -/
theorem actual_upper_full_q_image_misses_bounded_support
    (N cap B : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (S : Finset ℕ)
    (hB : 2 * B ≤ N)
    (hS : ∀ Q ∈ S, Q ≤ B)
    (Q : ℕ)
    (hQ : Q ∈
      (actualPrimitiveRosserRoom N cap w L X pre p).image
        (fun a => a * (p :: pre).prod)) :
    Q ∉ S := by
  classical
  intro hQS
  obtain ⟨a, ha, hQeq⟩ := Finset.mem_image.mp hQ
  have hlarge : B < a * (p :: pre).prod :=
    actual_upper_full_q_exceeds_any_half_level
      N cap B w L X pre p a hB ha
  have hsmall : Q ≤ B := hS Q hQS
  omega

/-- Conditional on the actual sieve coefficient's stated support
bound, the coefficient is ZERO on every reflected one-shell modulus.
This does NOT say that the original (unweighted) full-Q AP count
vanishes, nor that this rho is certified to be the manuscript rho_N. -/
theorem bounded_physical_coefficient_zero_on_actual_upper_full_q
    (N cap B : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (rho : ℕ → ℝ)
    (hB : 2 * B ≤ N)
    (hrho : ∀ Q, B < Q → rho Q = 0)
    (a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    rho (a * (p :: pre).prod) = 0 := by
  apply hrho
  exact actual_upper_full_q_exceeds_any_half_level
    N cap B w L X pre p a hB ha

/-- An exact signed failure-of-identification diagnostic. Multiplying
the previously defined full-Q AP room by ANY genuinely B-supported
physical coefficient kills every original a-occurrence, including
negative PLUS-beta weights. The original full-Q AP account, which
has NO such rho factor, is not thereby zero.

The conclusion is intentionally local. No masks are inserted into
the real frozen fifth/sixth event lists or the physical ledger. -/
theorem bounded_physical_coefficient_times_original_full_AP_zero
    (N cap B : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ)
    (rho : ℕ → ℝ)
    (hB : 2 * B ≤ N)
    (hrho : ∀ Q, B < Q → rho Q = 0) :
    (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
      actualSmallRosserPlus N cap w L a *
      rho (a * (p :: pre).prod) *
        (((actualFullQPrimitiveAPFibre N
          (a * (p :: pre).prod)).card : ℝ) -
          mean (p :: pre).prod)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hzero :
      rho (a * (p :: pre).prod) = 0 :=
    bounded_physical_coefficient_zero_on_actual_upper_full_q
      N cap B w L X pre p rho hB hrho a ha
  simp [hzero]

end
end ImbalancedChen.P4AOriginalFull87PhysicalLevelSeparation
