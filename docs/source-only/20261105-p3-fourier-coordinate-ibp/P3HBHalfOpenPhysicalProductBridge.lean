import ImbalancedChen.P3HBHalfOpenDyadicSubdivision
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
P3.6: discharge the genuine six-position padded-product premise in the
half-open HB R/128 geometric candidate from the ACTUAL original
\`factorTuples_spec\`. No new analytic/distribution input.

SOURCE_ONLY / NO LEAN COMPILATION / NO KERNEL VALIDATION.
Original manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (HB six-slot dyadic rectangle scales).
Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

WARNING: the refined pieces are sharp half-open indicators, NOT
C-infinity Fourier-admissible original W_T profiles. This file only
pays an algebraic factorTuple-to-six-coordinate bridge and its
conditional live-box consequence, NOT manuscript (S), (F), or PP.
-/
namespace ImbalancedChen.P3HBHalfOpenPhysicalProductBridge
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P3HBHalfOpenDyadicSubdivision

/-- Fixed-length list algebra: the six actual slots followed by unit
padding have exactly the original list product. The cases are exhaustive
because length is at most six; no product equality is an assumption. -/
private theorem paddedSixNatProduct (hb : List ℕ) (hlen : hb.length ≤ 6) :
    (∏ i : Fin 6, hb.getD i.val 1) = hb.prod := by
  rw [Fin.prod_univ_six]
  match hb with
  | [] => simp [List.getD]
  | [a] => simp [List.getD]
  | [a, b] => simp [List.getD, mul_assoc]
  | [a, b, c] => simp [List.getD, mul_assoc]
  | [a, b, c, d] => simp [List.getD, mul_assoc]
  | [a, b, c, d, e] => simp [List.getD, mul_assoc]
  | [a, b, c, d, e, f] => simp [List.getD, mul_assoc]
  | a :: b :: c :: d :: e :: f :: g :: rest =>
      simp at hlen

/-- Real padded six-axis product is the original n for any actual
ordered r-factor HB fibre, as soon as r ≤ 6. -/
theorem factorTuple_paddedSix_product
    {r n : ℕ} {hb : List ℕ}
    (hhb : hb ∈ factorTuples r n) (hr : r ≤ 6) :
    (∏ i : Fin 6, ((hb.getD i.val 1 : ℕ) : ℝ)) = (n : ℝ) := by
  have hspec := factorTuples_spec r n hb hhb
  have hlen : hb.length ≤ 6 := by omega
  have hnat : (∏ i : Fin 6, hb.getD i.val 1) = n := by
    rw [paddedSixNatProduct hb hlen, hspec.2.1]
  exact_mod_cast hnat

/-- On each genuine order-three HB source, j=0,1,2 implies r=2,4,6;
there is no separate padded-product hypothesis. -/
theorem originalHB_paddedSix_product
    {j n : ℕ} {hb : List ℕ}
    (hj : j ∈ Finset.range 3)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n) :
    (∏ i : Fin 6, ((hb.getD i.val 1 : ℕ) : ℝ)) = (n : ℝ) := by
  apply factorTuple_paddedSix_product hhb
  have := Finset.mem_range.mp hj
  omega

/-- Remove hphysical from the prior HALF-OPEN R/128 lemma, for the
ACTUAL original rank 2/4/6 HB occurrences. All remaining assumptions
are literal cutoff plateaux, a live refined rectangle, and the actual
nonzero smooth complete-group cutoff. No distributional error is assumed.
The half-open indicator is still discontinuous and cannot feed (F). -/
theorem originalHB_halfOpen_live_R128
    (chi : ℝ → ℂ) (label : Fin 6 → ℕ) (side : Fin 6 → Bool)
    (marked hb : List ℕ) (j n : ℕ) (R : ℝ)
    (hj : j ∈ Finset.range 3)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hR : 0 < R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hgroup : chi ((n : ℝ) / R) - chi (2 * (n : ℝ) / R) ≠ 0)
    (hlive : hbHalfCut chi label side marked hb ≠ 0) :
    R / 128 < ∏ i : Fin 6, hbHalfLower label side i := by
  exact hbHalfCut_live_R128 chi label side marked hb n R
    hR hsmall hlarge hgroup hlive
    (originalHB_paddedSix_product hj hhb)

end ImbalancedChen.P3HBHalfOpenPhysicalProductBridge
