import ImbalancedChen.P3HBMarkedFixedProductFibre
import ImbalancedChen.P3HBRoughLiteralMoment
import Mathlib.Tactic

/-!
P3.6 — quantitative ORIGINAL labelled rough-HB fixed-product fibre.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

This consumes the literal factorTuples, roughTupleWeight, original W(marked,hb)
and genuine global Mobius already present in offMarkedOccurrence. A genuine
pointwise norm bound A on the actual geometry W is the only new elementary
hypothesis; the result is NOT a distribution assumption or PP estimate.

For each fixed residual product n != 0, one actual marked/HB fibre has
absolute mass <= A * log(n) * tau(n)^(2*(j+1)).
The physical signed response remains ONE unchanged sum over Q with the SAME
integer rho and exact coprime mean. The offshift theorem explicitly excludes
the full complete-product target; no divisors at zero are used.
Pinned manuscript: 9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2-4 (HB),(T),(F). Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBMarkedFixedProductMassBound

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P3HBMarkedFixedProductFibre
open ImbalancedChen.P3HBRoughLiteralMoment

/-- Sum the absolute masses of every ORIGINAL ordered occurrence, without
quotienting labels, and with its actual global full-product Mobius. -/
def originalHBFixedAbsoluteMass
    (n j : ℕ) (z y : ℝ)
    (W : List ℕ × List ℕ → ℂ) (marked : List ℕ) : ℝ :=
  ∑ hb ∈ factorTuples (2 * (j + 1)) n,
    ‖offMarkedOccurrence j z y W marked hb‖

/-- One-bounded global Mobius is evaluated on the ACTUAL complete marked*HB
product; factorTuples_spec is used to make it constant on this fibre.
The bound A is a genuine geometry sup norm, not a PP-shaped assumption. -/
theorem originalHBFixedAbsoluteMass_le_rough
    (n j : ℕ) (z y : ℝ)
    (W : List ℕ × List ℕ → ℂ) (marked : List ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hW : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb)‖ ≤ A) :
    originalHBFixedAbsoluteMass n j z y W marked ≤
      A * roughLiteralHBAbsMass z y j n := by
  classical
  have hmuR :
      |((ArithmeticFunction.moebius (marked.prod * n) : ℝ))| ≤ (1 : ℝ) := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one
      (n := marked.prod * n))
  have hmuC :
      ‖(((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))‖ ≤
        (1 : ℝ) := by
    simpa only [Complex.norm_real] using hmuR
  calc
    originalHBFixedAbsoluteMass n j z y W marked =
      ∑ hb ∈ factorTuples (2 * (j + 1)) n,
        (‖W (marked, hb)‖ * ‖roughTupleWeight z y (roles j) hb‖) *
          ‖(((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))‖ := by
      unfold originalHBFixedAbsoluteMass
      apply Finset.sum_congr rfl
      intro hb hhb
      have hp : hb.prod = n :=
        (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
      simp only [offMarkedOccurrence, norm_mul, hp]
    _ ≤ ∑ hb ∈ factorTuples (2 * (j + 1)) n,
          A * ‖roughTupleWeight z y (roles j) hb‖ := by
      apply Finset.sum_le_sum
      intro hb hhb
      have hrough : 0 ≤ ‖roughTupleWeight z y (roles j) hb‖ :=
        norm_nonneg _
      have hbase : 0 ≤ A * ‖roughTupleWeight z y (roles j) hb‖ :=
        mul_nonneg hA hrough
      calc
        _ ≤ (A * ‖roughTupleWeight z y (roles j) hb‖) *
              ‖(((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hW hb hhb) hrough) (norm_nonneg _)
        _ ≤ (A * ‖roughTupleWeight z y (roles j) hb‖) * 1 :=
          mul_le_mul_of_nonneg_left hmuC hbase
        _ = _ := by ring
    _ = A * roughLiteralHBAbsMass z y j n := by
      simp only [roughLiteralHBAbsMass, Finset.mul_sum]

/-- Genuine fixed-product coefficient bound, with exactly one original
HB log slot and the ACTUAL 2(j+1) ordered positions. The strict rough
projector cannot enlarge the source's original literal mass. -/
theorem originalHBFixedOccurrenceMass_norm_le_tau
    (n j : ℕ) (z y : ℝ)
    (W : List ℕ × List ℕ → ℂ) (marked : List ℕ)
    (A : ℝ) (hn : n ≠ 0) (hA : 0 ≤ A)
    (hW : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb)‖ ≤ A)
    (hz : 0 ≤ z) :
    ‖originalHBFixedOccurrenceMass n j z y W marked‖ ≤
      A * Real.log (n : ℝ) * ((n.divisors.card : ℝ) ^ (2 * (j + 1))) := by
  calc
    ‖originalHBFixedOccurrenceMass n j z y W marked‖
        ≤ originalHBFixedAbsoluteMass n j z y W marked := by
      unfold originalHBFixedOccurrenceMass originalHBFixedAbsoluteMass
      exact norm_sum_le _ _
    _ ≤ A * roughLiteralHBAbsMass z y j n :=
      originalHBFixedAbsoluteMass_le_rough n j z y W marked A hA hW
    _ ≤ A * (Real.log (n : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) :=
      mul_le_mul_of_nonneg_left
        (roughLiteralHBAbsMass_le_tau_pow hz y j n hn) hA
    _ = _ := by ring

/-- This is the SAME signed physical response, not a separate sum of
absolute q-errors. The zero complete shift is explicitly excluded; the
target diagonal retains its separate ledger and cannot use tau(0). -/
theorem offshift_fixed_hb_physical_norm_le_tau
    (N n j : ℕ) (z y : ℝ)
    (W : List ℕ × List ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (A : ℝ) (hn : n ≠ 0) (hA : 0 ≤ A)
    (hW : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb)‖ ≤ A)
    (hz : 0 ≤ z) (hoff : marked.prod * n ≠ N) :
    ‖originalHBFixedOccurrenceMass n j z y W marked *
        offMarkedPhysicalResponse marked.prod N n Q rho‖ ≤
      (A * Real.log (n : ℝ) *
        ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) *
          ‖offMarkedPhysicalResponse marked.prod N n Q rho‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (originalHBFixedOccurrenceMass_norm_le_tau
      n j z y W marked A hn hA hW hz) (norm_nonneg _)

end ImbalancedChen.P3HBMarkedFixedProductMassBound
