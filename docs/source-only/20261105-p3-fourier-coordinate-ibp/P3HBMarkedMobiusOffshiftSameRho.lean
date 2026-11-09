import ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor
import ImbalancedChen.P3ActualMarkedOffShiftDivisors
import Mathlib.Tactic

/-!
P3.6 — complete SAME physical rho, target AND nonzero-shift marked/rough-HB
ledger. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

This uses the original ordered factorTuples occurrences, roughTupleWeight,
literal global Mobius on the COMPLETE product, exact coprime mean, and
physical q. The off-target terms are indexed by the nonzero signed
complete-product shift, NOT the HB residual shift. The target term is
separate, with no divisors at zero.

Only the explicitly global-Mobius marked/rough HB subfamily is covered.
No divisor-moment saving, arbitrary W_T admission, causal rho_T/Q_T
identification, Fourier H-tail payment or complete PP estimate is claimed.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion 20261010 sections 3-4 (T),(F).
-/

namespace ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBMarkedMobiusFourDiagonal
open ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- The literal full marked-product NONZERO shift divisor indicator minus
the EXACT coprime mean. This agrees with fineKernel only off target. -/
def offMarkedPhysicalKernel (r N q n : ℕ) : ℝ :=
  (if q ∈ (markedShiftAbs r N n).divisors then (1 : ℝ) else 0) -
    (if Nat.Coprime (r * n) q then (Nat.totient q : ℝ)⁻¹ else 0)

/-- Same physical Q and same INTEGER rho for a single off-target
complete product. This definition is a finite algebraic response,
not a bound or a new analytic input. -/
def offMarkedPhysicalResponse
    (r N n : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ) : ℂ :=
  ∑ q ∈ Q, (rho q : ℂ) * ((offMarkedPhysicalKernel r N q n : ℝ) : ℂ)

/-- Exactly the original labelled ordered rough HB occurrence, with its
genuine global Mobius (r*n) and its original complex tuple weight. -/
def offMarkedOccurrence
    (j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (marked hb : List ℕ) : ℂ :=
  W (marked, hb) * roughTupleWeight z y (roles j) hb *
    (((ArithmeticFunction.moebius (marked.prod * hb.prod) : ℝ) : ℂ))

/-- Full (unfiltered) physical q-contribution of this precise
marked/ordered-rough HB subfamily. -/
def mobiusMarkedRoughFullAtQ
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ marked ∈ M,
    ∑ hb ∈ factorTuples (2 * (j + 1)) n,
      W (marked, hb) * roughTupleWeight z y (roles j) hb *
        markedResidualKernel marked.prod N q hb.prod

/-- All genuine off-target occurrences; the FULL marked*HB product
is tested, and no factorTuples label or position is merged. -/
def mobiusMarkedRoughOffAtQ
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ marked ∈ M,
    ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod ≠ N),
      W (marked, hb) * roughTupleWeight z y (roles j) hb *
        markedResidualKernel marked.prod N q hb.prod

/-- The unrestricted original source splits into exact-target and
genuinely nonzero-shift fibres before any shifted divisor estimate. -/
theorem mobiusMarkedRoughFullAtQ_split
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) :
    mobiusMarkedRoughFullAtQ N n j q z y M W =
      mobiusMarkedRoughTargetAtQ N n j q z y M W +
        mobiusMarkedRoughOffAtQ N n j q z y M W := by
  classical
  unfold mobiusMarkedRoughFullAtQ mobiusMarkedRoughTargetAtQ
    mobiusMarkedRoughOffAtQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro marked hm
  exact Finset.sum_filter_add_sum_filter_not

/-- The kernel's true nonzero complete shift is a finite divisor test.
The original mean is NOT replaced with the unconditioned 1/phi(q). -/
theorem offMarkedPhysicalKernel_eq_fineKernel
    (r N q n : ℕ) (hne : r * n ≠ N) :
    fineKernel N q (r * n) = offMarkedPhysicalKernel r N q n := by
  simpa only [offMarkedPhysicalKernel] using
    (fineKernel_marked_off_divisors r N q n hne)

/-- The actual global-Mobius HB off-target q mass has an exact
divisor-minus-coprime expansion, keeping original labelled weights. -/
theorem mobiusMarkedRoughOffAtQ_divisors
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) :
    mobiusMarkedRoughOffAtQ N n j q z y M W =
      ∑ marked ∈ M,
        ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
          (fun hb => marked.prod * hb.prod ≠ N),
          offMarkedOccurrence j z y W marked hb *
            ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ) := by
  classical
  unfold mobiusMarkedRoughOffAtQ
  apply Finset.sum_congr rfl
  intro marked hm
  apply Finset.sum_congr rfl
  intro hb hhb
  have hne : marked.prod * hb.prod ≠ N := (Finset.mem_filter.mp hhb).2
  rw [markedResidualKernel_off_divisors
    marked.prod N q hb.prod hne]
  unfold offMarkedOccurrence offMarkedPhysicalKernel
  ring

/-- Finite Fubini keeps the signed rho sum INSIDE each original
labelled occurrence. There is no sum of separate absolute q errors,
and no replacement by a residual-only product. -/
theorem mobiusMarkedRoughOff_same_rho_fubini
    (N n j : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      mobiusMarkedRoughOffAtQ N n j q z y M W) =
      ∑ marked ∈ M,
        ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
          (fun hb => marked.prod * hb.prod ≠ N),
          offMarkedOccurrence j z y W marked hb *
            offMarkedPhysicalResponse marked.prod N hb.prod Q rho := by
  classical
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
          ∑ marked ∈ M,
            ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
              (fun hb => marked.prod * hb.prod ≠ N),
              offMarkedOccurrence j z y W marked hb *
                ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [mobiusMarkedRoughOffAtQ_divisors]
    _ = ∑ q ∈ Q, ∑ marked ∈ M,
          ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
            (fun hb => marked.prod * hb.prod ≠ N),
            (rho q : ℂ) * (offMarkedOccurrence j z y W marked hb *
              ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro marked hm
          rw [Finset.mul_sum]
    _ = ∑ marked ∈ M, ∑ q ∈ Q,
          ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
            (fun hb => marked.prod * hb.prod ≠ N),
            (rho q : ℂ) * (offMarkedOccurrence j z y W marked hb *
              ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ)) :=
        Finset.sum_comm
    _ = ∑ marked ∈ M,
          ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
            (fun hb => marked.prod * hb.prod ≠ N),
            ∑ q ∈ Q, (rho q : ℂ) *
              (offMarkedOccurrence j z y W marked hb *
                ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro marked hm
          exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro marked hm
      apply Finset.sum_congr rfl
      intro hb hhb
      unfold offMarkedPhysicalResponse
      calc
        _ = ∑ q ∈ Q, offMarkedOccurrence j z y W marked hb *
              ((rho q : ℂ) *
                ((offMarkedPhysicalKernel marked.prod N q hb.prod : ℝ) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = _ := by rw [Finset.mul_sum]

/-- The original signed three HB terms still share ONE physical rho
when the complete source is split at b=N. -/
theorem signed_three_full_split
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughFullAtQ N n j q z y M W) =
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) +
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughOffAtQ N n j q z y M W) := by
  classical
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          (mobiusMarkedRoughTargetAtQ N n j q z y M W +
            mobiusMarkedRoughOffAtQ N n j q z y M W) := by
          apply Finset.sum_congr rfl
          intro q hq
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [mobiusMarkedRoughFullAtQ_split]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]

/-- Exact original signed order-three off-target response, reordered by
the original HB positions and complete-product divisors, without taking
absolute values before the q sum. -/
theorem signed_three_off_same_rho_fubini
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughOffAtQ N n j q z y M W) =
    ∑ j ∈ Finset.range 3,
      (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
        (∑ marked ∈ M,
          ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
              (fun hb => marked.prod * hb.prod ≠ N),
            offMarkedOccurrence j z y W marked hb *
              offMarkedPhysicalResponse marked.prod N hb.prod Q rho) := by
  classical
  calc
    _ = ∑ q ∈ Q, ∑ j ∈ Finset.range 3,
          (rho q : ℂ) *
            (((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
              mobiusMarkedRoughOffAtQ N n j q z y M W) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range 3, ∑ q ∈ Q,
          (rho q : ℂ) *
            (((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
              mobiusMarkedRoughOffAtQ N n j q z y M W) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range 3,
          (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
            (∑ q ∈ Q, (rho q : ℂ) *
              mobiusMarkedRoughOffAtQ N n j q z y M W) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mobiusMarkedRoughOff_same_rho_fubini]

/-- Exact signed full-modulus marked/rough HB ledger:
global-mu diagonal + signed off-target complete-product divisor response.
This is a finite identity, NOT a uniform PP estimate or arithmetic saving. -/
theorem signed_three_full_target_and_off_same_rho
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughFullAtQ N n j q z y M W) =
    ((((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        physicalRhoTargetKernel N Q rho) *
          hbThreeTargetMass N n z y M W) +
      (∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          (∑ marked ∈ M,
            ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
                (fun hb => marked.prod * hb.prod ≠ N),
              offMarkedOccurrence j z y W marked hb *
                offMarkedPhysicalResponse marked.prod N hb.prod Q rho)) := by
  calc
    _ = (∑ q ∈ Q, (rho q : ℂ) *
          ∑ j ∈ Finset.range 3,
            (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
              mobiusMarkedRoughTargetAtQ N n j q z y M W) +
        (∑ q ∈ Q, (rho q : ℂ) *
          ∑ j ∈ Finset.range 3,
            (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
              mobiusMarkedRoughOffAtQ N n j q z y M W) :=
        signed_three_full_split N n z y M W Q rho
    _ = _ := by
      rw [signed_three_mobius_target_exact_factor,
        signed_three_off_same_rho_fubini]

end
end ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
