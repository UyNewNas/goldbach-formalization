import ImbalancedChen.ActualUpperPolicyFiniteBridge
import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import ImbalancedChen.P3ActualU8CommonCarrierPP
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A genuine EVEN-RETAINING first-exit tree produces INTEGER rough
Möbius coefficients on its literal original support. Its physical
coefficient is the same signed small-Rosser attachment used in the
actual U8 sharp-K triple source. This identifies a non-arbitrary
rough candidate without assuming the final frozen whole-domain
causal compiler has been constructed.

The original physical triple weight and all p₂=q occurrences remain.
The majorant, complete signed PP, density and exact primitive mean
are evaluated at ONE physical coefficient. When the compiler's rough
values are literally these first-exit values, its common-carrier
coefficient delta vanishes, not just its abstract L1 upper bound.

This does NOT identify the actual final causal rho_T, prove bounds on
other compiler candidates, or pay any logarithmic PP discrepancy.
-/

namespace ImbalancedChen.P3ActualU8EvenRetainedTreePP

noncomputable section
open scoped BigOperators

private def treeSupport (retained : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  firstExitRetainedModuli retained (roughPrimeUniverse N cap w z)

private def treeCoefficient (retained : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) : ℝ :=
  (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ)

private def treePhysicalQ (retained : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w)
    (treeSupport retained N cap w z)

private def treePhysicalRho (retained : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (treeSupport retained N cap w z)
    (treeCoefficient retained N cap w z)
    (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)

/-- The full finite tree support is the genuine retained raw support,
not an independently selected set or the entire auxiliary level. -/
theorem tree_support_eq_raw (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    treeSupport retained N cap w z =
      fixedRoughSupport (retained false) N cap w z :=
  (UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z).symm

/-- All integer rough values agree, including OFF-support zeros.
No equality is asserted for a different coefficient compiler. -/
theorem tree_coefficient_eq_raw (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    treeCoefficient retained N cap w z =
      fixedRoughCoefficient (retained false) N cap w z := by
  funext d
  exact (UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    retained heven N cap w z d).symm

/-- One literal physical Q and rho, before the test integer or U8
prime-product source is supplied. The SMALL attachment may be real:
only the rough first-exit coefficient is integer-valued. -/
theorem tree_physical_eq_raw (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    treePhysicalQ retained N cap w z =
        actualSmallRoughModuli (retained false) N cap w z ∧
    treePhysicalRho retained N cap w z L =
        actualSmallRoughRho (retained false) N cap w z L := by
  constructor
  · change smallRoughModuli (actualSmallRosserSupport N cap w)
        (treeSupport retained N cap w z) =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (fixedRoughSupport (retained false) N cap w z)
    rw [tree_support_eq_raw retained heven N cap w z]
  · change smallRoughRho (actualSmallRosserSupport N cap w)
        (treeSupport retained N cap w z)
        (treeCoefficient retained N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L)
    rw [tree_support_eq_raw retained heven N cap w z,
      tree_coefficient_eq_raw retained heven N cap w z]

/-- Existing actual sieve majorant at this EXACT first-exit physical
coefficient. No distribution estimate is assumed for the majorant. -/
theorem tree_physical_majorant (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (treePhysicalQ retained N cap w z)
        (treePhysicalRho retained N cap w z L) n.natAbs := by
  obtain ⟨hQ, hRho⟩ := tree_physical_eq_raw retained heven N cap w z L
  rw [hQ, hRho]
  exact actualSmallRoughRho_majorant (retained false) N cap w z L
    hL hwL hwz hzcap n

/-- The true ORIGINAL labelled U8 source, with its q=p₂ wall,
has the complete signed same-rho physical decomposition. -/
theorem tree_actual_u8_signed_insertion (retained : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) :
    (∑ m ∈ Finset.range N, P5U8SharpKSource.productWeight N m *
        physicalDivisorSum (treePhysicalQ retained N cap w z)
          (treePhysicalRho retained N cap w z L) (N - m)) =
      p5z_labelledMass (Finset.range N) (P5U8SharpKSource.productWeight N) *
          physicalDensitySum (treePhysicalQ retained N cap w z)
            (treePhysicalRho retained N cap w z L) +
      p5z_labelledCoprimeCorrection (Finset.range N) id
          (P5U8SharpKSource.productWeight N)
          (treePhysicalQ retained N cap w z)
          (treePhysicalRho retained N cap w z L) +
      Part3.primeProductSignedError 3 N N
          (treePhysicalQ retained N cap w z)
          (treePhysicalRho retained N cap w z L)
          (P5U8SharpKSource.physicalWeight N) :=
  P5U8SharpKSource.same_rho_physical_sum_eq_main_correction_PP N _ _

/-- A common carrier may contain compiler-only moduli. If its INTEGER
rough values are literally the original even-retaining tree values,
the complete U8 signed PP discrepancy is EXACTLY the original raw
discrepancy, including the exact coprime mean. This is not true for
an arbitrary different compiled coefficient. -/
theorem tree_actual_u8_PP_common_eq_raw
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hcover : treeSupport retained N cap w z ⊆ rough) :
    Part3.primeProductSignedError 3 N N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (treeCoefficient retained N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L))
        (P5U8SharpKSource.physicalWeight N) =
      Part3.primeProductSignedError 3 N N
        (actualSmallRoughModuli (retained false) N cap w z)
        (actualSmallRoughRho (retained false) N cap w z L)
        (P5U8SharpKSource.physicalWeight N) := by
  have hraw : fixedRoughSupport (retained false) N cap w z ⊆ rough := by
    rw [← tree_support_eq_raw retained heven N cap w z]
    exact hcover
  rw [tree_coefficient_eq_raw retained heven N cap w z]
  exact P3ActualU8CommonCarrierPP.actual_u8_rank3_PP_common_eq_raw
    (retained false) N cap w z L rough hraw

end

end ImbalancedChen.P3ActualU8EvenRetainedTreePP
