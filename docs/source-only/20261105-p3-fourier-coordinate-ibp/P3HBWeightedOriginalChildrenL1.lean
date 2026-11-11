import ImbalancedChen.P3HBSmoothTensorQuantitativeL1
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
P3.6 / pinned manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 and §4 (F).

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This is the first genuine COUPLED zeroth-order L1 charge for the complete
original three-way six-slot HB smooth child family: the same measurable
geometry W multiplies ALL 3^6 original labelled children before taking
absolute values and integrating. The assumption |W| <= M is an ordinary
zeroth-order geometric envelope; it is NOT a Fourier/PP/discrepancy premise.
No relabelling, change in dyadic scales, rho, physical moduli or means.

Only a bounded measurable geometry is admitted here. No claim is made that
every manuscript physical W_T satisfies a T/m(N)-uniform M, nor that this
pays a mixed Frechet derivative, U5/trim derivatives, Fourier tail,
complete modulus mass, product=T exception or actual same-rho PP.
-/

namespace ImbalancedChen.P3HBWeightedOriginalChildrenL1
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothTensorL1
open ImbalancedChen.P3HBSmoothTensorQuantitativeL1

/-- A real geometry multiplier couples to the original COMPLEX HB child,
without changing the child label. The norm of the complete labelled sum
equals the common geometric modulus times the original norm sum. -/
theorem weighted_children_norm_sum_eq
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℝ) (u : Fin 6 → ℝ) :
    (∑ child ∈ smoothChildren,
      ‖(W u : ℂ) * logTensorMixed chi orders child u‖) =
      |W u| * (∑ child ∈ smoothChildren,
        ‖logTensorMixed chi orders child u‖) := by
  simp_rw [norm_mul, Complex.norm_real]
  rw [Finset.mul_sum]

/-- A bounded measurable coupled geometry preserves Lebesgue
integrability of the COMPLETE original 729-labelled absolute mass.
This uses the pinned Integrable.bdd_mul on the genuine 6D product volume,
rather than an assumed integrability field. -/
theorem weighted_children_norm_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ)
    (W : (Fin 6 → ℝ) → ℝ)
    (hWmeas : Measurable W) (M : ℝ)
    (hWbound : ∀ u, |W u| ≤ M) :
    Integrable (fun u : Fin 6 → ℝ =>
      |W u| * (∑ child ∈ smoothChildren,
        ‖logTensorMixed chi orders child u‖)) := by
  have hmass : Integrable (fun u : Fin 6 → ℝ =>
      ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) :=
    all_logTensorMixed_children_norm_integrable
      chi hchi hsmall hlarge orders
  have hmeas : AEStronglyMeasurable
      (fun u : Fin 6 → ℝ => |W u|) :=
    hWmeas.abs.aestronglyMeasurable
  have hbounded : ∀ᵐ u ∂(volume : Measure (Fin 6 → ℝ)),
      ‖|W u|‖ ≤ M := Filter.Eventually.of_forall (by
    intro u
    simpa only [Real.norm_eq_abs, abs_abs] using hWbound u)
  exact hmass.bdd_mul hmeas hbounded

/-- Nontrivial COUPLED L1 inequality: one common geometry is multiplied
into all 3^6 original labelled HB child tensors. Its cost is the actual
ordinary amplitude M times the previously derived separated HB integral.
There is no hypothesis equivalent to a Fourier or PP conclusion. -/
theorem weighted_children_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (orders : Fin 6 → ℕ)
    (horders : ∀ i : Fin 6, orders i ≤ K)
    (W : (Fin 6 → ℝ) → ℝ)
    (hWmeas : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hWbound : ∀ u, |W u| ≤ M) :
    (∫ u : Fin 6 → ℝ,
      |W u| * (∑ child ∈ smoothChildren,
        ‖logTensorMixed chi orders child u‖)) ≤
      M * ((smoothChildren.card : ℝ) *
        ((2 * Real.log 2) * C) ^ 6) := by
  let mass : (Fin 6 → ℝ) → ℝ := fun u =>
    ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖
  have hmass : Integrable mass :=
    all_logTensorMixed_children_norm_integrable
      chi hchi hsmall hlarge orders
  have hweighted : Integrable (fun u => |W u| * mass u) :=
    weighted_children_norm_integrable
      chi hchi hsmall hlarge orders W hWmeas M hWbound
  have hmajor : Integrable (fun u => M * mass u) :=
    hmass.const_mul M
  have hmass_nonneg (u : Fin 6 → ℝ) : 0 ≤ mass u := by
    dsimp [mass]
    exact Finset.sum_nonneg (fun child _ => norm_nonneg _)
  have hpoint (u : Fin 6 → ℝ) :
      |W u| * mass u ≤ M * mass u :=
    mul_le_mul_of_nonneg_right (hWbound u) (hmass_nonneg u)
  calc
    (∫ u : Fin 6 → ℝ, |W u| * mass u) ≤
        ∫ u : Fin 6 → ℝ, M * mass u :=
      integral_mono hweighted hmajor hpoint
    _ = M * (∫ u : Fin 6 → ℝ, mass u) :=
      integral_const_mul M mass
    _ ≤ M * ((smoothChildren.card : ℝ) *
        ((2 * Real.log 2) * C) ^ 6) :=
      mul_le_mul_of_nonneg_left
        (all_logTensorMixed_children_L1_le
          chi hchi hsmall hlarge K C hC orders horders) hM

/-- Literal original dyadic labels and all their multiplicities survive
the coupling by the SAME W. Still only zeroth-order in the geometry W. -/
theorem weighted_scaled_children_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (label orders : Fin 6 → ℕ)
    (horders : ∀ i : Fin 6, orders i ≤ K)
    (W : (Fin 6 → ℝ) → ℝ)
    (hWmeas : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hWbound : ∀ u, |W u| ≤ M) :
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren,
        ‖(W u : ℂ) * scaledTensorMixed chi label orders child u‖) ≤
      M * ((smoothChildren.card : ℝ) *
        ((2 * Real.log 2) * C) ^ 6) := by
  simp_rw [scaledTensorMixed_eq_logTensorMixed]
  simp_rw [weighted_children_norm_sum_eq]
  exact weighted_children_L1_le chi hchi hsmall hlarge
    K C hC orders horders W hWmeas M hM hWbound

end
end ImbalancedChen.P3HBWeightedOriginalChildrenL1
