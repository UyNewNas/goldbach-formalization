import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.P3ActualU8DirectUnitPayment
import Mathlib.Tactic

/-!
P3.6 / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Connect the literal N-dependent physical attachment exported by
ActualUpperCountingInputs to the genuine U8 prime-triple signed PP
count. Unlike the preceding unrestricted raw-attachment statement,
the cutoff, Rosser level, small/rough split, actual modulus carrier,
and signed coefficient here are the source definitions
attachedUpperModuli / attachedUpperCoefficient.

The literal manuscript upper presieve exponent is rho_0 = 19/96,
strictly smaller than 1/5. The natural ceiling is paid EVENTUALLY
and before ANY retention policy or enumeration cap is chosen.
No identification with the FINAL causally compiled INTEGER rho_N
is claimed; no arbitrary-log PP saving or density bound is assumed.
The U8 q=1 quotient source is paid only by its direct count.
-/

namespace ImbalancedChen.P3ActualU8AttachedPhysical

noncomputable section
open Filter Topology
open scoped BigOperators

/-- The real strict presieve prime cutoff is ceil (N^(nu*r)).
The positive exponent gap, rather than a false pointwise rounding
identity, eventually pays the inclusive U8 N^(1/5) loss. -/
theorem eventually_attached_u8_cutoff
    {nu r : ℝ} (hnu : 0 ≤ nu) (hr : 0 ≤ r)
    (hgap : nu * r < (1 / 5 : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.ceil ((N : ℝ) ^ (nu * r)) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ) := by
  filter_upwards
    [eventually_floor_rpow_add_one_le_rpow (mul_nonneg hnu hr) hgap]
    with N hround
  calc
    ((Nat.ceil ((N : ℝ) ^ (nu * r)) : ℕ) : ℝ) ≤
        ((Nat.floor ((N : ℝ) ^ (nu * r)) : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one ((N : ℝ) ^ (nu * r))
    _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) := hround

/-- Literal physical U8 attachment, with one exact signed rho used in
the pointwise sieve majorant, density, coprime correction and original
rank-three PP error. One common N threshold precedes the ENTIRE choice
of finite retention policy and cap. Only the source-error count is
paid; the signed PP discrepancy is still shown as an unbounded term. -/
theorem eventually_u8_at_attached_upper
    {nu r epsilon : ℝ} (hnu : 0 < nu) (hr : 0 ≤ r)
    (hε : 0 < epsilon) (hεone : epsilon ≤ 1)
    (hεr : epsilon ^ 2 ≤ r)
    (hgap : nu * r < (1 / 5 : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
        (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) →
          let Q := attachedUpperModuli nu r epsilon retain cap N
          let rho := attachedUpperCoefficient nu r epsilon retain cap N
          currentChenUpsilon8 N ≤
            p5z_labelledMass (Finset.range N)
              (P5U8SharpKSource.productWeight N) *
                physicalDensitySum Q rho +
            p5z_labelledCoprimeCorrection (Finset.range N) id
              (P5U8SharpKSource.productWeight N) Q rho +
            Part3.primeProductSignedError 3 N N Q rho
              (P5U8SharpKSource.physicalWeight N) +
            δ * singularNormalization N := by
  filter_upwards
    [eventually_attached_u8_cutoff hnu.le hr hgap,
      P3ActualU8DirectUnitPayment.eventually_actual_u8_upper_via_prime_PP_no_unit_PP δ hδ,
      eventually_ge_atTop (2 : ℕ)]
    with N hcut hsource hN
  intro retain cap hcap
  exact hsource
    (Nat.ceil ((N : ℝ) ^ (nu * r)))
    (attachedUpperModuli nu r epsilon retain cap N)
    (attachedUpperCoefficient nu r epsilon retain cap N)
    hcut
    (attachedUpperCoefficient_majorant hnu hε hεone hεr
      retain cap hN hcap)

/-- Manuscript presieve wall rho_0=19/96 is STRICTLY below 1/5.
The coefficient is the actual N-dependent attachment, NOT YET the
final causally frozen integer coefficient rho_T. -/
theorem eventually_u8_at_manuscript_rho0
    (epsilon : ℝ) (hε : 0 < epsilon) (hεone : epsilon ≤ 1)
    (hεr : epsilon ^ 2 ≤ (19 / 96 : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ) →
          let Q := attachedUpperModuli 1 (19 / 96) epsilon retain cap N
          let rho := attachedUpperCoefficient 1 (19 / 96) epsilon retain cap N
          currentChenUpsilon8 N ≤
            p5z_labelledMass (Finset.range N)
              (P5U8SharpKSource.productWeight N) *
                physicalDensitySum Q rho +
            p5z_labelledCoprimeCorrection (Finset.range N) id
              (P5U8SharpKSource.productWeight N) Q rho +
            Part3.primeProductSignedError 3 N N Q rho
              (P5U8SharpKSource.physicalWeight N) +
            δ * singularNormalization N := by
  simpa only [one_mul] using
    (eventually_u8_at_attached_upper
      (nu := (1 : ℝ)) (r := (19 / 96 : ℝ)) (epsilon := epsilon)
      (by norm_num) (by norm_num) hε hεone hεr
      (by norm_num) δ hδ)

end

end ImbalancedChen.P3ActualU8AttachedPhysical
