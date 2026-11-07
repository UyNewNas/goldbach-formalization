import ImbalancedChen.Part3Gamma0ActualConstantMode
import ImbalancedChen.Part3CompactCuspParabolicL2

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual nonzero Fourier-radial compact cusp Poincare vector is orthogonal
to the actual nonzero quotient constant. Its L2 membership, strip L1,
measurability and true integer-translation periodicity all come from the
genuine compact-cusp supplier. The quotient mean is computed using actual
GammaInfinity\Gamma0 unfolding and the actual zero strip phase integral.
No hL2, hMean, spectral Fourier label, or assumed orthogonality is input.
The quotient constant's energy-domain/kernel membership remains OPEN.
-/

namespace ImbalancedChen.Part3.Gamma0CompactCuspConstantOrthogonality20261025a

noncomputable section
open Set MeasureTheory
open Gamma0QuotientCellPushforward20261025a GammaInfinityTranslationStrip20261025a
open Gamma0ActualParabolicUnfolding20261025a ActualInfinityKloostermanSeed20261025a
open Gamma0ActualConstantMode20261025a CompactCuspParabolicL220261025a

/-- Every genuine compact positive-height radial seed with nonzero integer
horizontal mode has zero ACTUAL quotient integral after parabolic summation. -/
theorem compactCuspPoincare_integral_zero (N : ℕ) [NeZero N]
    (m : ℤ) (hm : m≠0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ⊆Ioi (0:ℝ)) :
    (∫ q,parabolicComplexPoincare N (fourierRadialSeed m ψ) q ∂carrierPushforward N)=0 :=
  parabolic_fourier_mean_zero N m hm ψ (fourierRadialSeed_periodic m ψ)
    (fourierRadialSeed_measurable m ψ hψ) (fourierRadialSeed_integrableOn_strip m ψ hψ hc hpos)

/-- Actual L2 inner product with the canonical quotient constant, with
all finite-volume and compact-seed inputs supplied internally. -/
theorem constantL2_inner_compactCuspPoincareL2_zero (N : ℕ) [NeZero N]
    (m : ℤ) (hm : m≠0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ⊆Ioi (0:ℝ)) :
    inner ℂ (constantL2 N) (compactCuspPoincareL2 N m ψ hψ hc hpos)=0 := by
  rw [constantL2_inner]
  calc
    (∫ q,compactCuspPoincareL2 N m ψ hψ hc hpos q ∂carrierPushforward N)=
        ∫ q,parabolicComplexPoincare N (fourierRadialSeed m ψ) q ∂carrierPushforward N :=
      integral_congr_ae (compactCuspPoincare_memLp_two N m ψ hψ hc hpos).coeFn_toLp
    _ = 0 := compactCuspPoincare_integral_zero N m hm ψ hψ hc hpos

theorem compactCuspPoincareL2_inner_constantL2_zero (N : ℕ) [NeZero N]
    (m : ℤ) (hm : m≠0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ⊆Ioi (0:ℝ)) :
    inner ℂ (compactCuspPoincareL2 N m ψ hψ hc hpos) (constantL2 N)=0 := by
  simpa only [map_zero,inner_conj_symm] using
    congrArg star (constantL2_inner_compactCuspPoincareL2_zero N m hm ψ hψ hc hpos)

end
end ImbalancedChen.Part3.Gamma0CompactCuspConstantOrthogonality20261025a
