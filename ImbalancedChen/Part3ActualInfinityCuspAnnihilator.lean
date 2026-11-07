import ImbalancedChen.Part3ActualPoincareSpectralCoefficient
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual closed subspace of the actual Gamma0 quotient L2 space: annihilate
all genuine compact positive-height incomplete Eisenstein seeds at infinity.
The seed vectors are the proved parabolic Poincare sums, not arbitrary
vectors assigned spectral labels. No completeness or scattering input.
This is the infinity condition; all other rational cusps remain separate.
-/
namespace ImbalancedChen.Part3.ActualInfinityCuspAnnihilator20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.ActualPoincareSpectralCoefficient20261026a

/-- Actual admissible zero-frequency height seeds. -/
structure HeightSeed where
  toFun : ℝ → ℂ
  continuous : Continuous toFun
  compact : HasCompactSupport toFun
  positive : tsupport toFun ⊆ Ioi (0 : ℝ)

abbrev QuotientL2 (N : ℕ) [NeZero N] := Lp ℂ 2 (carrierPushforward N)

def zeroSeedL2 (N : ℕ) [NeZero N] (s : HeightSeed) : QuotientL2 N :=
  compactCuspPoincareL2 N 0 s.toFun s.continuous s.compact s.positive

/-- Literal Hilbert annihilator of all actual incomplete Eisenstein vectors. -/
def infinityCuspSubspace (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  ⨅ s : HeightSeed, (ℂ ∙ zeroSeedL2 N s)ᗮ

theorem infinityCuspSubspace_closed (N : ℕ) [NeZero N] :
    IsClosed (infinityCuspSubspace N : Set (QuotientL2 N)) := by
  unfold infinityCuspSubspace
  rw [Submodule.iInf_orthogonal]
  exact Submodule.isClosed_orthogonal _

theorem mem_infinityCuspSubspace_iff (N : ℕ) [NeZero N] (V : QuotientL2 N) :
    V ∈ infinityCuspSubspace N ↔ ∀ s : HeightSeed, inner ℂ (zeroSeedL2 N s) V = 0 := by
  simp only [infinityCuspSubspace, Submodule.mem_iInf,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- For actual continuous quotient representatives, the annihilator is
exactly zero against every compact height test under the true unfolding.
The next module proves that this means AE vanishing of the actual mode. -/
theorem continuous_mem_iff_compact_height_tests (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N)) :
    hU2.toLp U ∈ infinityCuspSubspace N ↔ ∀ s : HeightSeed,
      (∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (s.toFun y) * actualTestFourier N U 0 y)) = 0 := by
  rw [mem_infinityCuspSubspace_iff]
  exact forall_congr' (fun s => by
    rw [zeroSeedL2, compactCuspPoincareL2,
      actual_poincare_L2_inner_eq_fourier N 0 s.toFun s.continuous s.compact s.positive U hU hU2])

end
end ImbalancedChen.Part3.ActualInfinityCuspAnnihilator20261026b
