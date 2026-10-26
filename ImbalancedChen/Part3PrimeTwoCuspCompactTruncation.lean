import ImbalancedChen.Part3PrimeTwoCuspCompactCover
import Mathlib.Topology.Algebra.ConstMulAction

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual open orbit projection and the actual Fricke homeomorphism imply
openness of both literal cusp tails. Their closed complement is compact,
using the separately derived full finite-coset cover at pY. -/

noncomputable section
open Set Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b

namespace ImbalancedChen.Part3.PrimeTwoCuspCompactTruncation20261026b

/-- The group-action quotient map is open in its genuine quotient topology. -/
theorem orbitProjection_isOpenMap (N : ℕ) : IsOpenMap (orbitProjection N) :=
  isOpenMap_quotient_mk'_mul

theorem infinityHighNeighborhood_isOpen (N : ℕ) (Y : ℝ) :
    IsOpen (infinityHighNeighborhood N Y) := by
  apply orbitProjection_isOpenMap N
  exact isOpen_lt continuous_const UpperHalfPlane.continuous_im

/-- Both maps here are the actual spatial actions, so no continuity or
open-embedding property of a separately postulated cusp chart is input. -/
theorem zeroHighNeighborhood_isOpen (p : ℕ) (hp : p.Prime) (Y : ℝ) :
    IsOpen (zeroHighNeighborhood p hp Y) := by
  have hW : IsOpenMap (fun z : UpperHalfPlane => frickeSL p hp.pos • z) :=
    isOpenMap_smul _
  exact ((orbitProjection_isOpenMap p).comp hW) _
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im)

theorem twoCuspTruncation_isClosed (p : ℕ) (hp : p.Prime) (Y : ℝ) :
    IsClosed (twoCuspTruncation p hp Y) :=
  ((infinityHighNeighborhood_isOpen p Y).union
    (zeroHighNeighborhood_isOpen p hp Y)).isClosed_compl

/-- Globally compact complement of the two normalized STRICT tails,
including both horizontal boundary levels and every quotient boundary
orbit, already at Y=1. -/
theorem twoCuspTruncation_isCompact (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) : IsCompact (twoCuspTruncation p hp Y) :=
  (quotientTruncatedCarrier_isCompact p ((p : ℝ) * Y)).of_isClosed_subset
    (twoCuspTruncation_isClosed p hp Y)
    (twoCuspTruncation_subset_compact_carrier p hp Y hY)

end ImbalancedChen.Part3.PrimeTwoCuspCompactTruncation20261026b
