import ImbalancedChen.P2OriginalSaving16OwnedIntegral
import Mathlib.Tactic.NormNum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Display adapter for the 20261106 manuscript's G16 table entry. Reuse the
existing OwnedIntegral endpoint on its original region and density. The
finite certificate, ownership and arithmetic acceptance boundaries remain.
-/
namespace ImbalancedChen.P2OriginalSaving16DisplayBound

open MeasureTheory
open P2OriginalAscendingEighthCapDictionary (sourceDensity)
open P2OriginalSaving16FourteenPhysicalAtlas (region)

/-- Exact comparison with the already declared historical Q96 endpoint. -/
theorem displayed_bound_le_historical_endpoint :
    (1543640141 : ℝ) / (10 : ℝ) ^ 14 ≤
      (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 := by
  norm_num

/-- The manuscript's displayed bound on the same original source integral. -/
theorem displayed_bound_le_source_integral :
    (1543640141 : ℝ) / (10 : ℝ) ^ 14 ≤
      ∫ x in region, sourceDensity x :=
  displayed_bound_le_historical_endpoint.trans
    P2OriginalSaving16OwnedIntegral.historical_endpoint_le_source_integral

end ImbalancedChen.P2OriginalSaving16DisplayBound
