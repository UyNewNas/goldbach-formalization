import ImbalancedChen.Part3ActualMacdonaldPrintedHolomorphic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual printed-domain slice topology. For each fixed slit argument w,
R=|Im(w)|+|Re(w)|+1 is positive and R+w lies in the strict quarter-sector.
The slit plane is star-convex at this positive point by the pinned genuine
complex-convex theorem. Convexity of the shifted sum-quarter restriction
keeps the same segments inside the printed slice. Thus the actual slice
is path connected, with an explicit positive-real tail for subsequent
identity-theorem accumulation. No connectedness or continuation premise
is assumed for a Bessel transform.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldPrintedSliceTopology20261026b

noncomputable section
open Set
open ActualComplexMacdonaldQuarterL120261026b ActualComplexMacdonaldQuarterIdentity20261026b
open ActualMacdonaldPositiveProductSheet20261026b ActualMacdonaldPrintedHolomorphic20261026b

def printedSliceBase (w : ℂ) : ℝ := |w.im| + |w.re| + 1

theorem printedSliceBase_pos (w : ℂ) : 0 < printedSliceBase w := by
  unfold printedSliceBase
  positivity

/-- The entire positive-real tail beyond this explicit threshold belongs
to the actual printed slice, including when the fixed argument is in the
left half-plane. -/
theorem positive_real_tail_mem_printedSlice {w : ℂ} (hw : w ∈ Complex.slitPlane)
    {y : ℝ} (hy : |w.im| + |w.re| < y) : (y : ℂ) ∈ printedMacdonaldSlice w := by
  have hy0 : 0 < y := by linarith [abs_nonneg w.im, abs_nonneg w.re]
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl hy0), hw, ?_⟩
  change |((y : ℂ) + w).im| < ((y : ℂ) + w).re
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.add_re, Complex.ofReal_re]
  linarith [neg_le_abs w.re]

theorem printedSliceBase_mem {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    (printedSliceBase w : ℂ) ∈ printedMacdonaldSlice w :=
  positive_real_tail_mem_printedSlice hw (by unfold printedSliceBase; linarith)

/-- Intersecting the pinned positive-center slit star with the convex
shifted sum-quarter condition preserves the actual connecting segments. -/
theorem printedMacdonaldSlice_starConvex_at_positive {w : ℂ}
    (hw : w ∈ Complex.slitPlane) {R : ℝ} (hR : 0 < R)
    (hs : (R : ℂ) + w ∈ strictQuarterSector) :
    StarConvex ℝ (R : ℂ) (printedMacdonaldSlice w) := by
  intro z hz a b ha hb hab
  refine ⟨Complex.starConvex_ofReal_slitPlane hR hz.1 ha hb hab, hw, ?_⟩
  have hcoeff : a • w + b • w = w := by rw [← add_smul, hab, one_smul]
  have he : (a • (R : ℂ) + b • z) + w = a • ((R : ℂ) + w) + b • (z + w) := by
    rw [smul_add, smul_add]
    calc
      _ = (a • (R : ℂ) + b • z) + (a • w + b • w) := by rw [hcoeff]
      _ = _ := by abel
  change (a • (R : ℂ) + b • z) + w ∈ strictQuarterSector
  rw [he]
  exact strictQuarterSector_convex hs hz.2.2 ha hb hab

theorem printedMacdonaldSlice_starConvex {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    StarConvex ℝ (printedSliceBase w : ℂ) (printedMacdonaldSlice w) :=
  printedMacdonaldSlice_starConvex_at_positive hw (printedSliceBase_pos w) (printedSliceBase_mem hw).2.2

theorem printedMacdonaldSlice_isPathConnected {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IsPathConnected (printedMacdonaldSlice w) :=
  (printedMacdonaldSlice_starConvex hw).isPathConnected (printedSliceBase_mem hw)

theorem printedMacdonaldSlice_isPreconnected {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IsPreconnected (printedMacdonaldSlice w) :=
  (printedMacdonaldSlice_isPathConnected hw).isConnected.isPreconnected

theorem quarter_subset_printed_positive_slice {y : ℝ} (hy : 0 < y) :
    strictQuarterSector ⊆ printedMacdonaldSlice (y : ℂ) := by
  intro z hz
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (strictQuarterSector_re_pos hz)),
    Complex.mem_slitPlane_iff.mpr (Or.inl hy), ?_⟩
  change |(z + (y : ℂ)).im| < (z + (y : ℂ)).re
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.add_re, Complex.ofReal_re]
  have h : |z.im| < z.re := hz
  linarith

end
end ImbalancedChen.Part3.ActualMacdonaldPrintedSliceTopology20261026b
