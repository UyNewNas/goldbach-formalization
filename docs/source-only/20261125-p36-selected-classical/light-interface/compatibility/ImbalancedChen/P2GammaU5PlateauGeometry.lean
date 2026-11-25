import ImbalancedChen.P2OriginalU5PlateauRectangle
import ImbalancedChen.P2GammaRootFiberRelative
import ImbalancedChen.ActualPrimeBoxMass

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A real positive-area constant-level piece of the ORIGINAL U5 selector.
The root is not rounded or replaced: on the displayed separated box its
max formula equals its own constant B(a) branch. All target exclusions,
strict pair order and half-open endpoints remain in the actual carrier.
This is one genuine root fibre, not coverage of every causal history.
-/
namespace ImbalancedChen.P2GammaU5PlateauGeometry
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaSelectedPhysicalTheta P2GammaRootFiberRelative
open P2OriginalU5SmallPartnerRootPayment
open P5OriginalU5CausalFinite (pairSupport coordinates)

/-- Original constant branch, NOT the global cap 153/256. -/
def plateauFiber (N : ℕ) : Finset Pair :=
  rootFiber N (plateauQ N) (fun _ => True)



/-- Closed box geometry is stronger than the half-open arithmetic box.
Both nonconstant branches are strictly below the original constant. -/


/-- All original U5 pairs already satisfy the upper residual-domain test;
this is not restricted to the new plateau rectangle. -/
theorem root_residual_le_target {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) : rootQ N t/((t.1*t.2 : ℕ) : ℝ) ≤ N := by
  have hd : (1 : ℝ) ≤ ((t.1*t.2 : ℕ) : ℝ) := by
    exact_mod_cast pair_product_pos ht
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hroot : rootQ N t ≤ (N : ℝ) :=
    (root_level_cap (show 1 ≤ N by omega) t).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num : (153/256 : ℝ) ≤ 1))
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ))).mpr
  exact hroot.trans (by nlinarith [Nat.cast_nonneg N])

/-- The two residual tests do not discard any original pair whose root
level equals Q. This does not make distinct root levels identical. -/
theorem rootFiber_eq_original_level_filter {N : ℕ} (hN : 2 ≤ N)
    (Qphys : ℝ) (keep : Pair → Prop) :
    rootFiber N Qphys keep =
      (pairSupport N).filter (fun t => keep t ∧ rootQ N t = Qphys) := by
  ext t
  simp only [rootFiber,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hkeep,heq,_⟩
    exact ⟨ht,hkeep,heq⟩
  · rintro ⟨ht,hkeep,heq⟩
    refine ⟨ht,hkeep,heq,?_,?_⟩
    · simpa only [← heq] using root_residual_gt_one hN ht
    · simpa only [← heq] using root_residual_le_target hN ht

theorem rectangle_subset_plateauFiber {N : ℕ} (hN : 2 ≤ N) :
    rectangle N ⊆ plateauFiber N := by
  intro t ht
  have hp := rectangle_subset_pairSupport hN ht
  rw [plateauFiber,rootFiber_eq_original_level_filter hN]
  exact Finset.mem_filter.mpr ⟨hp,True.intro,rectangle_rootQ hN ht⟩

end
end ImbalancedChen.P2GammaU5PlateauGeometry
