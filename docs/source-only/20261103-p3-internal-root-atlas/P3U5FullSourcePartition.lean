import ImbalancedChen.P3U5RootAtlas

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Exact finite partition of ALL original U5 labels, with an arbitrary keep
predicate retained. Four geometric lanes and the complete finite image
of original rootQ cover the kept source. The SAME rho, modulus carrier,
empty-mother lane, multiplicities and physical root are unchanged.
This is source coverage, not an estimate of the three nonplateau lanes.
-/
namespace ImbalancedChen.P3U5FullSourcePartition
noncomputable section
open scoped Classical BigOperators
open P3U5RootAtlas P2GammaU5PlateauGeometry
open P2GammaSelectedPhysicalTheta P2GammaRootFiberRelative
open P2OriginalU5SmallPartnerRootPayment
open P5OriginalU5CausalFinite (pairSupport coordinates)
open P2OriginalChildPhysicalNormalization (thetaAtom)

/-- Label-side owner, using precisely the old logarithmic coordinates. -/
def actualLane (N : ℕ) (t : Pair) : Lane := owner (coordinates N t 0) (coordinates N t 1)

def kept (N : ℕ) (keep : Pair → Prop) : Finset Pair := (pairSupport N).filter keep

def laneSupport (N : ℕ) (keep : Pair → Prop) (l : Lane) : Finset Pair :=
  (kept N keep).filter (fun t => actualLane N t = l)

theorem mem_laneSupport (N : ℕ) (keep : Pair → Prop) (l : Lane) (t : Pair) :
    t ∈ laneSupport N keep l ↔ t ∈ pairSupport N ∧ keep t ∧ actualLane N t = l := by
  simp only [laneSupport,kept,Finset.mem_filter]
  tauto

theorem laneSupport_subset (N : ℕ) (keep : Pair → Prop) (l : Lane) :
    laneSupport N keep l ⊆ pairSupport N :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem laneSupport_disjoint (N : ℕ) (keep : Pair → Prop) {l r : Lane} (h : l ≠ r) :
    Disjoint (laneSupport N keep l) (laneSupport N keep r) := by
  apply Finset.disjoint_left.mpr
  intro t ht hr
  exact h (((mem_laneSupport N keep l t).mp ht).2.2.symm.trans
    ((mem_laneSupport N keep r t).mp hr).2.2)

theorem rootQ_eq_owned {N : ℕ} (hN : 2 ≤ N) {t : Pair} (ht : t ∈ pairSupport N) :
    rootQ N t = (N : ℝ)^(laneLevel (actualLane N t) (coordinates N t 0) (coordinates N t 1)) := by
  have hx := P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht
  obtain ⟨hu,hut,hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hx
  unfold rootQ actualLane
  rw [original_level_eq_owned hu hut.le hh.le]

/-- Whole plateau identity; equality faces are included exactly once. -/
theorem actualLane_plateau_iff {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) : actualLane N t = Lane.plateau ↔ rootQ N t = plateauQ N := by
  constructor
  · intro ho
    rw [rootQ_eq_owned hN ht,ho]
    rfl
  · intro hq
    have hx := P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht
    obtain ⟨hu,hut,hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hx
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have he : Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1) =
        plateauLevel := by
      change (N : ℝ)^Part5OriginalUpsilon5CausalDictionary.level
        (coordinates N t 0) (coordinates N t 1) = (N : ℝ)^plateauLevel at hq
      exact le_antisymm ((Real.rpow_le_rpow_left_iff hNr).mp hq.le)
        ((Real.rpow_le_rpow_left_iff hNr).mp hq.symm.le)
    exact (owner_plateau_iff _ _).mpr
      ((original_level_eq_plateau_iff hu hut.le hh.le).mp he)

theorem plateau_lane_eq_rootFiber {N : ℕ} (hN : 2 ≤ N) (keep : Pair → Prop) :
    laneSupport N keep Lane.plateau = rootFiber N (plateauQ N) keep := by
  rw [rootFiber_eq_original_level_filter hN]
  ext t
  rw [mem_laneSupport]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ht,hk,ho⟩
    exact ⟨ht,hk,(actualLane_plateau_iff hN ht).mp ho⟩
  · rintro ⟨ht,hk,hq⟩
    exact ⟨ht,hk,(actualLane_plateau_iff hN ht).mpr hq⟩

/-- Exact coverage for arbitrary signed tests, not only positive masses. -/
theorem sum_lanes {α : Type*} [AddCommMonoid α] (N : ℕ)
    (keep : Pair → Prop) (F : Pair → α) :
    (∑ l : Lane,∑ t ∈ laneSupport N keep l,F t) = ∑ t ∈ kept N keep,F t := by
  simp only [laneSupport,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp

/-- Both count and exact coprime mean retain this identical rho. -/
theorem selectedGamma_lanes (N : ℕ) (keep : Pair → Prop) (moduli : Finset ℕ)
    (rho : ℕ → ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedGamma N moduli rho (laneSupport N keep l) sigma) =
      selectedGamma N moduli rho (kept N keep) sigma :=
  sum_lanes N keep _

theorem selectedEmpty_lanes (N : ℕ) (keep : Pair → Prop) (moduli : Finset ℕ)
    (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedEmpty N moduli rho T (laneSupport N keep l) sigma) =
      selectedEmpty N moduli rho T (kept N keep) sigma :=
  sum_lanes N keep _

theorem selectedResidual_lanes (N : ℕ) (keep : Pair → Prop) (moduli : Finset ℕ)
    (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedResidual N moduli rho T (laneSupport N keep l) sigma) =
      selectedResidual N moduli rho T (kept N keep) sigma := by
  simp only [selectedResidual,Finset.sum_sub_distrib,
    selectedGamma_lanes,selectedEmpty_lanes]

/-- All original pairs survive either keep or its explicit complement. -/
theorem keep_complement_test {α : Type*} [AddCommMonoid α]
    (N : ℕ) (keep : Pair → Prop) (F : Pair → α) :
    (∑ t ∈ kept N keep,F t) + (∑ t ∈ kept N (fun t => ¬keep t),F t) =
      ∑ t ∈ pairSupport N,F t :=
  Finset.sum_filter_add_sum_filter_not (pairSupport N) keep F

/-- There may be many levels. This is a finite image, not a fixed-size claim. -/
def rootValues (N : ℕ) (keep : Pair → Prop) : Finset ℝ := (kept N keep).image (rootQ N)

theorem rootFiber_eq_kept_filter {N : ℕ} (hN : 2 ≤ N)
    (keep : Pair → Prop) (Q : ℝ) :
    rootFiber N Q keep = (kept N keep).filter (fun t => rootQ N t = Q) := by
  rw [rootFiber_eq_original_level_filter hN]
  ext t
  simp only [kept,Finset.mem_filter]
  tauto

/-- Complete same-original-Q regrouping, with no source discarded. -/
theorem sum_rootFibers {α : Type*} [AddCommMonoid α] {N : ℕ} (hN : 2 ≤ N)
    (keep : Pair → Prop) (F : Pair → α) :
    (∑ Q ∈ rootValues N keep,∑ t ∈ rootFiber N Q keep,F t) =
      ∑ t ∈ kept N keep,F t := by
  simp_rw [rootFiber_eq_kept_filter hN]
  exact Finset.sum_fiberwise_of_maps_to (s := kept N keep) (t := rootValues N keep)
    (g := rootQ N) (fun t ht => Finset.mem_image_of_mem _ ht) F

theorem selectedResidual_rootFibers {N : ℕ} (hN : 2 ≤ N) (keep : Pair → Prop)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    (∑ Q ∈ rootValues N keep,selectedResidual N moduli rho T (rootFiber N Q keep) sigma) =
      selectedResidual N moduli rho T (kept N keep) sigma := by
  simp only [selectedResidual,selectedGamma,selectedEmpty,Finset.sum_sub_distrib]
  rw [sum_rootFibers hN keep,sum_rootFibers hN keep]

/-- A labelled sum of the ORIGINAL atoms at their own physical roots.
It is not asserted equal to a single common-Q Theta. -/
def movingTheta (N : ℕ) (keep : Pair → Prop) (sigma : Pair → ℝ) : ℝ :=
  ∑ t ∈ kept N keep,sigma t * thetaAtom N (rootQ N t) (t.1*t.2)

/-- Same-Q normalizers only combine by summing the actual root fibres. -/
theorem selectedTheta_rootFibers {N : ℕ} (hN : 2 ≤ N)
    (keep : Pair → Prop) (sigma : Pair → ℝ) :
    (∑ Q ∈ rootValues N keep,selectedTheta N Q (rootFiber N Q keep) sigma) =
      movingTheta N keep sigma := by
  simp_rw [selectedTheta_eq_atoms]
  calc
    _ = ∑ Q ∈ rootValues N keep,∑ t ∈ rootFiber N Q keep,
        sigma t * thetaAtom N (rootQ N t) (t.1*t.2) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      apply Finset.sum_congr rfl
      intro t ht
      rw [rootFiber_eq_kept_filter hN] at ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := sum_rootFibers hN keep _

/-- Full four-lane normalizer bookkeeping. No mass lower bound is needed. -/
theorem movingTheta_lanes (N : ℕ) (keep : Pair → Prop) (sigma : Pair → ℝ) :
    (∑ l : Lane,∑ t ∈ laneSupport N keep l,
      sigma t * thetaAtom N (rootQ N t) (t.1*t.2)) = movingTheta N keep sigma :=
  sum_lanes N keep _

end
end ImbalancedChen.P3U5FullSourcePartition
