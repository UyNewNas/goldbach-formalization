import ImbalancedChen.P3U5SmoothRootPartition
import ImbalancedChen.P3U5FullSourcePartition

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The smooth weights act on the original labelled source. All counts and
coprime means keep ONE identical rho and modulus carrier. Exact signed
finite identities allow arbitrary keep/tests; this algebra does NOT license
arbitrary arithmetic filters as inputs to the manuscript smooth PP theorem.
-/
namespace ImbalancedChen.P3U5SmoothSourceLedger
noncomputable section
open scoped Classical BigOperators
open P3U5RootAtlas P3U5FullSourcePartition P3U5SmoothRootPartition
open P2GammaSelectedPhysicalTheta
open P2GammaRetainedSameRhoMother P2OriginalGammaUpperLowRankConsumer
open P5OriginalU5CausalFinite (pairSupport coordinates)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalU5SmallPartnerRootPayment (rootQ)

def weightedTest (N m : ℕ) (keep : Pair → Prop) (l : Lane) (F : Pair → ℝ) : ℝ :=
  ∑ t ∈ kept N keep,smoothWeight m l (coordinates N t)*F t

/-- Exact smooth partition at every finite target, including all walls. -/
theorem sum_weightedTest (N m : ℕ) (keep : Pair → Prop) (F : Pair → ℝ) :
    (∑ l : Lane,weightedTest N m keep l F) = ∑ t ∈ kept N keep,F t := by
  unfold weightedTest
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_mul,smoothWeight_sum,one_mul]

/-- No source is discarded by smoothing or by the separate keep filter. -/
theorem keep_complement_smooth (N m : ℕ) (keep : Pair → Prop) (F : Pair → ℝ) :
    (∑ l : Lane,weightedTest N m keep l F)+
      (∑ l : Lane,weightedTest N m (fun t => ¬keep t) l F) =
      ∑ t ∈ pairSupport N,F t := by
  rw [sum_weightedTest,sum_weightedTest]
  exact keep_complement_test N keep F

/-- The error is a literal signed sum with the original sharp owner.
This is the boundary term that must be paid, not a discarded null set. -/
def laneDefect (N m : ℕ) (keep : Pair → Prop) (l : Lane) (F : Pair → ℝ) : ℝ :=
  ∑ t ∈ kept N keep,
    ((if actualLane N t=l then (1 : ℝ) else 0)-smoothWeight m l (coordinates N t))*F t

theorem sharp_eq_smooth_add_defect (N m : ℕ) (keep : Pair → Prop)
    (l : Lane) (F : Pair → ℝ) :
    (∑ t ∈ laneSupport N keep l,F t) =
      weightedTest N m keep l F+laneDefect N m keep l F := by
  simp only [laneSupport,Finset.sum_filter,weightedTest,laneDefect]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hl : actualLane N t=l <;> simp only [hl,if_true,if_false] <;> ring

theorem laneDefect_bound (N m : ℕ) (keep : Pair → Prop) (l : Lane) (F : Pair → ℝ) :
    |laneDefect N m keep l F| ≤
      ∑ t ∈ kept N keep,|F t|*wallBudget m (coordinates N t) := by
  calc
    _ ≤ ∑ t ∈ kept N keep,
        |((if actualLane N t=l then (1 : ℝ) else 0)-smoothWeight m l (coordinates N t))*F t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (smooth_owner_error m l (coordinates N t))
        (abs_nonneg (F t))).trans_eq (mul_comm _ _)

/-- All equality-owner corrections cancel in the complete source.
A bound for a separate lane must still retain its absolute defect. -/
theorem sum_laneDefect_zero (N m : ℕ) (keep : Pair → Prop) (F : Pair → ℝ) :
    (∑ l : Lane,laneDefect N m keep l F) = 0 := by
  have h (l : Lane) : laneDefect N m keep l F =
      (∑ t ∈ laneSupport N keep l,F t)-weightedTest N m keep l F := by
    linarith [sharp_eq_smooth_add_defect N m keep l F]
  simp_rw [h]
  rw [Finset.sum_sub_distrib,sum_lanes,sum_weightedTest,sub_self]

/-- Explicit finite total scalar cost: the four weights have total mass
ONE, not four. This also holds for signed original label amplitudes. -/
theorem total_label_scalar_mass (N m : ℕ) (keep : Pair → Prop) (sigma : Pair → ℝ) :
    (∑ l : Lane,∑ t ∈ kept N keep,
      |smoothWeight m l (coordinates N t)*sigma t|) =
      ∑ t ∈ kept N keep,|sigma t| := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have h (l : Lane) : |smoothWeight m l (coordinates N t)*sigma t| =
      smoothWeight m l (coordinates N t)*|sigma t| := by
    rw [abs_mul,abs_of_nonneg (smoothWeight_range m l (coordinates N t)).1]
  simp_rw [h]
  rw [← Finset.sum_mul,smoothWeight_sum,one_mul]

def smoothSelector (N m : ℕ) (l : Lane) (sigma : Pair → ℝ) (t : Pair) : ℝ :=
  smoothWeight m l (coordinates N t)*sigma t

theorem selectedGamma_smooth_test (N m : ℕ) (keep : Pair → Prop) (l : Lane)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (sigma : Pair → ℝ) :
    selectedGamma N moduli rho (kept N keep) (smoothSelector N m l sigma) =
      weightedTest N m keep l (fun t => sigma t*∑ q ∈ moduli,rho q*gammaDiscrepancy N t q) := by
  apply Finset.sum_congr rfl
  intro t ht
  simp only [smoothSelector]
  ring

theorem selectedEmpty_smooth_test (N m : ℕ) (keep : Pair → Prop) (l : Lane)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    selectedEmpty N moduli rho T (kept N keep) (smoothSelector N m l sigma) =
      weightedTest N m keep l (fun t => sigma t*emptyPairError N t moduli rho T) := by
  apply Finset.sum_congr rfl
  intro t ht
  simp only [smoothSelector]
  ring

theorem selectedGamma_smooth_partition (N m : ℕ) (keep : Pair → Prop)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedGamma N moduli rho (kept N keep) (smoothSelector N m l sigma)) =
      selectedGamma N moduli rho (kept N keep) sigma := by
  simp_rw [selectedGamma_smooth_test]
  exact sum_weightedTest N m keep _

theorem selectedEmpty_smooth_partition (N m : ℕ) (keep : Pair → Prop)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedEmpty N moduli rho T (kept N keep) (smoothSelector N m l sigma)) =
      selectedEmpty N moduli rho T (kept N keep) sigma := by
  simp_rw [selectedEmpty_smooth_test]
  exact sum_weightedTest N m keep _

theorem selectedResidual_smooth_partition (N m : ℕ) (keep : Pair → Prop)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    (∑ l : Lane,selectedResidual N moduli rho T (kept N keep) (smoothSelector N m l sigma)) =
      selectedResidual N moduli rho T (kept N keep) sigma := by
  simp only [selectedResidual,Finset.sum_sub_distrib,
    selectedGamma_smooth_partition,selectedEmpty_smooth_partition]

/-- The actual root value stays in the test. No interpolation of rho,
physical Q, ceiling, or the original Theta atom is performed. -/
theorem movingTheta_smooth_partition (N m : ℕ) (keep : Pair → Prop) (sigma : Pair → ℝ) :
    (∑ l : Lane,movingTheta N keep (smoothSelector N m l sigma)) =
      movingTheta N keep sigma := by
  have h (l : Lane) : movingTheta N keep (smoothSelector N m l sigma) =
      weightedTest N m keep l
        (fun t => sigma t*thetaAtom N (rootQ N t) (t.1*t.2)) := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [smoothSelector]
    ring
  simp_rw [h]
  exact sum_weightedTest N m keep _

/-- Explicit same-rho sharp/smooth discrepancy difference. Its RHS is
NOT declared small by a harmonic-mass result: the arithmetic test can grow. -/
theorem selectedResidual_lane_defect (N m : ℕ) (keep : Pair → Prop) (l : Lane)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    selectedResidual N moduli rho T (laneSupport N keep l) sigma =
      selectedResidual N moduli rho T (kept N keep) (smoothSelector N m l sigma)+
      laneDefect N m keep l (fun t => sigma t*
        ((∑ q ∈ moduli,rho q*gammaDiscrepancy N t q)-emptyPairError N t moduli rho T)) := by
  have h := sharp_eq_smooth_add_defect N m keep l
    (fun t => sigma t*((∑ q ∈ moduli,rho q*gammaDiscrepancy N t q)-
      emptyPairError N t moduli rho T))
  simpa only [selectedResidual,selectedGamma,selectedEmpty,weightedTest,
    smoothSelector,mul_sub,Finset.sum_sub_distrib,mul_assoc] using h

end
end ImbalancedChen.P3U5SmoothSourceLedger
