import ImbalancedChen.P3U5SmoothSourceLedger
import ImbalancedChen.CurrentChenPairHarmonicMean

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Fixed smooth stage first, target threshold second. Existing target-deleted
prime-box convergence is invoked as an already available supplier; no new
PNT/Mertens or other external theorem is implemented. Four proper affine
walls are proved null. Their finite arithmetic equality labels are NOT
removed: they remain in wallBudget, whose actual harmonic mass is paid.

This is harmonic geometry payment, NOT an N/log^A discrepancy estimate,
not a uniform assertion for m=m(N), and not a causal-policy licence.
-/
namespace ImbalancedChen.P3U5SmoothWallMass
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
open P3U5RootAtlas P3U5SmoothRootPartition P3U5SmoothSourceLedger
open P3U5FullSourcePartition P2GammaSelectedPhysicalTheta
open Part5OriginalUpsilon5CausalDictionary (a h)
open P5OriginalU5CausalFinite (pairSupport coordinates)

def cube : Set Point := logPrimeBox (fun _ : Fin 2 => a) (fun _ => h)
def logDensity (x : Point) : ℝ := ∏ i : Fin 2,1/x i

def wallIntegral (m : ℕ) : ℝ := ∫ x in cube,wallBudget m x*logDensity x

def cubeWallMass (N m : ℕ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h) (wallBudget m)

def harmonicWallMass (N m : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N,wallBudget m (coordinates N t)/(Nat.totient (t.1*t.2) : ℝ)

private theorem logDensity_nonneg {x : Point} (hx : x ∈ cube) : 0 ≤ logDensity x := by
  apply Finset.prod_nonneg
  intro i hi
  exact one_div_nonneg.mpr ((show (0 : ℝ) ≤ a by norm_num [a]).trans
    (mem_logPrimeBox.mp hx i).1)

private theorem wall_integrable (m : ℕ) :
    IntegrableOn (fun x : Point => wallBudget m x*logDensity x) cube :=
  integrableOn_logPrimeBox_test_cube (by norm_num [a] : (0 : ℝ) < a)
    (wallBudget m) (wallBudget_contDiff m).continuous.continuousOn

/-- Nullity is supplied for these four actual nonzero forms, not assumed. -/
theorem ae_off_original_walls : ∀ᵐ x ∂volume,∀ j : Fin 4,margin j x ≠ 0 := by
  filter_upwards [ae_primeAffineGate_no_wall wallForm wallOffset wallForm_ne_zero] with x hx
  intro j
  exact sub_ne_zero.mpr (hx j).symm

/-- The physical log density stays on the original fixed positive cube. -/
theorem tendsto_wallIntegral : Tendsto wallIntegral atTop (𝓝 0) := by
  have hdom : IntegrableOn (fun x : Point => (4 : ℝ)*logDensity x) cube :=
    integrableOn_logPrimeBox_test_cube (by norm_num [a] : (0 : ℝ) < a)
      (fun _ : Point => (4 : ℝ)) continuousOn_const
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict cube) (fun x : Point => (4 : ℝ)*logDensity x)
    (fun m => (wall_integrable m).aestronglyMeasurable) hdom
    (fun m => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin 2 => a) (fun _ => h))] with x hx
      have hd := logDensity_nonneg hx
      have hb := wallBudget_range m x
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hb.2 hd)
    (show ∀ᵐ x ∂volume.restrict cube,
        Tendsto (fun m : ℕ => wallBudget m x*logDensity x) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [ae_restrict_of_ae ae_off_original_walls] with x hx
      simpa only [zero_mul] using (tendsto_wallBudget hx).mul_const (logDensity x))
  simpa only [wallIntegral,integral_zero] using h

/-- Same target exclusions and exact half-open box, using the existing input. -/
theorem tendsto_cubeWallMass (m : ℕ) :
    Tendsto (fun N : ℕ => cubeWallMass N m) atTop (𝓝 (wallIntegral m)) :=
  tendsto_actualPrimeBoxTestSum_cube (by norm_num [a]) (by norm_num [a,h])
    (wallBudget m) (wallBudget_contDiff m).continuous.continuousOn

/-- The original STRICT pair selector is compared with the complete box.
No extra ordinary/enhanced level or arithmetic filter is inserted. -/
theorem harmonicWallMass_le_cube {N : ℕ} (hN : 2 ≤ N) (m : ℕ) :
    harmonicWallMass N m ≤ cubeWallMass N m := by
  calc
    _ = actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h)
        ((primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
          (wallBudget m)) :=
      currentChenUpsilon5_harmonic_eq_actualPrimeBox hN (wallBudget m)
    _ ≤ _ := by
      unfold cubeWallMass actualPrimeBoxTestSum
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
      by_cases ho : actualPrimeTupleLog N p ∈
          primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)
      · simp only [Set.indicator_of_mem ho,le_refl]
      · rw [Set.indicator_of_notMem ho]
        exact (wallBudget_range m _).1

/-- The order is eps -> smooth stage -> N threshold. There is no uniform
N threshold over all growing stages, and no inverse-Theta normalization. -/
theorem exists_stage_cubeWallMass {eps : ℝ} (heps : 0 < eps) :
    ∃ m0 : ℕ,∀ m : ℕ,m0 ≤ m →
      ∀ᶠ N : ℕ in atTop,2 ≤ N ∧ cubeWallMass N m ≤ eps := by
  have hi : ∀ᶠ m : ℕ in atTop,wallIntegral m < eps/2 :=
    tendsto_wallIntegral.eventually (gt_mem_nhds (half_pos heps))
  obtain ⟨m0,hm0⟩ := eventually_atTop.mp hi
  refine ⟨m0,?_⟩
  intro m hm
  have hI : wallIntegral m < eps := lt_trans (hm0 m hm) (by linarith)
  filter_upwards [(tendsto_cubeWallMass m).eventually (gt_mem_nhds hI),
    eventually_ge_atTop (2 : ℕ)] with N hmass hN
  exact ⟨hN,hmass.le⟩

/-- Finite uniform domination for arbitrary bounded signed tests and keep.
Its denominator is the original reciprocal totient, not Theta or a count. -/
theorem harmonic_lane_error_bound (N m : ℕ) (keep : Pair → Prop) (l : Lane)
    (F : Pair → ℝ) {height : ℝ} (hh : 0 ≤ height)
    (hF : ∀ t ∈ kept N keep,|F t| ≤ height) :
    |(∑ t ∈ laneSupport N keep l,F t/(Nat.totient (t.1*t.2) : ℝ))-
      weightedTest N m keep l (fun t => F t/(Nat.totient (t.1*t.2) : ℝ))| ≤
        height*harmonicWallMass N m := by
  rw [sharp_eq_smooth_add_defect,add_sub_cancel_left]
  apply (laneDefect_bound N m keep l _).trans
  calc
    _ ≤ ∑ t ∈ kept N keep,
        height*(wallBudget m (coordinates N t)/(Nat.totient (t.1*t.2) : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
      have he := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hF t ht) (Nat.cast_nonneg _))
        (wallBudget_range m (coordinates N t)).1
      convert he using 1 <;> ring
    _ ≤ ∑ t ∈ pairSupport N,
        height*(wallBudget m (coordinates N t)/(Nat.totient (t.1*t.2) : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => mul_nonneg hh (div_nonneg (wallBudget_range m _).1 (Nat.cast_nonneg _)))
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- One chosen stage and one subsequent target threshold work for ALL four
lanes, all later keep filters, heights and height-bounded signed tests.
This is a positive harmonic domination argument, not a PP licence for keep. -/
theorem exists_common_four_lane_harmonic_approximation {eps : ℝ} (heps : 0 < eps) :
    ∃ m0 : ℕ,∀ m : ℕ,m0 ≤ m → ∀ᶠ N : ℕ in atTop,
      ∀ (keep : Pair → Prop) (height : ℝ),0 ≤ height → ∀ F : Pair → ℝ,
      (∀ t ∈ kept N keep,|F t| ≤ height) →
      (∑ l : Lane,
        |(∑ t ∈ laneSupport N keep l,F t/(Nat.totient (t.1*t.2) : ℝ))-
          weightedTest N m keep l (fun t => F t/(Nat.totient (t.1*t.2) : ℝ))|) ≤
            eps*height := by
  obtain ⟨m0,hm0⟩ := exists_stage_cubeWallMass (show 0 < eps/4 by positivity)
  refine ⟨m0,?_⟩
  intro m hm
  filter_upwards [hm0 m hm] with N hN
  intro keep height hh F hF
  have hmass : harmonicWallMass N m ≤ eps/4 :=
    (harmonicWallMass_le_cube hN.1 m).trans hN.2
  calc
    _ ≤ ∑ _l : Lane,height*(eps/4) := by
      apply Finset.sum_le_sum
      intro l hl
      exact (harmonic_lane_error_bound N m keep l F hh hF).trans
        (mul_le_mul_of_nonneg_left hmass hh)
    _ = eps*height := by rw [sum_lanes_eval]; ring

end
end ImbalancedChen.P3U5SmoothWallMass
