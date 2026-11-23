import ImbalancedChen.P5ZU11ActualH248Ordinary
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
The max-two H248 state is a full affine half-space, including L < 2*w.
Its value is the actual adjacent minimum at serialized knot 50, rather
than the right open-cell value. This state is retained in the prime test
sum and integral. A positive denominator extension is used only outside
the chosen region, so positivity is required locally on that region.

This is a genuine prime harmonic test-function limit. It supplies neither
the original Rosser count comparison nor the signed AP estimate. The
arbitrary affine-sandwich region may preserve geometric priority cells;
no adaptive mask is assumed constant. SOURCE_ONLY / UNCOMPILED /
NOT_ROOT_ACCEPTED. No table feedback soundness is asserted.
-/

namespace ImbalancedChen.P5Z.U1011H248Clamp

open Set MeasureTheory Filter Topology
open Classical
open U11Integral U11Canonical U11H248
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

noncomputable section

/-- The actual knot reached by clamping an upper query to two. -/
def clampKnot : Fin 201 := ⟨50, by norm_num⟩

theorem floorGrid_fifty : floorGrid 50 = 2 := by
  norm_num [floorGrid]

/-- Closed-cell lookup uses both neighbors of knot 50. -/
theorem clampKnot_value (nums : Fin 200 → ℤ) :
    floorKnotValue nums clampKnot =
      min (floorValue nums 49) (floorValue nums 50) := by
  norm_num [floorKnotValue, clampKnot]

/-- Every serialized atom, including singleton knots, has its literal value. -/
theorem H248_eq_atom {s : ℝ} {b : FloorAtom} (hb : s ∈ upperAtomSet b) :
    H248 s = floorAtomValue H248Numerators b := by
  unfold H248 upperFloor
  calc
    _ = (upperAtomSet b).indicator (fun _ => floorAtomValue H248Numerators b) s := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        exact indicator_of_notMem (fun hc => hcb (upperAtom_unique hc hb)) _
      · intro h
        exact (h (Finset.mem_univ b)).elim
    _ = _ := indicator_of_mem hb _

/-- The scalar state reached by every query below two retains both neighbors. -/
theorem H248_max_two_of_le {s : ℝ} (hs : s ≤ 2) :
    H248 (max 2 s) = min (floorValue H248Numerators 49)
      (floorValue H248Numerators 50) := by
  have hb : (2 : ℝ) ∈ upperAtomSet (.inr clampKnot) := by
    change (2 : ℝ) ∈ Icc 1 5 ∩ {floorGrid 50}
    rw [floorGrid_fifty]
    norm_num
  rw [max_eq_left hs, H248_eq_atom hb]
  exact clampKnot_value H248Numerators

/-- Knot 50 pulls back to an entire half-space; it is not an equality seam. -/
theorem mem_ratio_clamp_rootAtom_iff (L w : ℝ) (hw : 0 < w) :
    max 2 (L / w) ∈ floorAtomSet (.inr clampKnot) ↔ L ≤ 2 * w := by
  change (max 2 (L / w) ∈ Icc (2 : ℝ) 5 ∧
    max 2 (L / w) = floorGrid 50) ↔ _
  rw [floorGrid_fifty]
  constructor
  · intro h
    have hq : L / w ≤ 2 := (le_max_right (2 : ℝ) (L / w)).trans_eq h.2
    exact (div_le_iff₀ hw).1 hq
  · intro h
    have hq : L / w ≤ 2 := (div_le_iff₀ hw).2 h
    rw [max_eq_left hq]
    norm_num

theorem H248_affine_clamp (L w : ℝ) (hw : 0 < w) (hL : L ≤ 2 * w) :
    H248 (max 2 (L / w)) = min (floorValue H248Numerators 49)
      (floorValue H248Numerators 50) :=
  H248_max_two_of_le ((div_le_iff₀ hw).2 hL)

/-- Both actual adjacent values occur in the coefficient of the clamp cost. -/
def clampCoefficient : ℝ :=
  4 * (1 - min (floorValue H248Numerators 49) (floorValue H248Numerators 50))

theorem clampCoefficient_nonneg : 0 ≤ clampCoefficient := by
  unfold clampCoefficient
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr ((min_le_left _ _).trans (H248_value_bounds 49).2))

theorem ordinary_eq_clamp (L : LogFour → ℝ) (v : LogFour)
    (hw : 0 < v 3) (hL : L v ≤ 2 * v 3) :
    ordinaryKernel H248 (fun _ => L) 0 v = clampCoefficient / L v := by
  unfold ordinaryKernel clampCoefficient
  rw [H248_affine_clamp (L v) (v 3) hw hL]

/-- A positive extension makes the cell formula continuous on the cube
without requiring the actual affine residual to be positive off the cell. -/
def extendedClampMinimum (ell : ℝ) (L : LogFour → ℝ) (v : LogFour) : ℝ :=
  min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
    (clampCoefficient / max ell (L v))

private theorem cube_subset_compactBox :
    Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)) ⊆
      compactBox := by
  intro v hv
  constructor
  · intro j
    exact (hv j (Set.mem_univ j)).1
  · intro j
    exact (hv j (Set.mem_univ j)).2

theorem continuousOn_extendedClampMinimum (ell : ℝ) (hell : 0 < ell)
    (L : LogFour → ℝ)
    (hL : ContinuousOn L
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)))) :
    ContinuousOn (extendedClampMinimum ell L)
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
  have hs := (continuousOn_canonical_switched_compactBox currentK).mono
    cube_subset_compactBox
  have ho : ContinuousOn (fun v => clampCoefficient / max ell (L v))
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
    exact continuousOn_const.div (continuousOn_const.max hL)
      (fun v _ => (hell.trans_le (le_max_left ell (L v))).ne')
  exact hs.min ho

theorem extended_eq_original (ell : ℝ) (L : LogFour → ℝ) (v : LogFour)
    (hw : 0 < v 3) (hlo : ell ≤ L v) (hhi : L v ≤ 2 * v 3) :
    extendedClampMinimum ell L v = min
      (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
      (ordinaryKernel H248 (fun _ => L) 0 v) := by
  rw [extendedClampMinimum, max_eq_right hlo, ordinary_eq_clamp L v hw hhi]

/-- Actual four-prime harmonic convergence on the full clamp cell.
All strict/weak gates are geometric. The same selected region occurs in
the arithmetic prime sum and harmonic integral; no whole mean, count
upper bound, convergence premise or constant adaptive-mask premise occurs. -/
theorem tendsto_actualPrimeBox_H248_clamp_minimum {r : ℕ}
    (ell : ℝ) (hell : 0 < ell) (L : LogFour → ℝ)
    (hL : ContinuousOn L
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))))
    (G : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hG : ∀ j, G j ≠ 0) (R : Set LogFour) (hR : MeasurableSet R)
    (hstrict : primeAffineGateRegion G c ⊆ R)
    (hweak : ∀ v ∈ R, ∀ j, G j v ≤ c j)
    (hcell : ∀ v ∈ R, 0 < v 3 ∧ ell ≤ L v ∧ L v ≤ 2 * v 3) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ : Fin 4 => (59 / 250 : ℝ))
      (R.indicator (fun v => min
        (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v)))) atTop
      (𝓝 (∫ v in logPrimeBox
          (fun _ : Fin 4 => (417 / 5000 : ℝ))
          (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
        min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
          (ordinaryKernel H248 (fun _ => L) 0 v) * ∏ j, 1 / v j)) := by
  have heq (v : LogFour) (hv : v ∈ R) :
      min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v) = extendedClampMinimum ell L v := by
    exact (extended_eq_original ell L v (hcell v hv).1
      (hcell v hv).2.1 (hcell v hv).2.2).symm
  have hf : R.indicator (fun v => min
        (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v)) =
      R.indicator (extendedClampMinimum ell L) := by
    funext v
    by_cases hv : v ∈ R
    · simp only [indicator_of_mem hv, heq v hv]
    · simp only [indicator_of_notMem hv]
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    G c hG R hR hstrict hweak (extendedClampMinimum ell L)
    (continuousOn_extendedClampMinimum ell hell L hL)
  have hint : (∫ v in logPrimeBox
      (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
        extendedClampMinimum ell L v * ∏ j, 1 / v j) =
      ∫ v in logPrimeBox
        (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
          min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
            (ordinaryKernel H248 (fun _ => L) 0 v) * ∏ j, 1 / v j := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter hR)
    intro v hv
    rw [heq v hv.2]
  rw [hf, ← hint]
  exact hlim

end

end ImbalancedChen.P5Z.U1011H248Clamp
