import ImbalancedChen.P5ZU1011SameRhoSignedDensityWallReserve
import ImbalancedChen.P5ZU1011AffineSmoothBoxCover

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The compiler mesh n stays fixed. A NEW geometric refinement m is selected
after epsilon from the proper original wall widths. Only then is smoothing
width delta selected for its finitely many coordinate faces. The latter
pays the actual finite atom multiplicity; no factor growing with m is
charged to the crossing-wall reserve. N is chosen last.
-/
namespace ImbalancedChen.P5Z.U1011SameRhoMeshFaceReserveSelection
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011CompactLogIntervalSmoothing
open U1011SameRhoSignedDensityWallReserve

abbrev FaceSlot (m : ℕ) := Fin 4 × Fin (m + 2)

def faceForms (m : ℕ) (k : Fin (Fintype.card (FaceSlot m))) : LogFour →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((Fintype.equivFin (FaceSlot m)).symm k).1

def faceBounds (m : ℕ) (k : Fin (Fintype.card (FaceSlot m))) : ℝ :=
  logPrimeMeshPoint (lower : ℝ) (upper : ℝ) m
    ((Fintype.equivFin (FaceSlot m)).symm k).2.val

theorem faceForms_ne_zero (m : ℕ) (k : Fin (Fintype.card (FaceSlot m))) : faceForms m k ≠ 0 := by
  intro hz
  have h := congrArg (fun L : LogFour →L[ℝ] ℝ => L (fun _ => 1)) hz
  simp only [faceForms, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply] at h
  norm_num at h

/-- Every smoothing face is an actual coordinate mesh hyperplane,
including lower and upper equality, not merely a continuous null set. -/
theorem faceReserve_subset_closed_faces {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (inner : Bool) (J : Finset (Grid m)) {v : LogFour}
    (hv : faceReserve inner δ J v) :
    v ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ := by
  obtain ⟨j, hj, i, hi⟩ := hv
  let a := logPrimeMeshLo (lower : ℝ) (upper : ℝ) m j i
  let b := logPrimeMeshHi (lower : ℝ) (upper : ℝ) m j i
  have habs : |v i - a| ≤ δ ∨ |v i - b| ≤ δ := by
    cases inner with
    | false =>
      change outerReserve δ a b (v i) at hi
      rcases hi with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · left
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · right
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    | true =>
      change innerReserve δ a b (v i) at hi
      rcases hi with ⟨hlo, hhi, hnear | hnear⟩
      · left
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · right
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases habs with hlo | hhi
  · let q : FaceSlot m := (i, ⟨(j i).val, by omega⟩)
    refine ⟨(Fintype.equivFin (FaceSlot m)) q, ?_⟩
    simpa only [faceForms, faceBounds, Equiv.symm_apply_apply, q,
      ContinuousLinearMap.proj_apply, a, logPrimeMeshLo] using hlo
  · let q : FaceSlot m := (i, ⟨(j i).val + 1, by omega⟩)
    refine ⟨(Fintype.equivFin (FaceSlot m)) q, ?_⟩
    simpa only [faceForms, faceBounds, Equiv.symm_apply_apply, q,
      ContinuousLinearMap.proj_apply, b, logPrimeMeshHi] using hhi

def wallScale {ι : Type*} [Fintype ι] (g : ι → MixedGate) : ℝ :=
  1 + ∑ i, ‖(g i).linear‖

theorem wallScale_pos {ι : Type*} [Fintype ι] (g : ι → MixedGate) : 0 < wallScale g := by
  have hs : 0 ≤ ∑ i, ‖(g i).linear‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  unfold wallScale
  linarith

/-- The same proper-row reduction handles original constant gates exactly. -/
theorem wallReserve_subset_reduced_strip {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (m : ℕ) {v : LogFour} (hv : wallReserve g m v) :
    v ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
      (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) := by
  obtain ⟨i, hi, hv⟩ := hv
  let q : ProperIndex g := ⟨i, hi⟩
  refine ⟨(Fintype.equivFin (ProperIndex g)) q, ?_⟩
  have hnorm : ‖(g i).linear‖ ≤ wallScale g := by
    have hs := Finset.single_le_sum (fun i _ => norm_nonneg (g i).linear) (Finset.mem_univ i)
    unfold wallScale
    linarith
  have hstep : 0 ≤ logPrimeMeshStep (lower : ℝ) (upper : ℝ) m :=
    (logPrimeMeshStep_pos (by norm_num [lower, upper]) m).le
  have hbound := hv.trans (mul_le_mul_of_nonneg_right hnorm hstep)
  simpa only [reducedForms, reducedBounds, Equiv.symm_apply_apply, q] using hbound

theorem boundary_mono_width {r n N : ℕ} (eta : ℚ) (E : ℕ × ℕ → Prop)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) {δ w : ℝ} (hδw : δ ≤ w) :
    boundary n N eta E L c δ ≤ boundary n N eta E L c w := by
  unfold boundary
  apply Finset.sum_le_sum
  intro t ht
  by_cases hsmall : coordinates N t ∈ primeAffineWallStrip L c δ
  · obtain ⟨i, hi⟩ := hsmall
    have hsmall' : coordinates N t ∈ primeAffineWallStrip L c δ := ⟨i, hi⟩
    have hbig : coordinates N t ∈ primeAffineWallStrip L c w := ⟨i, hi.trans hδw⟩
    simp only [if_pos hsmall', if_pos hbig, le_refl]
  · simp only [if_neg hsmall]
    split_ifs <;> positivity

/-- epsilon -> refinement m -> positive smoothing width delta -> N.
The face multiplicity is paid AFTER fixing m, while the proper affine
crossing contribution has unit cost. Both bounds use the ORIGINAL native
signed divisor main and retain all arithmetic equality faces. -/
theorem exists_mesh_and_face_density_reserves {ι : Type*} [Fintype ι]
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (g : ι → MixedGate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        ∀ E : ℕ × ℕ → Prop,
          boundary n N eta E (reducedForms g) (reducedBounds g)
            (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) < epsilon / 2 ∧
          ((Fintype.card (Grid m) : ℝ) + 1) *
            boundary n N eta E (faceForms m) (faceBounds m) δ < epsilon / 2 := by
  obtain ⟨w, hw, hwall⟩ := exists_mixed_circuit_density_wall_reserve n eta heta g
    (epsilon / 2) (half_pos hepsilon)
  have hscale := wallScale_pos g
  have hlim : Tendsto (fun m : ℕ => wallScale g *
      logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_logPrimeMeshStep (lower : ℝ) (upper : ℝ)).const_mul (wallScale g)
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hw)).exists
  let K : ℝ := (Fintype.card (Grid m) : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ, hδ, hface⟩ := exists_actual_native_density_wall_reserve n eta heta
    (faceForms m) (faceBounds m) (faceForms_ne_zero m)
    (epsilon / (2 * K)) (div_pos hepsilon (mul_pos (by norm_num) hK))
  refine ⟨m, δ, hδ, ?_⟩
  filter_upwards [hwall, hface] with N hwallN hfaceN
  intro E
  constructor
  · exact (boundary_mono_width eta E (reducedForms g) (reducedBounds g) hm.le).trans_lt (hwallN E)
  · have h := mul_lt_mul_of_pos_left (hfaceN E) hK
    have hc : K * (epsilon / (2 * K)) = epsilon / 2 := by field_simp [hK.ne']; ring
    rw [hc] at h
    exact h

end
end ImbalancedChen.P5Z.U1011SameRhoMeshFaceReserveSelection
