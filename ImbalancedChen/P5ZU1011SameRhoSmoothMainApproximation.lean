import ImbalancedChen.P5ZU1011SameRhoMeshFaceReserveSelection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual finite separated smooth covers approximate the ORIGINAL selected
native signed divisor MAIN. The compiler mesh stays fixed; epsilon then
the geometric refinement then the smoothing width precede N. Crossing
walls cost one, whereas finite smooth-face multiplicity is paid only after
the geometric refinement is fixed. Every arithmetic face remains in the
closed reserve. No AP, centre or strong-PP conclusion follows.
-/
namespace ImbalancedChen.P5Z.U1011SameRhoSmoothMainApproximation
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011SameRhoSignedDensityWallReserve U1011SameRhoMeshFaceReserveSelection

def chosenCells {ι : Type*} (inner : Bool) (g : ι → MixedGate) (m : ℕ) : Finset (Grid m) :=
  if inner then innerCells g m else outerCells g m

theorem cover_bounds {m : ℕ} (inner : Bool) (δ : ℝ) (J : Finset (Grid m)) (v : LogFour) :
    0 ≤ smoothCover inner δ J v ∧ smoothCover inner δ J v ≤ (Fintype.card (Grid m) : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (boxAtom_bounds inner δ m j v).1)
  · calc
      _ ≤ ∑ _j ∈ J, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (boxAtom_bounds inner δ m j v).2)
      _ = (J.card : ℝ) := by simp
      _ ≤ (Fintype.card (Grid m) : ℝ) := by exact_mod_cast Finset.card_le_univ J

/-- Separate crossing and face payments. The geometric crossing term has
unit cost, so refining the mesh does not amplify its boundary mass. -/
theorem smooth_error_pointwise {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (inner : Bool) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube) :
    |smoothCover inner δ (chosenCells inner g m) v - regionIndicator g v| ≤
      (if v ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
        (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) then 1 else 0) +
      ((Fintype.card (Grid m) : ℝ) + 1) *
        (if v ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ then 1 else 0) := by
  let J := chosenCells inner g m
  have hl : 0 ≤ literalCover J v ∧ literalCover J v ≤ 1 := by
    rw [literalCover_owned J hv]
    split_ifs <;> constructor <;> norm_num
  have hr : 0 ≤ regionIndicator g v ∧ regionIndicator g v ≤ 1 := by
    unfold regionIndicator
    split_ifs <;> constructor <;> norm_num
  obtain ⟨hs0, hs1⟩ := cover_bounds inner δ J v
  have hsabs : |smoothCover inner δ J v - literalCover J v| ≤
      (Fintype.card (Grid m) : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.cast_nonneg (Fintype.card (Grid m))]
  have hlabs : |literalCover J v - regionIndicator g v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hface : |smoothCover inner δ J v - literalCover J v| ≤
      ((Fintype.card (Grid m) : ℝ) + 1) *
        (if v ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ then 1 else 0) := by
    by_cases hf : v ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ
    · simpa only [if_pos hf, mul_one] using hsabs
    · have hz : smoothCover inner δ J v - literalCover J v = 0 := by
        by_contra hn
        exact hf (faceReserve_subset_closed_faces hδ inner J (cover_error_supported hδ inner J v hn))
      simp only [hz, abs_zero, if_neg hf, mul_zero, le_refl]
  have hwall : |literalCover J v - regionIndicator g v| ≤
      (if v ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
        (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) then 1 else 0) := by
    by_cases hw : v ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
        (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m)
    · simpa only [if_pos hw] using hlabs
    · have hz : literalCover J v - regionIndicator g v = 0 := by
        by_contra hn
        apply hw
        apply wallReserve_subset_reduced_strip g m
        cases inner with
        | false => exact literal_outer_error_wall g m hv hn
        | true => exact literal_inner_error_wall g m hv hn
      simp only [hz, abs_zero, if_neg hw, le_refl]
  exact (abs_sub_le _ (literalCover J v) _).trans
    ((add_le_add hface hwall).trans_eq (add_comm _ _))

/-- Original native Rosser main at one ACTUAL tuple, after its signed
divisor sum and with the complete physical denominator unchanged. -/
def nativeRowMain (n N : ℕ) (eta : ℚ) (t : Four) : ℝ :=
  (∑ d ∈ support n N eta t, coefficient n N eta t d *
    (1 / (Nat.totient (fullPrefix t * d) : ℝ))) * Real.log (N : ℝ) / singularSeries N

def smoothMainError {ι : Type*} (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    (g : ι → MixedGate) (inner : Bool) (m : ℕ) (δ : ℝ) : ℝ :=
  |∑ t ∈ ordinaryTuples n N E, nativeRowMain n N eta t *
    (smoothCover inner δ (chosenCells inner g m) (coordinates N t) -
      regionIndicator g (coordinates N t))|

theorem actual_native_smoothMainError_le {ι : Type*} [Fintype ι]
    (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (hN : 1 < N)
    (g : ι → MixedGate) (inner : Bool) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    smoothMainError n N eta E g inner m δ ≤
      boundary n N eta E (reducedForms g) (reducedBounds g)
        (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m) +
      ((Fintype.card (Grid m) : ℝ) + 1) *
        boundary n N eta E (faceForms m) (faceBounds m) δ := by
  unfold smoothMainError boundary
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  have hv : coordinates N t ∈ cube :=
    U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN (Finset.mem_filter.mp ht).1
  have herr := smooth_error_pointwise g inner m hδ hv
  have h := mul_le_mul_of_nonneg_left herr (abs_nonneg (nativeRowMain n N eta t))
  rw [abs_mul]
  change |nativeRowMain n N eta t| * _ ≤ _
  by_cases hw : coordinates N t ∈ primeAffineWallStrip (reducedForms g) (reducedBounds g)
      (wallScale g * logPrimeMeshStep (lower : ℝ) (upper : ℝ) m)
  <;> by_cases hf : coordinates N t ∈ primeAffineWallStrip (faceForms m) (faceBounds m) δ
  <;> simp only [hw, hf, if_true, if_false, mul_one, mul_zero, add_zero, zero_add] at h ⊢
  <;> dsimp only [nativeRowMain] at h ⊢
  <;> nlinarith

/-- The actual selected same-rho MAIN receives a finite separated smooth
test approximation for every prescribed tolerance, including both one-sided
cover choices. Mesh and width are fixed before N and every original E. -/
theorem exists_actual_native_smooth_main_approximation {ι : Type*} [Fintype ι]
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (g : ι → MixedGate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        ∀ E : ℕ × ℕ → Prop, ∀ inner : Bool,
          smoothMainError n N eta E g inner m δ < epsilon := by
  obtain ⟨m, δ, hδ, hpaid⟩ := exists_mesh_and_face_density_reserves n eta heta g epsilon hepsilon
  refine ⟨m, δ, hδ, ?_⟩
  filter_upwards [hpaid, (eventually_gt_atTop (1 : ℕ)).filter_mono inf_le_left] with N hN hlarge
  intro E inner
  have hb := actual_native_smoothMainError_le n N eta E hlarge g inner m hδ
  have hp := hN E
  linarith

end
end ImbalancedChen.P5Z.U1011SameRhoSmoothMainApproximation
