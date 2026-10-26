import ImbalancedChen.P5ZU1011FourDimensionalSmoothBoxAtoms
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A finite separated four-dimensional smooth inner/outer cover of a literal
mixed strict/weak affine circuit. Its only losses are actual mesh-face
reserves and proper affine-wall strips of width norm(row)*meshStep.
Constant true/false rows are handled exactly. No arithmetic wall is erased.
-/
namespace ImbalancedChen.P5Z.U1011AffineSmoothBoxCover
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011FourDimensionalSmoothBoxAtoms

def innerCells {ι : Type*} (g : ι → MixedGate) (n : ℕ) : Finset (Grid n) :=
  Finset.univ.filter (fun j => ∀ v ∈ cell n j, v ∈ mixedRegion g)

def outerCells {ι : Type*} (g : ι → MixedGate) (n : ℕ) : Finset (Grid n) :=
  Finset.univ.filter (fun j => (cell n j ∩ mixedRegion g).Nonempty)

def regionIndicator {ι : Type*} (g : ι → MixedGate) (v : LogFour) : ℝ :=
  if v ∈ mixedRegion g then 1 else 0

def wallReserve {ι : Type*} (g : ι → MixedGate) (n : ℕ) (v : LogFour) : Prop :=
  ∃ i, (g i).linear ≠ 0 ∧ |(g i).linear v - (g i).offset| ≤
    ‖(g i).linear‖ * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n

theorem same_cell_norm_sub_le {n : ℕ} {j : Grid n} {v w : LogFour}
    (hv : v ∈ cell n j) (hw : w ∈ cell n j) :
    ‖v - w‖ ≤ logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
  have hstep := logPrimeMeshStep_pos (by norm_num [lower, upper] : (lower : ℝ) < (upper : ℝ)) n
  apply (pi_norm_le_iff_of_nonneg hstep.le).mpr
  intro i
  have hvi := mem_logPrimeMeshCell.mp hv i
  have hwi := mem_logPrimeMeshCell.mp hw i
  have hh := logPrimeMeshHi_eq_lo_add_step (lower : ℝ) (upper : ℝ) n j i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_cell_linear_oscillation {n : ℕ} {j : Grid n} {v w : LogFour}
    (hv : v ∈ cell n j) (hw : w ∈ cell n j) (L : LogFour →L[ℝ] ℝ) :
    |L v - L w| ≤ ‖L‖ * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
  have h := L.le_opNorm (v - w)
  rw [map_sub, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (same_cell_norm_sub_le hv hw) (norm_nonneg L))

/-- A crossed row is proper and its ACTUAL arithmetic points lie in a
quantified strip. Strict and weak endpoint conventions are both retained. -/
theorem crossing_gate_reserve {n : ℕ} {j : Grid n} {v x y : LogFour}
    (hv : v ∈ cell n j) (hx : x ∈ cell n j) (hy : y ∈ cell n j)
    (g : MixedGate) (hgx : g.Holds x) (hgy : ¬g.Holds y) :
    g.linear ≠ 0 ∧ |g.linear v - g.offset| ≤
      ‖g.linear‖ * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
  have hproper : g.linear ≠ 0 := by
    intro hz
    exact hgy ((zero_row_independent g hz x y).mp hgx)
  have hleft : g.linear x ≤ g.offset := by
    cases hs : g.strict
    · simpa [MixedGate.Holds, hs] using hgx
    · exact (by simpa [MixedGate.Holds, hs] using hgx : g.linear x < g.offset).le
  have hright : g.offset ≤ g.linear y := by
    cases hs : g.strict
    · exact le_of_lt (lt_of_not_ge (by simpa [MixedGate.Holds, hs] using hgy))
    · exact le_of_not_gt (by simpa [MixedGate.Holds, hs] using hgy)
  have hoscx := same_cell_linear_oscillation hv hx g.linear
  have hoscy := same_cell_linear_oscillation hv hy g.linear
  refine ⟨hproper, abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := (abs_le.mp hoscy).1
    linarith
  · have h := (abs_le.mp hoscx).2
    linarith

theorem innerCells_subset_outerCells {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {v : LogFour} (hv : v ∈ cube) :
    owner n v ∈ innerCells g n → owner n v ∈ outerCells g n := by
  intro hi
  have hinside := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, owner_mem n hv,
    hinside v (owner_mem n hv)⟩

/-- An outer cell which is not inner meets both sides of one ORIGINAL
row. Finite smooth-box refinement therefore charges an actual wall strip. -/
theorem outer_not_inner_wall {ι : Type*} (g : ι → MixedGate) {n : ℕ} {j : Grid n}
    (hout : j ∈ outerCells g n) (hnot : j ∉ innerCells g n)
    {v : LogFour} (hv : v ∈ cell n j) : wallReserve g n v := by
  obtain ⟨x, hx, hgx⟩ := (Finset.mem_filter.mp hout).2
  have hbad : ∃ y ∈ cell n j, y ∉ mixedRegion g := by
    by_contra h
    push_neg at h
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨y, hy, hgy⟩ := hbad
  have hi : ∃ i, ¬ (g i).Holds y := by
    by_contra h
    push_neg at h
    exact hgy h
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, crossing_gate_reserve hv hx hy (g i) (hgx i) hi⟩

theorem literal_inner_le_region_le_outer {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {v : LogFour} (hv : v ∈ cube) :
    literalCover (innerCells g n) v ≤ regionIndicator g v ∧
      regionIndicator g v ≤ literalCover (outerCells g n) v := by
  rw [literalCover_owned _ hv, literalCover_owned _ hv]
  by_cases hr : v ∈ mixedRegion g
  · have ho : owner n v ∈ outerCells g n :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, owner_mem n hv, hr⟩
    simp only [regionIndicator, if_pos hr, if_pos ho]
    constructor
    · split_ifs <;> norm_num
    · exact le_rfl
  · have hi : owner n v ∉ innerCells g n := by
      intro hi
      exact hr ((Finset.mem_filter.mp hi).2 v (owner_mem n hv))
    simp only [regionIndicator, if_neg hr, if_neg hi]
    constructor
    · exact le_rfl
    · split_ifs <;> norm_num

/-- Finite separated smooth box cover of the entire mixed circuit. -/
theorem smooth_inner_le_region_le_outer {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube) :
    smoothCover true δ (innerCells g n) v ≤ regionIndicator g v ∧
      regionIndicator g v ≤ smoothCover false δ (outerCells g n) v := by
  have h := literal_inner_le_region_le_outer g n hv
  exact ⟨(finite_cover_sandwich hδ _ v).1.trans h.1,
    h.2.trans (finite_cover_sandwich hδ _ v).2⟩

theorem literal_inner_error_wall {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {v : LogFour} (hv : v ∈ cube)
    (he : literalCover (innerCells g n) v - regionIndicator g v ≠ 0) : wallReserve g n v := by
  have hi : owner n v ∉ innerCells g n := by
    intro hi
    have hr : v ∈ mixedRegion g := (Finset.mem_filter.mp hi).2 v (owner_mem n hv)
    exact he (by simp [literalCover_owned _ hv, hi, regionIndicator, hr])
  have hr : v ∈ mixedRegion g := by
    by_contra hr
    exact he (by simp [literalCover_owned _ hv, hi, regionIndicator, hr])
  have ho : owner n v ∈ outerCells g n :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, owner_mem n hv, hr⟩
  exact outer_not_inner_wall g ho hi (owner_mem n hv)

theorem literal_outer_error_wall {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {v : LogFour} (hv : v ∈ cube)
    (he : literalCover (outerCells g n) v - regionIndicator g v ≠ 0) : wallReserve g n v := by
  have ho : owner n v ∈ outerCells g n := by
    by_contra ho
    have hr : v ∉ mixedRegion g := by
      intro hr
      exact ho (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, owner_mem n hv, hr⟩)
    exact he (by simp [literalCover_owned _ hv, ho, regionIndicator, hr])
  have hi : owner n v ∉ innerCells g n := by
    intro hi
    have hr : v ∈ mixedRegion g := (Finset.mem_filter.mp hi).2 v (owner_mem n hv)
    exact he (by simp [literalCover_owned _ hv, ho, regionIndicator, hr])
  exact outer_not_inner_wall g ho hi (owner_mem n hv)

/-- The analytic reserve selector receives a genuine pointwise support
statement: affine crossing strips OR the finite smooth coordinate faces. -/
theorem smooth_inner_error_supported {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube)
    (he : smoothCover true δ (innerCells g n) v - regionIndicator g v ≠ 0) :
    faceReserve true δ (innerCells g n) v ∨ wallReserve g n v := by
  by_cases hs : smoothCover true δ (innerCells g n) v - literalCover (innerCells g n) v ≠ 0
  · exact Or.inl (cover_error_supported hδ true _ v hs)
  · right
    apply literal_inner_error_wall g n hv
    have hsame := sub_eq_zero.mp (not_ne_iff.mp hs)
    rwa [← hsame]

theorem smooth_outer_error_supported {ι : Type*} (g : ι → MixedGate) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube)
    (he : smoothCover false δ (outerCells g n) v - regionIndicator g v ≠ 0) :
    faceReserve false δ (outerCells g n) v ∨ wallReserve g n v := by
  by_cases hs : smoothCover false δ (outerCells g n) v - literalCover (outerCells g n) v ≠ 0
  · exact Or.inl (cover_error_supported hδ false _ v hs)
  · right
    apply literal_outer_error_wall g n hv
    have hsame := sub_eq_zero.mp (not_ne_iff.mp hs)
    rwa [← hsame]

end
end ImbalancedChen.P5Z.U1011AffineSmoothBoxCover
