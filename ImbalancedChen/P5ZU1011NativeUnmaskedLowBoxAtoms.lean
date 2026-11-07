import ImbalancedChen.P5ZU1011NativeMaskPhysicalBoxAtoms
import ImbalancedChen.P5ZU1011OriginalSixteenU10FullHarmonic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The true U10 low band is treated on its OWN246-row policy/order circuit.
It is unmasked for every E, and is never placed in the U11 domain. Its
actual native coefficient has separated smooth physical box atoms at the
complete modulus (p0*p1*p2*p3)*d and the original frozen residual row.
-/
namespace ImbalancedChen.P5Z.U1011NativeUnmaskedLowBoxAtoms
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalSixteenJointNearCapCompiler U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy tupleTag ownerBox)
open U1011OriginalMaskSmoothBoxRealization (State circuitReserve circuit_error_supported)
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011NativeMaskPhysicalBoxAtoms (physicalTest physicalBoxAtom residualPhysicalCoefficient)

def lowGates (s : State) (m : ℕ) (k : Grid m) :
    U1011OriginalSixteenU10FullHarmonic.GateSlot10 ⊕ (Fin 4 × Bool) →
      U1011OriginalSixteenEligibilityState.MixedGate :=
  U1011SameRhoFixedCellPolyhedralIntegral.cutGates
    (U1011OriginalSixteenU10FullHarmonic.gates s) m k

def lowGeometry (s : State) (m : ℕ) (k : Grid m) : Set LogFour :=
  U1011OriginalSixteenU10FullHarmonic.piece s ∩ cell m k

theorem low_region (s : State) (m : ℕ) (k : Grid m) :
    mixedRegion (lowGates s m k) = lowGeometry s m k := by
  rw [lowGates, ← U1011SameRhoFixedCellPolyhedralIntegral.cut_eq_mixed,
    ← U1011OriginalSixteenU10FullHarmonic.piece_eq_mixed]
  rfl

def lowPieceTuples (s : State) (m N : ℕ) (k : Grid m) : Finset Four :=
  (P5U10OriginalMean.selector N).filter (fun t => coordinates N t ∈ lowGeometry s m k)

def lowPieceMarks (s : State) (m N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (k : Grid m) : Finset Mark :=
  (marks m N eta E).filter (fun a => coordinates N a.1 ∈ lowGeometry s m k)

private theorem low_source_to_ordinary {N : ℕ} (hN : 1 < N) (s : State) (m : ℕ)
    (E : ℕ × ℕ → Prop) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    {t : Four} (ht : t ∈ P5U10OriginalMean.selector N) (hg : coordinates N t ∈ lowGeometry s m k) :
    t ∈ ordinaryTuples m N E := by
  apply Finset.mem_filter.mpr
  refine ⟨U1011OriginalSixteenU10Geometry.selector_mem_joint hN ht E, ?_⟩
  simpa only [tupleTag, ownerBox, owner_eq_of_mem m hg.2] using hactive

private theorem low_ordinary_to_source {N : ℕ} (hN : 1 < N) (s : State) (m : ℕ)
    (E : ℕ × ℕ → Prop) (k : Grid m) {t : Four}
    (ht : t ∈ ordinaryTuples m N E) (hg : coordinates N t ∈ lowGeometry s m k) :
    t ∈ P5U10OriginalMean.selector N := by
  have hpbox := JointNearCapOwnerBinding.joint_slots_mem_box hN (Finset.mem_filter.mp ht).1
  have hp : slots t ∈ U1011OriginalSixteenU10Geometry.tuples10 N :=
    Finset.mem_filter.mpr ⟨hpbox, hg.1.1⟩
  have hs := (U1011OriginalSixteenU10Geometry.unslots_mem_selector_iff_tuples10 hN (slots t)).mpr hp
  simpa only [unslots_slots] using hs

theorem lowPieceMarks_eq_sigma {N : ℕ} (hN : 1 < N) (s : State) (m : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0) :
    lowPieceMarks s m N eta E k = (lowPieceTuples s m N k).sigma (activeRows m N eta) := by
  ext a
  rcases a with ⟨t, d⟩
  simp only [lowPieceMarks, marks, lowPieceTuples, Finset.mem_filter, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨ht, hd⟩, hg⟩
    exact ⟨⟨low_ordinary_to_source hN s m E k ht hg, hg⟩, hd⟩
  · rintro ⟨⟨ht, hg⟩, hd⟩
    exact ⟨⟨low_source_to_ordinary hN s m E k hactive ht hg, hd⟩, hg⟩

def lowCoefficientPiece (s : State) (m N : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) : ℝ :=
  ∑ t ∈ lowPieceTuples s m N k, ∑ d ∈ support m N eta t,
    if fullPrefix t * d = q then coefficient m N eta t d else 0

/-- The low coefficient is a restriction of the SAME joint sigma for
EVERY E. No outer paired mask can affect an unmasked low-band term. -/
theorem lowCoefficientPiece_eq_original_fibre {N : ℕ} (hN : 1 < N)
    (s : State) (m : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0) (q : ℕ) :
    lowCoefficientPiece s m N eta k q =
      ∑ a ∈ lowPieceMarks s m N eta E k, if modulus a = q then weight m N eta a else 0 := by
  rw [lowPieceMarks_eq_sigma hN s m eta E k hactive, Finset.sum_sigma]
  unfold lowCoefficientPiece
  apply Finset.sum_congr rfl
  intro t ht
  rw [activeRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : coefficient m N eta t d = 0 <;> simp [modulus, weight, hz]

private theorem lowPiece_sum_bijection {N : ℕ} (hN : 1 < N)
    (s : State) (m : ℕ) (k : Grid m) (F : Four → ℝ) :
    (∑ t ∈ lowPieceTuples s m N k, F t) =
      ∑ p ∈ (boxTuples N).filter (fun p => actualPrimeTupleLog N p ∈ lowGeometry s m k), F (unslots p) := by
  refine Finset.sum_bij (fun t _ => slots t) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht, hg⟩ := Finset.mem_filter.mp ht
    have hpbox := (Finset.mem_filter.mp
      ((U1011OriginalSixteenU10Geometry.unslots_mem_selector_iff_tuples10 hN (slots t)).mp
        (by simpa only [unslots_slots] using ht))).1
    exact Finset.mem_filter.mpr ⟨hpbox, hg⟩
  · intro t ht u hu heq
    exact slots_injective heq
  · intro p hp
    obtain ⟨hpbox, hg⟩ := Finset.mem_filter.mp hp
    have ht := (U1011OriginalSixteenU10Geometry.unslots_mem_selector_iff_tuples10 hN p).mpr
      (Finset.mem_filter.mpr ⟨hpbox, hg.1.1⟩)
    refine ⟨unslots p, Finset.mem_filter.mpr ⟨ht, ?_⟩, slots_unslots p⟩
    simpa only [coordinates, slots_unslots] using hg
  · intro t ht
    rw [unslots_slots]

theorem lowCoefficientPiece_eq_physicalTest {N : ℕ} (hN : 1 < N)
    (s : State) (m : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) :
    lowCoefficientPiece s m N eta k q =
      physicalTest m N eta k (regionIndicator (lowGates s m k)) q := by
  unfold lowCoefficientPiece
  rw [lowPiece_sum_bijection hN s m k, Finset.sum_filter]
  unfold physicalTest
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hg : actualPrimeTupleLog N p ∈ lowGeometry s m k
  · have hcell : coordinates N (unslots p) ∈ cell m k := by
      simpa only [coordinates, slots_unslots] using hg.2
    obtain ⟨hs, hc⟩ := compiled_static_on_cell m N eta hcell
    have hi : regionIndicator (lowGates s m k) (actualPrimeTupleLog N p) = 1 := by
      simp only [regionIndicator, low_region, if_pos hg]
    simp only [if_pos hg, hi, one_mul]
    unfold residualPhysicalCoefficient
    rw [hs]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hc d]
    simp only [fullPrefix, slots_unslots]
  · have hi : regionIndicator (lowGates s m k) (actualPrimeTupleLog N p) = 0 := by
      simp only [regionIndicator, low_region, if_neg hg]
    simp only [if_neg hg, hi, zero_mul]

def lowSmoothCover (inner : Bool) (s : State) (m : ℕ) (k : Grid m)
    (n : ℕ) (δ : ℝ) : LogFour → ℝ :=
  smoothCover inner δ (if inner then innerCells (lowGates s m k) n else outerCells (lowGates s m k) n)

theorem low_smooth_sandwich (s : State) (m : ℕ) (k : Grid m) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube) :
    lowSmoothCover true s m k n δ v ≤ regionIndicator (lowGates s m k) v ∧
      regionIndicator (lowGates s m k) v ≤ lowSmoothCover false s m k n δ v :=
  smooth_inner_le_region_le_outer (lowGates s m k) n hδ hv

theorem low_smooth_physical_atoms (inner : Bool) (s : State) (m N : ℕ)
    (eta : ℚ) (k : Grid m) (n : ℕ) (δ : ℝ) (q : ℕ) :
    physicalTest m N eta k (lowSmoothCover inner s m k n δ) q =
      ∑ j ∈ (if inner then innerCells (lowGates s m k) n else outerCells (lowGates s m k) n),
        physicalBoxAtom inner δ n j m N eta k q :=
  U1011NativeMaskPhysicalBoxAtoms.physicalTest_finite_cover inner δ _ m N eta k q

theorem low_native_error_identity {N : ℕ} (hN : 1 < N) (inner : Bool) (s : State)
    (m : ℕ) (eta : ℚ) (k : Grid m) (n : ℕ) (δ : ℝ) (q : ℕ) :
    physicalTest m N eta k (lowSmoothCover inner s m k n δ) q -
      lowCoefficientPiece s m N eta k q = physicalTest m N eta k
        (fun v => lowSmoothCover inner s m k n δ v - regionIndicator (lowGates s m k) v) q := by
  rw [lowCoefficientPiece_eq_physicalTest hN]
  unfold physicalTest
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem low_native_error_summand_supported {N : ℕ} (hN : 1 < N) (inner : Bool) (s : State)
    (m : ℕ) (eta : ℚ) (k : Grid m) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {p : Fin 4 → ℕ} (hp : p ∈ boxTuples N) (q : ℕ)
    (he : (lowSmoothCover inner s m k n δ (actualPrimeTupleLog N p) -
      regionIndicator (lowGates s m k) (actualPrimeTupleLog N p)) *
        residualPhysicalCoefficient m N eta k p q ≠ 0) :
    circuitReserve inner (lowGates s m k) n δ (actualPrimeTupleLog N p) := by
  have hv : actualPrimeTupleLog N p ∈ cube := by
    simpa only [boxTuples, cube, lower, upper] using
      ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  exact circuit_error_supported (lowGates s m k) inner n hδ hv (mul_ne_zero_iff.mp he).1

end
end ImbalancedChen.P5Z.U1011NativeUnmaskedLowBoxAtoms
