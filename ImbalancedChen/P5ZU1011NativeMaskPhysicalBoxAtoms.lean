import ImbalancedChen.P5ZU1011OriginalMaskSmoothBoxRealization
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.P5ZU1011JointNearCapOwnerBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL selected-cell native coefficient, restricted to one actual
high-band policy state, is attached to separated smooth physical atoms.
The physical modulus is literally (p0*p1*p2*p3)*d. The native residual
coefficient is unchanged; tuple multiplicity and the signed removed-row
multiplicity are explicit. Approximation error is an exact coefficient on
the actual geometric reserve, not an arithmetic-null-set deletion.
-/
namespace ImbalancedChen.P5Z.U1011NativeMaskPhysicalBoxAtoms
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenNativeHarmonic
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenAffineState
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalMaskSmoothBoxRealization
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011OriginalPairedRowPrimeTests (nativeMask nativeMask_log_dictionary originalDomain_mask_iff)
open U1011OriginalPairedFixedMaskHarmonic (outerUnion)
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy tupleTag ownerBox)
open Certificates.PairedV2

def actualE (S : Finset Row) (N : ℕ) : ℕ × ℕ → Prop := nativeMask (outerUnion S) N

def pieceGeometry (S : Finset Row) (s : State) (m : ℕ) (k : Grid m) : Set LogFour :=
  originalCell (outerUnion S) s ∩ cell m k

def nativePieceTuples (S : Finset Row) (s : State) (m N : ℕ) (k : Grid m) : Finset Four :=
  (U11Adaptive.source N (actualE S N)).filter (fun t => coordinates N t ∈ pieceGeometry S s m k)

/-- The exact original physical marks are restricted geometrically;
neither a new coefficient nor a replacement tuple carrier is introduced. -/
def nativePieceMarks (S : Finset Row) (s : State) (m N : ℕ) (eta : ℚ) (k : Grid m) : Finset Mark :=
  (marks m N eta (actualE S N)).filter (fun a => coordinates N a.1 ∈ pieceGeometry S s m k)

private theorem piece_log_implies_kept (S : Finset Row) (s : State) (m N : ℕ) (k : Grid m)
    {p : Fin 4 → ℕ} (hp : actualPrimeTupleLog N p ∈ pieceGeometry S s m k) : kept N (actualE S N) p := by
  have hdomain := (originalDomain_mask_iff (outerUnion S) _).mp hp.1.1
  refine ⟨hdomain.1, ?_⟩
  exact fun he => hdomain.2 ((nativeMask_log_dictionary (outerUnion S) N p).mp he)

private theorem tuple_in_piece_ordinary {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    {t : Four} (ht : t ∈ U11Adaptive.source N (actualE S N))
    (hg : coordinates N t ∈ pieceGeometry S s m k) : t ∈ ordinaryTuples m N (actualE S N) := by
  apply Finset.mem_filter.mpr
  refine ⟨source_mem_joint hN ht, ?_⟩
  simpa only [tupleTag, ownerBox, owner_eq_of_mem m hg.2] using hactive

private theorem ordinary_in_piece_source {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (k : Grid m)
    {t : Four} (ht : t ∈ ordinaryTuples m N (actualE S N))
    (hg : coordinates N t ∈ pieceGeometry S s m k) : t ∈ U11Adaptive.source N (actualE S N) := by
  have hpbox := JointNearCapOwnerBinding.joint_slots_mem_box hN (Finset.mem_filter.mp ht).1
  have hkept := piece_log_implies_kept S s m N k hg
  have hs := (unslots_source_iff_kept_box hN (actualE S N) (slots t)).mpr
    (Finset.mem_filter.mpr ⟨hpbox, hkept⟩)
  simpa only [unslots_slots] using hs

theorem nativePieceMarks_eq_sigma {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (eta : ℚ) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0) :
    nativePieceMarks S s m N eta k = (nativePieceTuples S s m N k).sigma (activeRows m N eta) := by
  ext a
  rcases a with ⟨t, d⟩
  simp only [nativePieceMarks, marks, nativePieceTuples, Finset.mem_filter, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨ht, hd⟩, hg⟩
    exact ⟨⟨ordinary_in_piece_source hN S s m k ht hg, hg⟩, hd⟩
  · rintro ⟨⟨ht, hg⟩, hd⟩
    exact ⟨⟨tuple_in_piece_ordinary hN S s m k hactive ht hg, hd⟩, hg⟩

def nativeCoefficientPiece (S : Finset Row) (s : State) (m N : ℕ) (eta : ℚ)
    (k : Grid m) (q : ℕ) : ℝ :=
  ∑ t ∈ nativePieceTuples S s m N k, ∑ d ∈ support m N eta t,
    if fullPrefix t * d = q then coefficient m N eta t d else 0

/-- This coefficient is a literal restriction of the ORIGINAL sigma
fibre. Zero rows can be removed without changing any signed term. -/
theorem nativeCoefficientPiece_eq_original_fibre {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (eta : ℚ) (k : Grid m)
    (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0) (q : ℕ) :
    nativeCoefficientPiece S s m N eta k q =
      ∑ a ∈ nativePieceMarks S s m N eta k, if modulus a = q then weight m N eta a else 0 := by
  rw [nativePieceMarks_eq_sigma hN S s m eta k hactive, Finset.sum_sigma]
  unfold nativeCoefficientPiece
  apply Finset.sum_congr rfl
  intro t ht
  rw [activeRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : coefficient m N eta t d = 0 <;> simp [modulus, weight, hz]

private theorem nativePiece_sum_bijection {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (k : Grid m) (F : Four → ℝ) :
    (∑ t ∈ nativePieceTuples S s m N k, F t) =
      ∑ p ∈ (boxTuples N).filter (fun p => actualPrimeTupleLog N p ∈ pieceGeometry S s m k), F (unslots p) := by
  refine Finset.sum_bij (fun t _ => slots t) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht, hg⟩ := Finset.mem_filter.mp ht
    have hpbox := (Finset.mem_filter.mp
      ((unslots_source_iff_kept_box hN (actualE S N) (slots t)).mp
        (by simpa only [unslots_slots] using ht))).1
    exact Finset.mem_filter.mpr ⟨hpbox, hg⟩
  · intro t ht u hu heq
    exact slots_injective heq
  · intro p hp
    obtain ⟨hpbox, hg⟩ := Finset.mem_filter.mp hp
    have ht := (unslots_source_iff_kept_box hN (actualE S N) p).mpr
      (Finset.mem_filter.mpr ⟨hpbox, piece_log_implies_kept S s m N k hg⟩)
    refine ⟨unslots p, Finset.mem_filter.mpr ⟨ht, ?_⟩, slots_unslots p⟩
    simpa only [coordinates, slots_unslots] using hg
  · intro t ht
    rw [unslots_slots]

def residualPhysicalCoefficient (m N : ℕ) (eta : ℚ) (k : Grid m) (p : Fin 4 → ℕ) (q : ℕ) : ℝ :=
  ∑ d ∈ rowSupport (boxPolicy (gridBox m k)) (gridBox m k) eta N,
    if (∏ i : Fin 4, p i) * d = q then
      rowCoefficient (boxPolicy (gridBox m k)) (gridBox m k) eta N d else 0

def physicalTest (m N : ℕ) (eta : ℚ) (k : Grid m) (W : LogFour → ℝ) (q : ℕ) : ℝ :=
  ∑ p ∈ boxTuples N, W (actualPrimeTupleLog N p) * residualPhysicalCoefficient m N eta k p q

/-- Exact attachment to the independent FOUR-prime box carrier with
the SAME native residual coefficient and COMPLETE physical modulus. -/
theorem nativeCoefficientPiece_eq_physicalTest {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (s : State) (m : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) :
    nativeCoefficientPiece S s m N eta k q = physicalTest m N eta k
      (retainedIndicator S s m k) q := by
  unfold nativeCoefficientPiece
  rw [nativePiece_sum_bijection hN S s m k]
  rw [Finset.sum_filter]
  unfold physicalTest
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hg : actualPrimeTupleLog N p ∈ pieceGeometry S s m k
  · have hcell : coordinates N (unslots p) ∈ cell m k := by
      simpa only [coordinates, slots_unslots] using hg.2
    obtain ⟨hs, hc⟩ := compiled_static_on_cell m N eta hcell
    have hindicator : retainedIndicator S s m k (actualPrimeTupleLog N p) = 1 := if_pos hg
    simp only [if_pos hg, hindicator, one_mul]
    unfold residualPhysicalCoefficient
    rw [hs]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hc d]
    simp only [fullPrefix, slots_unslots]
  · have hindicator : retainedIndicator S s m k (actualPrimeTupleLog N p) = 0 := if_neg hg
    simp only [if_neg hg, hindicator, zero_mul]

def physicalBoxAtom (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n)
    (m N : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) : ℝ :=
  physicalTest m N eta k (boxAtom inner δ n j) q

/-- Every physical smooth atom is literally a four-prime separated
convolution term with its original residual row. No tuple predicate is
left inside the prime-box carrier. -/
theorem physicalBoxAtom_literal (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n)
    (m N : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) :
    physicalBoxAtom inner δ n j m N eta k q =
      ∑ p ∈ boxTuples N,
        (∏ i : Fin 4, U1011CompactLogIntervalSmoothing.weight inner δ
          (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
          (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i)
          (Real.log (p i : ℝ) / Real.log (N : ℝ))) *
        ∑ d ∈ rowSupport (boxPolicy (gridBox m k)) (gridBox m k) eta N,
          if (∏ i : Fin 4, p i) * d = q then
            rowCoefficient (boxPolicy (gridBox m k)) (gridBox m k) eta N d else 0 := rfl

theorem physicalTest_finite_cover (inner : Bool) (δ : ℝ) {n : ℕ} (J : Finset (Grid n))
    (m N : ℕ) (eta : ℚ) (k : Grid m) (q : ℕ) :
    physicalTest m N eta k (smoothCover inner δ J) q =
      ∑ j ∈ J, physicalBoxAtom inner δ n j m N eta k q := by
  simp only [physicalTest, smoothCover, physicalBoxAtom]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem physicalTest_sub_sum {ρ : Type*} (T : Finset ρ)
    (m N : ℕ) (eta : ℚ) (k : Grid m) (W : LogFour → ℝ) (V : ρ → LogFour → ℝ) (q : ℕ) :
    physicalTest m N eta k (fun v => W v - ∑ r ∈ T, V r v) q =
      physicalTest m N eta k W q - ∑ r ∈ T, physicalTest m N eta k (V r) q := by
  unfold physicalTest
  simp_rw [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-- Exact signed box-atom expansion. Removed-row multiplicity is
external and explicit; there is no hidden normalization factorial. -/
theorem signed_smooth_physical_atoms (lowerSide : Bool) (S : Finset Row) (s : State)
    (m N : ℕ) (eta : ℚ) (k : Grid m) (n : ℕ) (δ : ℝ) (q : ℕ) :
    physicalTest m N eta k (signedSmoothCover lowerSide S s m k n δ) q =
      (∑ j ∈ (if lowerSide then innerCells (baseGates s m k) n else outerCells (baseGates s m k) n),
        physicalBoxAtom lowerSide δ n j m N eta k q) -
      ∑ r ∈ S, ∑ j ∈ (if lowerSide then outerCells (removedGates s m k r) n
          else innerCells (removedGates s m k r) n),
        physicalBoxAtom (!lowerSide) δ n j m N eta k q := by
  change physicalTest m N eta k (fun v =>
    smoothCover lowerSide δ
      (if lowerSide then innerCells (baseGates s m k) n else outerCells (baseGates s m k) n) v -
    ∑ r ∈ S, smoothCover (!lowerSide) δ
      (if lowerSide then outerCells (removedGates s m k r) n
        else innerCells (removedGates s m k r) n) v) q = _
  rw [physicalTest_sub_sum, physicalTest_finite_cover]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact physicalTest_finite_cover (!lowerSide) δ _ m N eta k q

/-- The difference from the ACTUAL native coefficient is exactly a
physical coefficient on the error profile. Its full d-sum is retained. -/
theorem actual_native_error_identity {N : ℕ} (hN : 1 < N)
    (lowerSide : Bool) (S : Finset Row) (s : State) (m : ℕ) (eta : ℚ)
    (k : Grid m) (n : ℕ) (δ : ℝ) (q : ℕ) :
    physicalTest m N eta k (signedSmoothCover lowerSide S s m k n δ) q -
      nativeCoefficientPiece S s m N eta k q = physicalTest m N eta k
        (fun v => signedSmoothCover lowerSide S s m k n δ v - retainedIndicator S s m k v) q := by
  rw [nativeCoefficientPiece_eq_physicalTest hN]
  unfold physicalTest
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem actual_native_error_summand_supported {N : ℕ} (hN : 1 < N)
    (lowerSide : Bool) (S : Finset Row) (s : State) (m : ℕ) (eta : ℚ)
    (k : Grid m) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) {p : Fin 4 → ℕ}
    (hp : p ∈ boxTuples N) (q : ℕ)
    (he : (signedSmoothCover lowerSide S s m k n δ (actualPrimeTupleLog N p) -
      retainedIndicator S s m k (actualPrimeTupleLog N p)) *
        residualPhysicalCoefficient m N eta k p q ≠ 0) :
    originalReserve lowerSide S s m k n δ (actualPrimeTupleLog N p) := by
  have hv : actualPrimeTupleLog N p ∈ cube := by
    simpa only [boxTuples, cube, lower, upper] using
      ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  exact original_mask_error_supported lowerSide S s m k n hδ hv (mul_ne_zero_iff.mp he).1

end
end ImbalancedChen.P5Z.U1011NativeMaskPhysicalBoxAtoms
