import ImbalancedChen.P5OldFifthActualChildJensenIntegral
import ImbalancedChen.P1OriginalFifthLiteralKernelModulus
import ImbalancedChen.P1FifthPositivePartActualOwner

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The whole-child unbuffered Jensen lower bound is restricted to the UNION
of original selected owner cells, not to a hypothetical full retained box.
The actual omitted set and the genuine signed-kernel buffer modulus are
charged separately. No coefficientwise Mobius monotonicity is asserted.
-/
namespace ImbalancedChen.P5ChildSelectedOwnerJensenReserve
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthGrid400UnitBoxPartition
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalVariableFifthContinuation
open P2OriginalFourthCapProducerInterface
open P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower
open P1FifthPositivePartActualOwner
open P1LiteralVariableFifthCompactSupplier
open P1OriginalFifthLiteralKernelModulus
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateBarycentric
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ
open P5OldFifthActualChildJensenIntegral

abbrev Point := Fin 5 → ℝ
abbrev Owner (m : ℕ) := Fin 5 → Fin (m + 1)

def selectedOwnerUnion (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Owner m)) : Set Point :=
  ⋃ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
    P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j

def retainedChild (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) : Set Point :=
  childBox raw c ∩ selectedOwnerUnion e chi m omega J5

def omittedChild (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) : Set Point :=
  childBox raw c \ retainedChild raw c e chi m omega J5

theorem selectedOwnerUnion_measurable (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) :
    MeasurableSet (selectedOwnerUnion e chi m omega J5) := by
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ =>
    P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j))

theorem retainedChild_measurable (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    MeasurableSet (retainedChild raw c e chi m omega J5) :=
  (childBox_measurable raw c).inter (selectedOwnerUnion_measurable e chi m omega J5)

theorem omittedChild_measurable (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    MeasurableSet (omittedChild raw c e chi m omega J5) :=
  (childBox_measurable raw c).diff (retainedChild_measurable raw c e chi m omega J5)

theorem retainedChild_eq_owner_union (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    retainedChild raw c e chi m omega J5 =
      ⋃ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        childOwnerDomain raw c e chi m omega j := by
  ext t
  simp only [retainedChild, selectedOwnerUnion, childOwnerDomain,
    mem_inter_iff, mem_iUnion]
  aesop

theorem childSubset_volume_lt_top (raw : FifthWireRow) (c : ChildIndex)
    {s : Set Point} (hs : s ⊆ childBox raw c) : volume s < ∞ :=
  (measure_mono (hs.trans (childBox_subset_closed raw c))).trans_lt
    isCompact_Icc.measure_lt_top

/-- Actual integer key bounds put the entire archived child in the SAME
positive compact cube used by the literal signed-kernel modulus. -/
theorem childBox_subset_kernelCompact (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) : childBox raw c ⊆ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := by
  intro t ht i _
  have hp := child_subset_parent raw hgrid c ht
  have hlo : (raw.lo i : ℝ) / 400 ≤ t i := by
    simpa only [FifthWireRow.lower, hgrid] using (hp i).1
  have hk : (1 : ℝ) ≤ (raw.lo i : ℝ) := by exact_mod_cast hpositive i
  exact ⟨by linarith, ((hp i).2.le).trans (hupper i)⟩

theorem positiveKey_childLeft_pos (raw : FifthWireRow)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (c : ChildIndex) (i : Fin 5) :
    0 < childLeft raw c i := by
  have hk : (1 : ℝ) ≤ (raw.lo i : ℝ) := by exact_mod_cast hpositive i
  have hw : 0 ≤ (width i : ℝ) * ((c i).val : ℝ) := by positivity
  simp only [childLeft, childLeftNumer]
  push_cast
  linarith

/-- A negative actual vertex sum uses the original zero fallback. Signed d
is preserved; no all-child nonnegativity premise is added. -/
def certifiedChildJensen (picks : ParentPicks) (raw : FifthWireRow)
    (c : ChildIndex) (b : ℝ) (d : ℤ) : ℝ :=
  if 0 ≤ d then childVolume raw c * childPrefactor raw c *
    Q b ((d : ℝ) / (1024 * 1600 * childRight raw c 4)) else 0

theorem certifiedChildJensen_le_whole
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd : (d : ℝ) = vertexD picks raw c) :
    certifiedChildJensen picks raw c b d ≤
      ∫ t in childBox raw c, frozenUpperPositiveKernel picks raw t := by
  by_cases hd0 : 0 ≤ d
  · rw [certifiedChildJensen, if_pos hd0]
    exact integral_frozenUpperPositiveKernel_ge_child_Jensen picks raw c hleft
      hb2 hb4 hnew d hd0 hd
  · rw [certifiedChildJensen, if_neg hd0]
    exact integral_nonneg (fun t => frozenUpperPositiveKernel_nonneg picks raw t)

/-- The first term is actual omitted volume; the second is actual retained
volume times the uniform modulus of the SAME positive signed raw kernel.
Neither term assumes a target density reserve has already been met. -/
def childOwnerReserve (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) : ℝ :=
  rowMassBound raw * volume.real (omittedChild raw c e chi m omega J5) +
    rowModulus raw (e : ℝ) * volume.real (retainedChild raw c e chi m omega J5)

theorem childOwnerReserve_nonneg (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    0 ≤ childOwnerReserve raw c e chi m omega J5 := by
  unfold childOwnerReserve
  exact add_nonneg
    (mul_nonneg (by linarith [one_le_rowMassBound raw]) ENNReal.toReal_nonneg)
    (mul_nonneg (rowModulus_nonneg raw e) ENNReal.toReal_nonneg)

/-- The unbuffered frozen surrogate is controlled on the WHOLE child.
This bound uses the actual literal positive kernel, not |signed mean|. -/
theorem frozenKernel_le_rowMassBound
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) {t : Point} (ht : t ∈ childBox raw c) :
    frozenUpperPositiveKernel picks raw t ≤ rowMassBound raw := by
  have hc := childBox_subset_kernelCompact raw hgrid hpositive hupper c ht
  have hp : ∀ i : Fin 5, 0 < t i := fun i =>
    (by norm_num : (0 : ℝ) < 1 / 400).trans_le (hc i (mem_univ _)).1
  exact (frozenUpperPositiveKernel_le_literalPositiveRawKernel picks raw t hp).trans
    (positive_kernel_le_rowMassBound raw 0 (by norm_num) t hc)

/-- Buffering uses a norm difference of genuine kernels, not an invalid
coefficientwise monotonicity assertion for finite signed Rosser weights. -/
theorem frozenKernel_le_buffered_positive_add_modulus
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) (e : ℚ) {t : Point} (ht : t ∈ childBox raw c) :
    frozenUpperPositiveKernel picks raw t ≤
      literalPositiveRawKernel (e : ℝ) raw t + rowModulus raw (e : ℝ) := by
  have hc := childBox_subset_kernelCompact raw hgrid hpositive hupper c ht
  have hp : ∀ i : Fin 5, 0 < t i := fun i =>
    (by norm_num : (0 : ℝ) < 1 / 400).trans_le (hc i (mem_univ _)).1
  have hsur := frozenUpperPositiveKernel_le_literalPositiveRawKernel picks raw t hp
  have hdiff := (abs_le.mp (positive_kernel_difference_le_rowModulus raw e t hc)).1
  change -rowModulus raw e ≤ literalPositiveRawKernel e raw t -
    literalPositiveRawKernel 0 raw t at hdiff
  linarith

/-- Exact clipping and signed-source buffer reserve for the actual retained
union. The omitted set can include whole open regions: its mass is charged
explicitly and is never assumed zero just because it is outside a label. -/
theorem whole_child_sub_reserve_le_retained_positive
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Owner m)) :
    (∫ t in childBox raw c, frozenUpperPositiveKernel picks raw t) -
        childOwnerReserve raw c e chi m omega J5 ≤
      ∫ t in retainedChild raw c e chi m omega J5, literalPositiveRawKernel e raw t := by
  let S := retainedChild raw c e chi m omega J5
  let D := omittedChild raw c e chi m omega J5
  have hS : MeasurableSet S := retainedChild_measurable raw c e chi m omega J5
  have hsub : S ⊆ childBox raw c := inter_subset_left
  have hDsub : D ⊆ childBox raw c := sdiff_subset
  have hK := integrableOn_frozenUpperPositiveKernel_child picks raw c
    (positiveKey_childLeft_pos raw hpositive c)
  have hPcompact := (continuousOn_literalPositiveRawKernel e (1 / 400) (19 / 96)
    (by norm_num) raw).integrableOn_compact
      (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))
  have hP : IntegrableOn (literalPositiveRawKernel e raw) S :=
    hPcompact.mono_set (hsub.trans (childBox_subset_kernelCompact raw hgrid hpositive hupper c))
  have hconst : IntegrableOn (fun _ : Point => rowModulus raw e) S :=
    integrableOn_const (childSubset_volume_lt_top raw c hsub).ne
  have hbuf : (∫ t in S, frozenUpperPositiveKernel picks raw t) ≤
      (∫ t in S, literalPositiveRawKernel e raw t) + rowModulus raw e * volume.real S := by
    have hi := setIntegral_mono_on (hK.mono_set hsub) (hP.add hconst) hS
      (fun t ht => frozenKernel_le_buffered_positive_add_modulus picks raw hgrid hpositive
        hupper c e (hsub ht))
    simpa only [integral_add hP hconst, setIntegral_const, smul_eq_mul, mul_comm] using hi
  have hlost : (∫ t in D, frozenUpperPositiveKernel picks raw t) ≤
      rowMassBound raw * volume.real D := by
    have hi := norm_setIntegral_le_of_norm_le_const (childSubset_volume_lt_top raw c hDsub)
      (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (frozenUpperPositiveKernel_nonneg picks raw t)]
        exact frozenKernel_le_rowMassBound picks raw hgrid hpositive hupper c (hDsub ht))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hi)
  have heq : (∫ t in D, frozenUpperPositiveKernel picks raw t) =
      (∫ t in childBox raw c, frozenUpperPositiveKernel picks raw t) -
        ∫ t in S, frozenUpperPositiveKernel picks raw t :=
    setIntegral_sdiff hS hK hsub
  dsimp [childOwnerReserve]
  change (∫ t in childBox raw c, frozenUpperPositiveKernel picks raw t) -
      (rowMassBound raw * volume.real D + rowModulus raw e * volume.real S) ≤ _
  linarith

/-- Selected owner cells remain a disjoint half-open partition inside the
child; fullCell's actual original history is retained in every summand. -/
theorem childOwners_pairwise_disjoint (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    Set.PairwiseDisjoint
      (P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 : Set (Owner m))
      (fun j => childOwnerDomain raw c e chi m omega j) := by
  intro j _ k _ hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  exact hjk (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
    htj.2.2.2.1 htk.2.2.2.1)

theorem retained_positive_integral_eq_sum_child_owners
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (c : ChildIndex) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Owner m)) :
    (∫ t in retainedChild raw c e chi m omega J5, literalPositiveRawKernel e raw t) =
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        ∫ t in childOwnerDomain raw c e chi m omega j, literalPositiveRawKernel e raw t := by
  rw [retainedChild_eq_owner_union]
  apply integral_biUnion_finset
  · intro j _
    exact childOwnerDomain_measurable raw c e chi m omega j
  · exact childOwners_pairwise_disjoint raw c e chi m omega J5
  · intro j _
    exact (integrableOn_literalPositiveRawKernel_rawOwner raw hgrid hpositive e chi m omega j).mono_set
      (childOwnerDomain_subset_rawOwner raw hgrid c e chi m omega j)

/-- The true selected union, with the same mask and signed source, receives
only a proved Jensen lower bound minus the two observable reserves. -/
theorem certified_child_sub_reserve_le_literal_owner_sum
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd : (d : ℝ) = vertexD picks raw c)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    certifiedChildJensen picks raw c b d - childOwnerReserve raw c e chi m omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
  have hj := certifiedChildJensen_le_whole picks raw c
    (positiveKey_childLeft_pos raw hpositive c) hb2 hb4 hnew d hd
  have hc := whole_child_sub_reserve_le_retained_positive picks raw hgrid hpositive hupper
    c e chi m omega J5
  rw [retained_positive_integral_eq_sum_child_owners raw hgrid hpositive c e chi m omega J5] at hc
  have hs : (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      ∫ t in childOwnerDomain raw c e chi m omega j, literalPositiveRawKernel e raw t) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
    apply Finset.sum_le_sum
    intro j hj
    exact setIntegral_mono_set
      (integrableOn_literalPositiveRawKernel_rawOwner raw hgrid hpositive e chi m omega j)
      (Filter.Eventually.of_forall (fun t => literalPositiveRawKernel_nonneg e raw t))
      (Filter.Eventually.of_forall (fun t ht =>
        childOwnerDomain_subset_rawOwner raw hgrid c e chi m omega j ht))
  exact (sub_le_sub_right hj _).trans (hc.trans hs)

/-- The sharp child-local form is retained for disjoint summation: the
right-hand side is clipped owner integrals, not 64 copies of a parent. -/
theorem certified_child_sub_reserve_le_clipped_owner_sum
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    (c : ChildIndex) {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd : (d : ℝ) = vertexD picks raw c)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    certifiedChildJensen picks raw c b d - childOwnerReserve raw c e chi m omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        ∫ t in childOwnerDomain raw c e chi m omega j, literalPositiveRawKernel e raw t := by
  have hj := certifiedChildJensen_le_whole picks raw c
    (positiveKey_childLeft_pos raw hpositive c) hb2 hb4 hnew d hd
  have hc := whole_child_sub_reserve_le_retained_positive picks raw hgrid hpositive hupper
    c e chi m omega J5
  rw [retained_positive_integral_eq_sum_child_owners raw hgrid hpositive c e chi m omega J5] at hc
  exact (sub_le_sub_right hj _).trans hc

/-- Finite additivity for the positive literal kernel is established with
its own integrability and the same genuine half-open child-owner partition. -/
theorem positive_rawOwnerIntegral_eq_sum_64_children
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Owner m) :
    literalPositiveRawOwnerIntegral raw e chi m omega j =
      ∑ c : ChildIndex, ∫ t in childOwnerDomain raw c e chi m omega j,
        literalPositiveRawKernel e raw t := by
  unfold literalPositiveRawOwnerIntegral
  rw [rawOwnerDomain_eq_union_children raw hgrid]
  have hi := integrableOn_literalPositiveRawKernel_rawOwner raw hgrid hpositive e chi m omega j
  rw [integral_biUnion_finset (Finset.univ : Finset ChildIndex)
    (fun c _ => childOwnerDomain_measurable raw c e chi m omega j)
    (childOwnerDomains_pairwise_disjoint raw e chi m omega j)
    (fun c _ => hi.mono_set
      (childOwnerDomain_subset_rawOwner raw hgrid c e chi m omega j))]
  simp

/-- ALL 64 original children are summed once, after selecting zero for a
negative d. The signed integer vertex identities remain exact inputs. -/
theorem all64_certified_sub_reserves_le_literal_owner_sum
    (picks : ParentPicks) (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ c : ChildIndex, ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ChildIndex → ℤ) (hd : ∀ c : ChildIndex, (d c : ℝ) = vertexD picks raw c)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    (∑ c : ChildIndex, certifiedChildJensen picks raw c b (d c) -
        childOwnerReserve raw c e chi m omega J5) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ChildIndex))
    (fun c _ => certified_child_sub_reserve_le_clipped_owner_sum picks raw hgrid hpositive
      hupper c hb2 hb4 (hnew c) (d c) (hd c) e chi m omega J5)
  rw [Finset.sum_comm] at hs
  have heq : (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      ∑ c : ChildIndex, ∫ t in childOwnerDomain raw c e chi m omega j,
        literalPositiveRawKernel e raw t) =
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
    apply Finset.sum_congr rfl
    intro j _
    exact (positive_rawOwnerIntegral_eq_sum_64_children raw hgrid hpositive e chi m omega j).symm
  exact hs.trans_eq heq

/-- The same raw-row source is attached to its actual original variable
fourth/fifth owner gain, through the already proved positive-part comparison.
Every ancestry, geometry, gate and key premise of that source is retained. -/
theorem all64_certified_sub_reserves_le_actual_owner_sum
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) (hkey : KeyInjective records)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (RefinedCell q))
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true)
    (picks : ParentPicks) (raw : FifthWireRow) (hr : raw ∈ records)
    (hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ))
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ c : ChildIndex, ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ChildIndex → ℤ) (hd : ∀ c : ChildIndex, (d c : ℝ) = vertexD picks raw c) :
    (∑ c : ChildIndex, certifiedChildJensen picks raw c b (d c) -
        childOwnerReserve raw c e chi (refinedMesh q) omega J5) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hs := all64_certified_sub_reserves_le_literal_owner_sum picks raw (hgrid raw hr)
    (hpositive raw hr) hupper hb2 hb4 hnew d hd e chi (refinedMesh q) omega J5
  have ha : (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
      literalPositiveRawOwnerIntegral raw e chi (refinedMesh q) omega j) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
    apply Finset.sum_le_sum
    intro j hj
    exact literalPositiveRawOwnerIntegral_le_actual records q hq hgrid hmask hkey hpositive
      e he chi omega homega homegaRho rows4 licensed4 hgeometry J5 hgate raw hr j hj
  exact hs.trans ha

/-- Both observable errors remain separate after finite summation: omitted
geometry times one real mass bound, and retained geometry times the actual
buffer modulus. No unknown sign of a finite Rosser coefficient is used. -/
theorem sum_childOwnerReserve_eq_two_terms (raw : FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    (∑ c : ChildIndex, childOwnerReserve raw c e chi m omega J5) =
      rowMassBound raw * (∑ c : ChildIndex, volume.real (omittedChild raw c e chi m omega J5)) +
        rowModulus raw e * (∑ c : ChildIndex, volume.real (retainedChild raw c e chi m omega J5)) := by
  simp only [childOwnerReserve, Finset.sum_add_distrib, Finset.mul_sum]

end
end ImbalancedChen.P5ChildSelectedOwnerJensenReserve
