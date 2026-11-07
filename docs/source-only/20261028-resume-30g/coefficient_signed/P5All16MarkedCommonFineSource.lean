import ImbalancedChen.P5All16InnerCartesianDictionary
import ImbalancedChen.P5ZU1011OriginalPairedRowPrimeTests

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The SAME original half-open alphabet contains the four MARKED slots and
the residual slots.  Marked coordinates are ![p4,p3,p2,p1]; the native
paired mask is pulled back exactly once.  The geometric whole-cell
certificate below is independent of N and of all arithmetic tuples.
It retains the original joint band, complement mask, owner, selected
policy, residual upper gates and strict cutoff.  It is not a declaration
that an arbitrary arithmetic E or a policy decision fibre is Cartesian.

Every tuple of the resulting FULL boxes is proved to belong to the
independently defined actual all16 PairMark source.  The original row
coefficient is evaluated there, giving only the RESIDUAL parity and the
same original beta.  No factorial is divided out of the marked source.
Uncovered actual source points remain in a separate arithmetic remainder.
-/

namespace ImbalancedChen.P5Z.All16MarkedCommonFineSource
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open All16PhysicalOwnerDiscrepancy All16ActualInnerWallReconstruction
open All16FineMeshGateScalar All16InnerCartesianDictionary
open ActualInnerMeshSeparatedGamma PresievedRoughGateMeshReserve
open PresievedFineLabelPrimeBoxes JointPresievedSlotAffineRealization

abbrev CoarseGrid (n : ℕ) := U1011OriginalFifteenNativeGridCells.Grid n

def pack (p : Fin 4 → ℕ) : Four := ((p 3, p 2), (p 1, p 0))

@[simp] theorem slots_pack (p : Fin 4 → ℕ) : slots (pack p) = p := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem pack_slots (t : Four) : pack (slots t) = t := rfl

@[simp] theorem fullPrefix_pack (p : Fin 4 → ℕ) : fullPrefix (pack p) = ∏ i, p i := by
  simp only [fullPrefix, slots_pack]

def cellZeta (n : ℕ) (eta : ℚ) (c : CoarseGrid n) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c))
    (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ)

def cellEll (n : ℕ) (eta : ℚ) (c : CoarseGrid n) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c))
    (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ)

def cellZ (n N : ℕ) (eta : ℚ) (c : CoarseGrid n) : ℝ :=
  (N : ℝ) ^ cellZeta n eta c

def cellCap (n N : ℕ) (eta : ℚ) (c : CoarseGrid n) : ℕ := Nat.ceil (cellZ n N eta c)

/-- Literal ORIGINAL fine bins, on one common prime carrier for BOTH
marked and residual occurrences.  Physical cutoffs are imposed below by
the geometric certificate, not by changing the alphabet in one group. -/
def commonAlphabet (N m : ℕ) : Fin (m + 1) → Finset ℕ :=
  meshPrimeAlphabet N N 1 N m

def commonVectors (N m r : ℕ) (a : Grid r m) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun i => commonAlphabet N m (a i))

def fullWord {r m : ℕ} (a : Grid 4 m) (j : Grid r m) : List (Fin (m + 1)) :=
  List.ofFn a ++ List.ofFn j

/-- Exact occurrence alphabet for the REAL whole marked+rough programs.
It is separate from any independent prime-test word. -/
def occurrenceLabels {r m : ℕ} (a : Grid 4 m) (j : Grid r m) :
    Fin 4 ⊕ Fin r → Fin (m + 1) := Sum.elim a j

def wholeOccurrences (r : ℕ) : List (Fin 4 ⊕ Fin r) :=
  List.ofFn Sum.inl ++ List.ofFn Sum.inr

theorem whole_occurrences_labels {r m : ℕ} (a : Grid 4 m) (j : Grid r m) :
    (wholeOccurrences r).map (occurrenceLabels a j) = fullWord a j := by
  simp [wholeOccurrences, occurrenceLabels, fullWord, List.map_ofFn, Function.comp_def]

theorem vectors_list_iff {N m r : ℕ} (a : Grid r m) (p : Fin r → ℕ) :
    p ∈ commonVectors N m r a ↔
      List.ofFn p ∈ meshPrimeBox N N 1 N m a := by
  simp only [commonVectors, Fintype.mem_piFinset, meshPrimeBox, commonAlphabet,
    mem_primeSlotBox_ofFn]

/-- No coordinate quotient or product deduplication: vector tuples are
in bijection with literal FULL common-alphabet list boxes. -/
theorem vectors_sum_list (N m r : ℕ) (a : Grid r m) (H : List ℕ → ℝ) :
    (∑ p ∈ commonVectors N m r a, H (List.ofFn p)) =
      ∑ ps ∈ meshPrimeBox N N 1 N m a, H ps := by
  apply Finset.sum_bij (fun p hp => List.ofFn p)
  · intro p hp
    exact (vectors_list_iff a p).mp hp
  · intro p hp q hq heq
    exact List.ofFn_injective heq
  · intro ps hps
    have hlen : ps.length = r := by
      simpa only [List.length_ofFn] using
        actualPrimeSlotBox_length (commonAlphabet N m) (List.ofFn a) ps hps
    subst r
    refine ⟨slotVector ps, ?_, ofFn_slotVector ps⟩
    apply (vectors_list_iff a _).mpr
    simpa only [ofFn_slotVector] using hps
  · intro p hp
    rfl

theorem vectors_log_cell {N m r : ℕ} (hN : 1 < N) {a : Grid r m}
    {p : Fin r → ℕ} (hp : p ∈ commonVectors N m r a) :
    actualPrimeTupleLog N p ∈ cell 0 1 m a :=
  ((mesh_box_dictionary hN 1 N a p).mp ((vectors_list_iff a p).mp hp)).2

theorem vectors_prime_carrier {N m r : ℕ} {a : Grid r m} {p : Fin r → ℕ}
    (hp : p ∈ commonVectors N m r a) (i : Fin r) :
    p i ∈ chenAdditivePrimeCarrier N := by
  have hi := (Fintype.mem_piFinset.mp hp) i
  have hd := mem_roughPrimeFinset.mp (mesh_prime_rough hi)
  exact mem_chenAdditivePrimeCarrier.mpr
    ⟨hd.1, hd.2.1, hd.2.1.coprime_iff_not_dvd.mpr hd.2.2.1⟩

/-- Original U10/U11 joint source in decreasing policy coordinates.
M is the fixed original paired region, not an arbitrary integer mask. -/
def prefixGeometry (M : Set (ℝ × ℝ)) (v : Fin 4 → ℝ) : Prop :=
  (417 / 5000 : ℝ) ≤ v 3 ∧ v 1 < (19 / 125 : ℝ) ∧
    v 0 < (59 / 250 : ℝ) ∧ StrictAnti v ∧
    (v 0 < (19 / 125 : ℝ) ∨ (v 0, v 1) ∉ M)

/-- All fields are original geometric/endpoint data, before N.  In
particular neither an actual source equality nor a gamma norm is a field. -/
structure WholeCell {n m r : ℕ} (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ))
    (c : CoarseGrid n) (a : Grid 4 m) (j : Grid r m) : Prop where
  tag : U1011OriginalSixteenStaticCellWinner.chosenTag
    (U1011OriginalFifteenNativeGridCells.gridBox n c) ≠ 0
  prefix : ∀ v ∈ cell 0 1 m a, prefixGeometry M v
  owner : cell 0 1 m a ⊆ U1011OriginalFifteenNativeGridCells.cell n c
  inner : j ∈ innerCells r 0 1 (cellEll n eta c) m
  residualLower : ∀ i, rho ≤ logPrimeMeshLo 0 1 m j i
  residualUpper : ∀ i, logPrimeMeshHi 0 1 m j i ≤ cellZeta n eta c
  markedLower : ∀ i, cellZeta n eta c ≤ logPrimeMeshLo 0 1 m a i

/-- Actual original last-pair pullback; adopting the actual P1 pairRegion
gives its original deletionMask by the existing definitional dictionary. -/
theorem whole_prefix_in_joint {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {p : Fin 4 → ℕ}
    (hp : p ∈ commonVectors N m 4 a) :
    pack p ∈ jointSelector N (U1011OriginalPairedRowPrimeTests.nativeMask M N) := by
  have hv := vectors_log_cell hN hp
  obtain ⟨hA, h3H, h4D, hantiLog, hmask⟩ := h.prefix _ hv
  have hpos : ∀ i, 0 < p i :=
    fun i => (mem_chenAdditivePrimeCarrier.mp (vectors_prime_carrier hp i)).2.1.pos
  have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hantiLog
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpw (i : Fin 4) := actualPrimeTupleLog_rpow hN p hpos i
  have hA' : (N : ℝ) ^ (417 / 5000 : ℝ) ≤ p 3 := by
    rw [← hpw 3]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hA
  have h3H' : (p 1 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) := by
    rw [← hpw 1]
    exact Real.rpow_lt_rpow_of_exponent_lt hn h3H
  have h4D' : (p 0 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) := by
    rw [← hpw 0]
    exact Real.rpow_lt_rpow_of_exponent_lt hn h4D
  have hm : (p 0 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) ∨
      ¬ U1011OriginalPairedRowPrimeTests.nativeMask M N (p 1, p 0) := by
    rcases hmask with hm | hm
    · left
      rw [← hpw 0]
      exact Real.rpow_lt_rpow_of_exponent_lt hn hm
    · right
      simpa only [U1011OriginalPairedRowPrimeTests.nativeMask_log_dictionary,
        U1011OriginalPairedRowPrimeTests.outerPair] using hm
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨vectors_prime_carrier hp 3, vectors_prime_carrier hp 2⟩,
    Finset.mem_product.mpr ⟨vectors_prime_carrier hp 1, vectors_prime_carrier hp 0⟩⟩, ?_⟩
  exact ⟨hA', hanti (by decide : (2 : Fin 4) < 3),
    hanti (by decide : (1 : Fin 4) < 2), hanti (by decide : (0 : Fin 4) < 1),
    h3H', h4D', hm⟩

theorem whole_prefix_owner {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {p : Fin 4 → ℕ}
    (hp : p ∈ commonVectors N m 4 a) :
    U1011OriginalFifteenNativeGridCells.owner n (coordinates N (pack p)) = c := by
  apply U1011OriginalFifteenNativeGridCells.owner_eq_of_mem n
  simpa only [coordinates, slots_pack] using h.owner (vectors_log_cell hN hp)

theorem whole_prefix_actual {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {p : Fin 4 → ℕ}
    (hp : p ∈ commonVectors N m 4 a) :
    pack p ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N
      (U1011OriginalPairedRowPrimeTests.nativeMask M N) := by
  refine Finset.mem_filter.mpr ⟨whole_prefix_in_joint hN h hp, ?_⟩
  simpa only [U1011OriginalSixteenStaticNativeCompiler.tupleTag,
    U1011OriginalSixteenStaticNativeCompiler.ownerBox, whole_prefix_owner hN h hp] using h.tag

/-- A common-alphabet residual box is the ORIGINAL physical rough box;
its lower cutoff, strict upper cutoff and enumeration cap are all derived. -/
theorem whole_residual_original_box {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {u : Fin r → ℕ}
    (hu : u ∈ commonVectors N m r j) :
    List.ofFn u ∈ meshPrimeBox N (cellCap n N eta c) ((N : ℝ) ^ rho)
      (cellZ n N eta c) m j := by
  have hv := vectors_log_cell hN hu
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ i, 0 < u i :=
    fun i => (mem_chenAdditivePrimeCarrier.mp (vectors_prime_carrier hu i)).2.1.pos
  apply (mesh_box_dictionary hN _ _ j u).mpr
  refine ⟨?_, hv⟩
  intro i
  rw [mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)]
  have hd := mem_chenAdditivePrimeCarrier.mp (vectors_prime_carrier hu i)
  refine ⟨hd.2.1, hd.2.1.coprime_iff_not_dvd.mp hd.2.2, ?_, ?_⟩
  · rw [← actualPrimeTupleLog_rpow hN u hpos i]
    exact Real.rpow_le_rpow_of_exponent_le hn.le
      ((h.residualLower i).trans ((mem_logPrimeMeshCell.mp hv i).1))
  · change (u i : ℝ) < (N : ℝ) ^ cellZeta n eta c
    rw [← actualPrimeTupleLog_rpow hN u hpos i]
    exact Real.rpow_lt_rpow_of_exponent_lt hn
      (((mem_logPrimeMeshCell.mp hv i).2).trans_le (h.residualUpper i))

/-- Every COMPLETE marked/residual Cartesian tuple is an actual PairMark.
This uses the original source and retained tree, not a supplied equality. -/
theorem whole_tuple_actual_pair {n N m r e : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {p : Fin 4 → ℕ} {u : Fin r → ℕ}
    (hp : p ∈ commonVectors N m 4 a) (hu : u ∈ commonVectors N m r j)
    (he : e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho)) :
    (⟨pack p, (e, (List.ofFn u).prod)⟩ : PairMark) ∈
      pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N) := by
  have ht := whole_prefix_actual hN h hp
  have ho := whole_prefix_owner hN h hp
  have hZ : U1011OriginalSixteenJointNearCapCompiler.Z n N eta (pack p) = cellZ n N eta c := by
    simp only [U1011OriginalSixteenJointNearCapCompiler.Z,
      U1011OriginalSixteenStaticNativeCompiler.selectedPolicy,
      U1011OriginalSixteenStaticNativeCompiler.ownerBox, ho,
      U1011OriginalSixteenJointNearCapCompiler.rowZ, cellZ, cellZeta]
  have hD : U1011OriginalSixteenJointNearCapCompiler.D n N eta (pack p) =
      (N : ℝ) ^ cellEll n eta c := by
    simp only [U1011OriginalSixteenJointNearCapCompiler.D,
      U1011OriginalSixteenStaticNativeCompiler.selectedPolicy,
      U1011OriginalSixteenStaticNativeCompiler.ownerBox, ho,
      U1011OriginalSixteenJointNearCapCompiler.rowD, cellEll]
  have hL : 1 < (N : ℝ) ^ cellEll n eta c := by
    rw [← hD]
    exact (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  have hd := inner_list_actual_retained hN ((N : ℝ) ^ rho) (cellZ n N eta c)
    (cellEll n eta c) hL h.inner (List.ofFn u) (whole_residual_original_box hN h hu)
  apply Finset.mem_sigma.mpr
  refine ⟨ht, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · simpa only [rowSmall, hZ, cellCap] using he
  · simpa only [rowRough, hZ, hD, cellCap] using hd

/-- The original coefficient on EVERY complete Cartesian source tuple,
with the exact residual sign and the single frozen beta level B. -/
theorem whole_tuple_actual_coefficient {n N m r e : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho B : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) {p : Fin 4 → ℕ} {u : Fin r → ℕ}
    (hp : p ∈ commonVectors N m 4 a) (hu : u ∈ commonVectors N m r j)
    (he : e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho)) :
    rowCoefficient n N eta ((N : ℝ) ^ rho) B (pack p) (e * (List.ofFn u).prod) =
      (-1 : ℝ) ^ r * rawBetaWeight N (cellCap n N eta c) r ((N : ℝ) ^ rho) B e := by
  have ht := whole_prefix_actual hN h hp
  have ho := whole_prefix_owner hN h hp
  have hD : U1011OriginalSixteenJointNearCapCompiler.D n N eta (pack p) =
      (N : ℝ) ^ cellEll n eta c := by
    simp only [U1011OriginalSixteenJointNearCapCompiler.D,
      U1011OriginalSixteenStaticNativeCompiler.selectedPolicy,
      U1011OriginalSixteenStaticNativeCompiler.ownerBox, ho,
      U1011OriginalSixteenJointNearCapCompiler.rowD, cellEll]
  have hL : 1 < (N : ℝ) ^ cellEll n eta c := by
    rw [← hD]
    exact (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  have hv := inner_list_actual_presieved_value hN ((N : ℝ) ^ rho) (cellZ n N eta c)
    (cellEll n eta c) B hL h.inner he (List.ofFn u) (whole_residual_original_box hN h hu)
  simpa only [rowCoefficient, U1011OriginalSixteenJointNearCapCompiler.Z,
    U1011OriginalSixteenJointNearCapCompiler.D,
    U1011OriginalSixteenStaticNativeCompiler.selectedPolicy,
    U1011OriginalSixteenStaticNativeCompiler.ownerBox, ho,
    U1011OriginalSixteenJointNearCapCompiler.rowZ,
    U1011OriginalSixteenJointNearCapCompiler.rowD, cellCap, cellZ, cellZeta, cellEll] using hv

/-- The physical prefix is absorbed into the SAME complete product.
There is no outside prime prefix in the resulting argument of F. -/
theorem whole_tuple_complete_modulus {r : ℕ} (p : Fin 4 → ℕ) (u : Fin r → ℕ) (e : ℕ) :
    fullPrefix (pack p) * (e * (List.ofFn u).prod) =
      e * (List.ofFn p ++ List.ofFn u).prod := by
  rw [fullPrefix_pack, List.prod_append, List.prod_ofFn]
  ring

/-- Actual marked AND residual Cartesian source, before group choice.
Only the original residual denominator occurs.  No marked factorial is
inserted.  This is the independently derived source port for the peer
same-whole-word three-gamma/beta theorem. -/
theorem whole_cell_source_eq_raw_full_box {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho B : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho),
      ∑ p ∈ commonVectors N m 4 a, ∑ u ∈ commonVectors N m r j,
        rowCoefficient n N eta ((N : ℝ) ^ rho) B (pack p) (e * (List.ofFn u).prod) *
          F (fullPrefix (pack p) * (e * (List.ofFn u).prod))) =
      ((-1 : ℝ) ^ r / (meshMultiplicity j : ℝ)) *
        ∑ e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho),
          rawBetaWeight N (cellCap n N eta c) r ((N : ℝ) ^ rho) B e *
            ∑ xs ∈ actualPrimeSlotBox (commonAlphabet N m) (fullWord a j), F (e * xs.prod) := by
  rw [inner_mesh_multiplicity_one (cellEll n eta c) h.inner]
  simp only [Nat.cast_one, div_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  calc
    _ = ∑ p ∈ commonVectors N m 4 a, ∑ u ∈ commonVectors N m r j,
        ((-1 : ℝ) ^ r * rawBetaWeight N (cellCap n N eta c) r ((N : ℝ) ^ rho) B e) *
          F (e * (List.ofFn p ++ List.ofFn u).prod) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro u hu
      rw [whole_tuple_actual_coefficient hN heta h hp hu he, whole_tuple_complete_modulus]
    _ = _ := by
      rw [fullWord, actualPrimeSlotBox_product_sum_append]
      simp_rw [← vectors_sum_list N m r j]
      rw [← vectors_sum_list N m 4 a]
      simp only [Finset.mul_sum, List.prod_append, mul_assoc]

end
end ImbalancedChen.P5Z.All16MarkedCommonFineSource
