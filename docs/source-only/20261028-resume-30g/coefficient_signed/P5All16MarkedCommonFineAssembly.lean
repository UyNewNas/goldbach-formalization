import ImbalancedChen.P5All16MarkedFineScalarBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The certified FULL marked/residual boxes are embedded into the actual
independently defined all16 PairMark source.  The maps are injective,
and different coarse owners, marked labels, residual labels and ranks
are disjoint.  Their union is therefore counted exactly once.

The remainder is independently defined as the ACTUAL source complement
and pushed to the SAME physical full q with original rowCoefficient.
No arbitrary E is hidden in F, no uncovered point is discarded, and no
wall smallness, proper-face localization, independent-test-u atlas or
internal PP conclusion is asserted by this finite source assembly.
-/

namespace ImbalancedChen.P5Z.All16MarkedCommonFineAssembly
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open OriginalPresievedRoughPrimeSlots JointPresievedSlotAffineRealization
open All16PhysicalOwnerDiscrepancy All16ActualInnerWallReconstruction
open All16FineMeshGateScalar PresievedRoughGateMeshReserve
open All16InnerCartesianDictionary All16MarkedCommonFineSource All16MarkedFineScalarBudget

abbrev RawTuple (r : ℕ) := ℕ × (Fin 4 → ℕ) × (Fin r → ℕ)

def tupleBox (n N m r : ℕ) (eta : ℚ) (rho : ℝ) (k : Key n m r) : Finset (RawTuple r) :=
  actualSmallRosserSupport N (cellCap n N eta k.1) ((N : ℝ) ^ rho) ×ˢ
    (commonVectors N m 4 k.2.1 ×ˢ commonVectors N m r k.2.2)

def tuplePair {r : ℕ} (x : RawTuple r) : PairMark :=
  ⟨pack x.2.1, (x.1, (List.ofFn x.2.2).prod)⟩

def atomPairs (n N m r : ℕ) (eta : ℚ) (rho : ℝ) (k : Key n m r) : Finset PairMark :=
  (tupleBox n N m r eta rho k).image tuplePair

private theorem cell_level_gt_one {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2) {p : Fin 4 → ℕ}
    (hp : p ∈ commonVectors N m 4 k.2.1) : 1 < (N : ℝ) ^ cellEll n eta k.1 := by
  have ht := whole_prefix_actual hN h hp
  have ho := whole_prefix_owner hN h hp
  have hD : U1011OriginalSixteenJointNearCapCompiler.D n N eta (pack p) =
      (N : ℝ) ^ cellEll n eta k.1 := by
    simp only [U1011OriginalSixteenJointNearCapCompiler.D,
      U1011OriginalSixteenStaticNativeCompiler.selectedPolicy,
      U1011OriginalSixteenStaticNativeCompiler.ownerBox, ho,
      U1011OriginalSixteenJointNearCapCompiler.rowD, cellEll]
  rw [← hD]
  exact (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1

theorem atom_pairs_subset_actual {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (hk : k ∈ certifiedKeys n m r eta rho M) :
    atomPairs n N m r eta rho k ⊆
      pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨he, hpu⟩ := Finset.mem_product.mp hx
  obtain ⟨hp, hu⟩ := Finset.mem_product.mp hpu
  exact whole_tuple_actual_pair hN heta (Finset.mem_filter.mp hk).2.1 hp hu he

theorem tuple_pair_injective {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2) :
    Set.InjOn (@tuplePair r) (tupleBox n N m r eta rho k : Set (RawTuple r)) := by
  intro x hx y hy heq
  obtain ⟨hxe, hxpu⟩ := Finset.mem_product.mp hx
  obtain ⟨hxp, hxu⟩ := Finset.mem_product.mp hxpu
  obtain ⟨hye, hypu⟩ := Finset.mem_product.mp hy
  obtain ⟨hyp, hyu⟩ := Finset.mem_product.mp hypu
  have hp : x.2.1 = y.2.1 := by
    simpa only [tuplePair, slots_pack] using congrArg (fun z : PairMark => slots z.1) heq
  have he : x.1 = y.1 := congrArg (fun z : PairMark => z.2.1) heq
  have hd : (List.ofFn x.2.2).prod = (List.ofFn y.2.2).prod :=
    congrArg (fun z : PairMark => z.2.2) heq
  have hu : x.2.2 = y.2.2 := by
    apply List.ofFn_injective
    exact inner_box_product_injective hN ((N : ℝ) ^ rho) (cellZ n N eta k.1)
      (cellEll n eta k.1) (cell_level_gt_one hN heta h hxp) h.inner
      (whole_residual_original_box hN h hxu) (whole_residual_original_box hN h hyu) hd
  exact Prod.ext he (Prod.ext hp hu)

theorem atom_pair_rank {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (hk : k ∈ certifiedKeys n m r eta rho M) {z : PairMark}
    (hz : z ∈ atomPairs n N m r eta rho k) : z.2.2.primeFactors.card = r := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨he, hpu⟩ := Finset.mem_product.mp hx
  obtain ⟨hp, hu⟩ := Finset.mem_product.mp hpu
  have h := (Finset.mem_filter.mp hk).2.1
  exact inner_box_product_rank hN ((N : ℝ) ^ rho) (cellZ n N eta k.1)
    (cellEll n eta k.1) (cell_level_gt_one hN heta h hp) h.inner
    (whole_residual_original_box hN h hu)

/-- Coarse ownership and both half-open fine labels are UNIQUE on the
literal physical pair; no product projection collapses marked tuples. -/
theorem atom_pairs_disjoint {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) {rho : ℝ} {M : Set (ℝ × ℝ)}
    {k l : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M)
    (hl : l ∈ certifiedKeys n m r eta rho M) (hne : k ≠ l) :
    Disjoint (atomPairs n N m r eta rho k) (atomPairs n N m r eta rho l) := by
  apply Finset.disjoint_left.mpr
  intro z hzk hzl
  obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hzk
  obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hzl
  obtain ⟨hxe, hxpu⟩ := Finset.mem_product.mp hx
  obtain ⟨hxp, hxu⟩ := Finset.mem_product.mp hxpu
  obtain ⟨hye, hypu⟩ := Finset.mem_product.mp hy
  obtain ⟨hyp, hyu⟩ := Finset.mem_product.mp hypu
  have heq := hxz.trans hyz.symm
  have hp : x.2.1 = y.2.1 := by
    simpa only [tuplePair, slots_pack] using congrArg (fun z : PairMark => slots z.1) heq
  have hd : (List.ofFn x.2.2).prod = (List.ofFn y.2.2).prod :=
    congrArg (fun z : PairMark => z.2.2) heq
  have hkc := (Finset.mem_filter.mp hk).2.1
  have hlc := (Finset.mem_filter.mp hl).2.1
  have hc : k.1 = l.1 := by
    rw [← whole_prefix_owner hN hkc hxp, ← whole_prefix_owner hN hlc hyp, hp]
  have ha : k.2.1 = l.2.1 := by
    apply logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 1)
      (vectors_log_cell hN hxp)
    simpa only [← hp] using vectors_log_cell hN hyp
  have hps : List.ofFn x.2.2 = List.ofFn y.2.2 := by
    have hxcan := inner_box_tuple_eq_canonical hN ((N : ℝ) ^ rho) (cellZ n N eta k.1)
      (cellEll n eta k.1) (cell_level_gt_one hN heta hkc hxp) hkc.inner
      (whole_residual_original_box hN hkc hxu)
    have hycan := inner_box_tuple_eq_canonical hN ((N : ℝ) ^ rho) (cellZ n N eta l.1)
      (cellEll n eta l.1) (cell_level_gt_one hN heta hlc hyp) hlc.inner
      (whole_residual_original_box hN hlc hyu)
    rw [hxcan.2, hycan.2, hc, hd]
  have hu := List.ofFn_injective hps
  have hj : k.2.2 = l.2.2 := by
    apply logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 1)
      (vectors_log_cell hN hxu)
    simpa only [← hu] using vectors_log_cell hN hyu
  exact hne (Prod.ext hc (Prod.ext ha hj))

def rankPairs (n N m r : ℕ) (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ)) : Finset PairMark :=
  (certifiedKeys n m r eta rho M).biUnion (atomPairs n N m r eta rho)

def cartesianPairs (R n N m : ℕ) (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ)) : Finset PairMark :=
  (Finset.range (R + 1)).biUnion (fun r => rankPairs n N m r eta rho M)

theorem cartesian_pairs_subset_actual {R n N m : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) (rho : ℝ) (M : Set (ℝ × ℝ)) :
    cartesianPairs R n N m eta rho M ⊆
      pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N) := by
  intro z hz
  obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
  exact atom_pairs_subset_actual hN heta hk hz

theorem cartesian_pairs_sum (R n N m : ℕ) (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) (rho : ℝ) (M : Set (ℝ × ℝ)) (H : PairMark → ℝ) :
    (∑ z ∈ cartesianPairs R n N m eta rho M, H z) =
      ∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
        ∑ z ∈ atomPairs n N m r eta rho k, H z := by
  have hkeys (r : ℕ) : Set.PairwiseDisjoint (certifiedKeys n m r eta rho M : Set (Key n m r))
      (atomPairs n N m r eta rho) := by
    intro k hk l hl hne
    exact atom_pairs_disjoint hN heta hk hl hne
  have hranks : Set.PairwiseDisjoint (Finset.range (R + 1) : Set ℕ)
      (fun r => rankPairs n N m r eta rho M) := by
    intro r hr s hs hne
    apply Finset.disjoint_left.mpr
    intro z hzr hzs
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzr
    obtain ⟨l, hl, hzl⟩ := Finset.mem_biUnion.mp hzs
    exact hne ((atom_pair_rank hN heta hk hzk).symm.trans (atom_pair_rank hN heta hl hzl))
  rw [cartesianPairs, Finset.sum_biUnion hranks]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_biUnion (hkeys r)

def rawAtomLinear (n N m r : ℕ) (eta : ℚ) (rho B : ℝ) (k : Key n m r) (F : ℕ → ℝ) : ℝ :=
  ((-1 : ℝ) ^ r / (meshMultiplicity k.2.2 : ℝ)) *
    ∑ e ∈ actualSmallRosserSupport N (cellCap n N eta k.1) ((N : ℝ) ^ rho),
      rawBetaWeight N (cellCap n N eta k.1) r ((N : ℝ) ^ rho) B e *
        ∑ xs ∈ actualPrimeSlotBox (commonAlphabet N m) (fullWord k.2.1 k.2.2), F (e * xs.prod)

theorem actual_atom_eq_raw_full_box {n N m r : ℕ} (hN : 1 < N) {eta : ℚ}
    (heta : 0 < eta) (rho B : ℝ) (M : Set (ℝ × ℝ)) {k : Key n m r}
    (hk : k ∈ certifiedKeys n m r eta rho M) (F : ℕ → ℝ) :
    (∑ z ∈ atomPairs n N m r eta rho k,
      pairWeight n N eta ((N : ℝ) ^ rho) B z * F (pairModulus z)) =
      rawAtomLinear n N m r eta rho B k F := by
  rw [atomPairs, Finset.sum_image]
  · simp only [tupleBox, Finset.sum_product, tuplePair, pairWeight, pairModulus]
    exact whole_cell_source_eq_raw_full_box hN heta (Finset.mem_filter.mp hk).2.1 F
  · exact tuple_pair_injective hN heta (Finset.mem_filter.mp hk).2.1

/-- Independently defined genuine arithmetic complement; it retains
every original marked/e/d weight, including zero and boundary rows. -/
def remainderPairs (R n N m : ℕ) (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ)) : Finset PairMark :=
  (pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N)).filter
    (fun z => z ∉ cartesianPairs R n N m eta rho M)

def remainderSupport (R n N m : ℕ) (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ)) : Finset ℕ :=
  (remainderPairs R n N m eta rho M).image pairModulus

def remainderRho (R n N m : ℕ) (eta : ℚ) (rho B : ℝ) (M : Set (ℝ × ℝ)) (q : ℕ) : ℝ :=
  ∑ z ∈ (remainderPairs R n N m eta rho M).filter (fun z => pairModulus z = q),
    pairWeight n N eta ((N : ℝ) ^ rho) B z

theorem remainder_exact_pushforward (R n N m : ℕ) (eta : ℚ) (rho B : ℝ)
    (M : Set (ℝ × ℝ)) (F : ℕ → ℝ) :
    (∑ z ∈ remainderPairs R n N m eta rho M,
      pairWeight n N eta ((N : ℝ) ^ rho) B z * F (pairModulus z)) =
      ∑ q ∈ remainderSupport R n N m eta rho M,
        remainderRho R n N m eta rho B M q * F q := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := remainderPairs R n N m eta rho M)
    (t := remainderSupport R n N m eta rho M) (g := pairModulus)
    (fun z hz => Finset.mem_image_of_mem pairModulus hz)
    (fun z => pairWeight n N eta ((N : ℝ) ^ rho) B z * F (pairModulus z))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q hq
  rw [remainderRho, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [(Finset.mem_filter.mp hz).2]

/-- Actual original same-rho source = FULL common marked/residual raw
atoms + independent genuine remainder, for EVERY signed full-q test.
The real adopted E is obtained by M=the original pairRegion, without
changing this source or its exact coprime-mean test. -/
theorem actual_all16_common_fine_plus_remainder (R n N m : ℕ) (hN : 1 < N)
    (eta : ℚ) (heta : 0 < eta) (rho B : ℝ) (M : Set (ℝ × ℝ)) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho)
      (U1011OriginalPairedRowPrimeTests.nativeMask M N),
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B
        (U1011OriginalPairedRowPrimeTests.nativeMask M N) q * F q) =
      (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
        rawAtomLinear n N m r eta rho B k F) +
      ∑ q ∈ remainderSupport R n N m eta rho M, remainderRho R n N m eta rho B M q * F q := by
  have hfull : (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho)
      (U1011OriginalPairedRowPrimeTests.nativeMask M N),
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B
        (U1011OriginalPairedRowPrimeTests.nativeMask M N) q * F q) =
      ∑ z ∈ pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N),
        pairWeight n N eta ((N : ℝ) ^ rho) B z * F (pairModulus z) := by
    rw [← joint_exact_pushforward n N eta _ B _ F]
    unfold pairMarks
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    rw [physical_row_pullback, Finset.sum_product]
    rfl
  rw [hfull]
  have hfilter : (pairMarks n N eta ((N : ℝ) ^ rho)
      (U1011OriginalPairedRowPrimeTests.nativeMask M N)).filter
      (fun z => z ∈ cartesianPairs R n N m eta rho M) = cartesianPairs R n N m eta rho M := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cartesian_pairs_subset_actual hN heta rho M h, h⟩⟩
  have hs := Finset.sum_filter_add_sum_filter_not
    (pairMarks n N eta ((N : ℝ) ^ rho) (U1011OriginalPairedRowPrimeTests.nativeMask M N))
    (fun z => z ∈ cartesianPairs R n N m eta rho M)
    (fun z => pairWeight n N eta ((N : ℝ) ^ rho) B z * F (pairModulus z))
  rw [hfilter] at hs
  rw [← hs, remainder_exact_pushforward]
  congr 1
  rw [cartesian_pairs_sum R n N m hN heta rho M]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro k hk
  exact actual_atom_eq_raw_full_box hN heta rho B M hk F

end
end ImbalancedChen.P5Z.All16MarkedCommonFineAssembly
