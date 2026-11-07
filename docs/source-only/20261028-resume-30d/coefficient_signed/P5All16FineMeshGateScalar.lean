import ImbalancedChen.P5All16SortedBlockAtomScalar
import ImbalancedChen.P5PresievedRoughSmoothCover
import ImbalancedChen.ActualFrozenSelectedPairSlots

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual retained all16 rough words receive a fixed fine mesh alphabet and
an exact whole-cell gate certificate or an explicit proper affine wall
reserve.  No arithmetic prime on a crossing cell is deleted.  For every
inner cell all tuples of the SAME original Cartesian fine prime box pass
the original strict upper tests and decreasing-order test.

The three-group occurrence assignment below computes the original frozen
selected-pair algorithm ONCE from these fine upper endpoints (low ranks
use the unsplit first group).  It partitions the entire Cartesian box;
it is not recomputed on observed prime values or discrepancies.  This
file proves exact raw tuple-sum regrouping, not the final three normalized
per-label gamma identity/capacity licence for all physical all16 branches.

The derived absolute scalar budget is for residual fine cells at fixed
small e and fixed physical prefix: sum |beta_r(e)/M_res(j)| is at most
sum_{r<=R}(m+1)^r.  It precedes N, e and the marked tuple.  It does NOT sum
over small e or physical marked tuples, and must not be reported as the
complete marked/raw coefficient scalar-mass estimate.
-/

namespace ImbalancedChen.P5Z.All16FineMeshGateScalar
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryCommonBetaModel OriginalPresievedRoughPrimeSlots
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open JointPresievedSlotAffineRealization PresievedRoughSlotAffineGates
open PresievedRoughGateMeshReserve PresievedFineLabelPrimeBoxes
open ActualAll16UnrestrictedResidualConvolution All16PhysicalOwnerDiscrepancy
open All16CanonicalFineWordNoZGuard

/-- One common half-open fine alphabet on [0,1), retaining the exact
original rough cutoff, prime ceiling and target-prime exclusion. -/
def meshPrimeAlphabet (N cap : ℕ) (w Z : ℝ) (m : ℕ) (i : Fin (m + 1)) : Finset ℕ :=
  finePrimeSet N cap w Z (logPrimeMeshPoint 0 1 m i.val)
    (logPrimeMeshPoint 0 1 m (i.val + 1))

/-- This mesh is the ORIGINAL fine alphabet at tau=1/(m+1), intersected
with the unchanged physical rough set.  Enumeration caps and exclusions
are not silently replaced by those of the standalone fine interval. -/
theorem mesh_alphabet_eq_original_intersection (N cap m : ℕ) (w Z : ℝ)
    (i : Fin (m + 1)) :
    meshPrimeAlphabet N cap w Z m i =
      roughPrimeFinset N cap w Z ∩
        actualPrimeFineLabelFinset N (1 / (m + 1 : ℝ)) i.val := by
  have hlo : logPrimeMeshPoint 0 1 m i.val =
      (1 / (m + 1 : ℝ)) * (i.val : ℝ) := by
    simp only [logPrimeMeshPoint, logPrimeMeshStep]
    ring
  have hhi : logPrimeMeshPoint 0 1 m (i.val + 1) =
      (1 / (m + 1 : ℝ)) * ((i.val : ℝ) + 1) := by
    simp only [logPrimeMeshPoint, logPrimeMeshStep, Nat.cast_add, Nat.cast_one]
    ring
  ext p
  constructor
  · intro hp
    obtain ⟨hr, hl, hu⟩ := Finset.mem_filter.mp hp
    have hpr := mem_roughPrimeFinset.mp hr
    apply Finset.mem_inter.mpr
    refine ⟨hr, mem_actualPrimeFineLabelFinset.mpr ⟨hpr.2.1, hpr.2.2.1, ?_, ?_⟩⟩
    · simpa only [hlo] using hl
    · simpa only [hhi] using hu
  · intro hp
    obtain ⟨hr, hf⟩ := Finset.mem_inter.mp hp
    have h := mem_actualPrimeFineLabelFinset.mp hf
    apply Finset.mem_filter.mpr
    exact ⟨hr, by simpa only [hlo] using h.2.2.1, by simpa only [hhi] using h.2.2.2⟩

def meshPrimeBox {r : ℕ} (N cap : ℕ) (w Z : ℝ) (m : ℕ)
    (j : Grid r m) : Finset (List ℕ) :=
  actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) (List.ofFn j)

/-- The mesh alphabet is an actual original-prime box, not a symbolic
index attached after evaluating the arithmetic discrepancy. -/
theorem mesh_box_dictionary {r N cap m : ℕ} (hN : 1 < N) (w Z : ℝ)
    (j : Grid r m) (p : Fin r → ℕ) :
    List.ofFn p ∈ meshPrimeBox N cap w Z m j ↔
      (∀ i, p i ∈ roughPrimeFinset N cap w Z) ∧
        actualPrimeTupleLog N p ∈ cell (r := r) 0 1 m j := by
  exact fine_box_log_dictionary hN cap w Z
    (fun i : Fin (m + 1) => logPrimeMeshPoint 0 1 m i.val)
    (fun i : Fin (m + 1) => logPrimeMeshPoint 0 1 m (i.val + 1)) j p

/-- Every tuple of a certified inner fine box satisfies the literal
original upper gate, with order and strict faces preserved. -/
theorem inner_mesh_box_original_gates {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (p : Fin r → ℕ) (hp : List.ofFn p ∈ meshPrimeBox N cap w Z m j) :
    StrictAnti p ∧ ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell)
      (List.ofFn p).reverse := by
  have hbox := (mesh_box_dictionary hN w Z j p).mp hp
  have hregion := (roughRegion_dictionary ell _).mp ((Finset.mem_filter.mp hj).2 _ hbox.2)
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeFinset.mp (hbox.1 i)).2.1.pos
  have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hregion.2
  exact ⟨hanti, (original_upper_prefix_iff_log hN ell p hpos hanti).mpr hregion.1⟩

/-- Actual canonical retained rough primes lie in [0,1) at scale N.
The physical Z<=N guard is the real original upper ceiling. -/
theorem retained_canonical_unit_log_box {N cap d : ℕ} (hN : 1 < N)
    {w Z L : ℝ} (hZN : Z ≤ (N : ℝ))
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualPrimeTupleLog N (slotVector (canonicalSlots N cap w Z d)) ∈
      logPrimeBox (fun _ => 0) (fun _ => 1) := by
  apply mem_logPrimeBox.mpr
  intro i
  have hp := canonicalSlots_prime_data (N := N) (cap := cap) (d := d)
    (List.getElem_mem i.isLt)
  have hrough : slotVector (canonicalSlots N cap w Z d) i ∈ roughPrimeFinset N cap w Z := by
    rw [← roughPrimeUniverse_toFinset N cap w Z]
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.getElem_mem i.isLt)).1)
  have hfine : slotVector (canonicalSlots N cap w Z d) i ∈ finePrimeSet N cap w Z 0 1 := by
    apply Finset.mem_filter.mpr
    refine ⟨hrough, ?_, ?_⟩
    · simpa using (show (1 : ℝ) ≤ slotVector (canonicalSlots N cap w Z d) i from
        by exact_mod_cast hp.1.one_lt.le)
    · simpa using hp.2.2.2.trans_le hZN
  exact ((finePrimeSet_log_iff hN w Z 0 1).mp hfine).2

/-- No retained arithmetic point is lost: it has a literal fine-box
witness, and either that WHOLE cell is certified or its actual log point
is retained in a proper affine wall reserve. -/
theorem retained_actual_mesh_cell_or_wall {N cap d : ℕ} (hN : 1 < N)
    {w Z ell : ℝ} (hZN : Z ≤ (N : ℝ)) (hL : 1 < (N : ℝ) ^ ell)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z)
    (m : ℕ) :
    let ps := canonicalSlots N cap w Z d
    let v := actualPrimeTupleLog N (slotVector ps)
    ∃ j ∈ outerCells ps.length 0 1 ell m,
      ps ∈ meshPrimeBox N cap w Z m j ∧ v ∈ cell 0 1 m j ∧
        (j ∈ innerCells ps.length 0 1 ell m ∨ wallReserve ps.length 0 1 ell m v) := by
  let ps := canonicalSlots N cap w Z d
  let p := slotVector ps
  have hbox := retained_canonical_unit_log_box hN hZN hd
  have hpos : ∀ i : Fin ps.length, 0 < p i :=
    fun i => (canonicalSlots_prime_data (List.getElem_mem i.isLt)).1.pos
  have hanti : StrictAnti p := by
    apply List.pairwise_ofFn.mp
    rw [ofFn_slotVector]
    exact canonicalSlots_descending N cap w Z d
  have hv : actualPrimeTupleLog N p ∈ roughRegion ps.length ell :=
    (roughRegion_dictionary ell _).mpr ⟨retained_slots_log_region hN hL hd,
      (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hanti⟩
  obtain ⟨j, hj, hvj, hgood⟩ := actual_point_fine_cell_or_wall (by norm_num : (0 : ℝ) < 1) m hbox hv
  refine ⟨j, hj, ?_, hvj, hgood⟩
  have hrough : ∀ i, p i ∈ roughPrimeFinset N cap w Z := by
    intro i
    rw [← roughPrimeUniverse_toFinset N cap w Z]
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.getElem_mem i.isLt)).1)
  have hmem := (mesh_box_dictionary hN w Z j p).mpr ⟨hrough, hvj⟩
  simpa only [p, ofFn_slotVector] using hmem

/-- Every nonzero TRUE all16 common-beta coefficient supplies the
actual marked modulus and bounded-rank residual word for this mesh.  Both
cutoff and region guards come from its own physical compiler. -/
theorem actual_all16_sigma_mesh_or_wall {n N q : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (nu0 betaEta : ℝ)
    (hnu : 0 < nu0) (hb : 0 < betaEta)
    (hbudget : betaEta < OriginalCommonBetaActualParameters.epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop)
    (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2))
      ((N : ℝ) ^ (nu0 * betaEta)) E q ≠ 0) (m : ℕ) :
    ∃ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∃ e ∈ rowSmall n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) t,
        ∃ d ∈ rowRough n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) t,
          q = U1011OriginalSixteenArithmeticProducts.fullPrefix t * (e * d) ∧
          d.primeFactors.card ≤ OriginalPresievedRoughRank.rankBound nu0 betaEta ∧
          let ps := rowSlots n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) t d
          let ell := (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
            (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
            (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta : ℝ)
          let v := actualPrimeTupleLog N (slotVector ps)
          ∃ j ∈ outerCells ps.length 0 1 ell m,
            ps ∈ meshPrimeBox N
              (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              ((N : ℝ) ^ (nu0 * betaEta ^ 2))
              (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) m j ∧
              v ∈ cell 0 1 m j ∧
              (j ∈ innerCells ps.length 0 1 ell m ∨ wallReserve ps.length 0 1 ell m v) := by
  obtain ⟨t, ht, e, he, d, hd, hqed, hrank, hregion, hvalue⟩ :=
    actual_jointSigma_slot_affine_realization hN heta nu0 betaEta hnu hb hbudget E hq
  refine ⟨t, ht, e, he, d, hd, hqed, hrank, ?_⟩
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  exact retained_actual_mesh_cell_or_wall hN
    (all16_physical_Z_le_N (by omega) heta ht) hL hd m

/-- The common beta entry is one-bounded before the original per-label
denominator is introduced; no beta estimate is requested from callers. -/
theorem raw_beta_abs_le_one (N cap k : ℕ) (w B : ℝ) (e : ℕ) :
    |rawBetaWeight N cap k w B e| ≤ 1 := by
  unfold rawBetaWeight
  split_ifs
  · exact actualSmallRosserPlus_abs_le_one N cap w B e
  · exact actualSmallRosserMinus_abs_le_one N cap w B e

def meshMultiplicity {r m : ℕ} (j : Grid r m) : ℕ :=
  ∏ i ∈ (List.ofFn j).toFinset, ((List.ofFn j).count i).factorial

theorem meshMultiplicity_pos {r m : ℕ} (j : Grid r m) : 0 < meshMultiplicity j := by
  exact Finset.prod_pos (fun i hi => Nat.factorial_pos _)

/-- Literal original residual M_res: repeated fine labels are counted,
not replaced by a total-rank or marked-slot factorial. -/
def meshScalar {r m : ℕ} (N cap : ℕ) (w B : ℝ) (e : ℕ) (j : Grid r m) : ℝ :=
  rawBetaWeight N cap r w B e / (meshMultiplicity j : ℝ)

theorem meshScalar_abs_le_one {r m : ℕ} (N cap : ℕ) (w B : ℝ) (e : ℕ) (j : Grid r m) :
    |meshScalar N cap w B e j| ≤ 1 := by
  have hM : (0 : ℝ) < meshMultiplicity j := by exact_mod_cast meshMultiplicity_pos j
  have hM1 : (1 : ℝ) ≤ meshMultiplicity j := by exact_mod_cast meshMultiplicity_pos j
  rw [meshScalar, abs_div, abs_of_pos hM]
  exact (div_le_one hM).mpr ((raw_beta_abs_le_one N cap r w B e).trans hM1)

/-- Fixed residual fine-cell scalar budget. It depends on rank and mesh,
not on N, the marked prefix, beta level, small e or arithmetic tests. -/
theorem residual_inner_cell_scalar_mass (r m N cap : ℕ) (w B ell : ℝ) (e : ℕ) :
    (∑ j ∈ innerCells r 0 1 ell m, |meshScalar N cap w B e j|) ≤
      ((m + 1 : ℕ) ^ r : ℝ) := by
  calc
    _ ≤ ∑ _j ∈ innerCells r 0 1 ell m, (1 : ℝ) :=
      Finset.sum_le_sum (fun j hj => meshScalar_abs_le_one N cap w B e j)
    _ = ((innerCells r 0 1 ell m).card : ℝ) := by simp
    _ ≤ (Fintype.card (Grid r m) : ℝ) := by
      exact_mod_cast Finset.card_le_univ (innerCells r 0 1 ell m)
    _ = _ := by simp [Grid, Fintype.card_fun]

theorem residual_all_rank_scalar_mass (R m N cap : ℕ) (w B ell : ℝ) (e : ℕ) :
    (∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
      |meshScalar N cap w B e j|) ≤
      ∑ r ∈ Finset.range (R + 1), ((m + 1 : ℕ) ^ r : ℝ) := by
  exact Finset.sum_le_sum (fun r hr => residual_inner_cell_scalar_mass r m N cap w B ell e)

/-- Original frozen selected-pair assignment, computed once from the
whole fine endpoint word. Low ranks remain in one group for the separate
low-rank route; no high-rank analytic capacity claim is made for them. -/
def computedGroups {ι : Type*} (D A : ℝ) (yz : Bool) (upper : ι → ℕ)
    (input : List ι) : List ι × List ι × List ι :=
  match input with
  | a :: b :: c :: tail => actualFrozenSelectedPairSlots D A yz upper ![a, b, c] tail
  | input => (input, [], [])

theorem computedGroups_partition {ι : Type*} (D A : ℝ) (yz : Bool)
    (upper : ι → ℕ) (input : List ι) :
    let out := computedGroups D A yz upper input
    (out.1 ++ out.2.1 ++ out.2.2).Perm input := by
  cases input with
  | nil => simp [computedGroups]
  | cons a input =>
    cases input with
    | nil => simp [computedGroups]
    | cons b input =>
      cases input with
      | nil => simp [computedGroups]
      | cons c tail =>
        exact actualFrozenSelectedPairSlots_perm D A yz upper ![a, b, c] tail

def meshUpper (N m : ℕ) (i : Fin (m + 1)) : ℕ :=
  Nat.floor ((N : ℝ) ^ logPrimeMeshPoint 0 1 m (i.val + 1))

theorem mesh_prime_le_upper {N cap m : ℕ} {w Z : ℝ} {i : Fin (m + 1)} {p : ℕ}
    (hp : p ∈ meshPrimeAlphabet N cap w Z m i) : p ≤ meshUpper N m i :=
  Nat.le_floor (Finset.mem_filter.mp hp).2.2.le

/-- Literal group product support for EVERY tuple in each of the
computed whole boxes, using the same original fine upper endpoints. -/
theorem computed_mesh_group_product_bounds {r N cap m : ℕ} (w Z : ℝ)
    (j : Grid r m) (D A : ℝ) (yz : Bool) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (∀ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.1,
      ps.prod ≤ (out.1.map (meshUpper N m)).prod) ∧
    (∀ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.1,
      ps.prod ≤ (out.2.1.map (meshUpper N m)).prod) ∧
    (∀ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.2,
      ps.prod ≤ (out.2.2.map (meshUpper N m)).prod) := by
  have hbound (input : List (Fin (m + 1))) :
      ∀ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) input,
        ps.prod ≤ (input.map (meshUpper N m)).prod :=
    actualPrimeSlotBox_prod_le_upper (meshPrimeAlphabet N cap w Z m) (meshUpper N m)
      input (fun i hi p hp => mesh_prime_le_upper hp)
  exact ⟨hbound _, hbound _, hbound _⟩

/-- Exact raw Cartesian regrouping on the computed occurrence lists.
The original mesh scalar stays outside the entire signed atom once.
Groupwise per-label gamma normalization and capacity licences are still
separate from this finite partition identity. -/
theorem computed_mesh_atom_three_group_sum {r N cap m : ℕ} (w Z B : ℝ) (e : ℕ)
    (j : Grid r m) (D A : ℝ) (yz : Bool) (H : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (meshScalar N cap w B e j) *
      (∑ ps ∈ meshPrimeBox N cap w Z m j, H ps.prod) =
      (meshScalar N cap w B e j) *
        ∑ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.1,
          ∑ qs ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.1,
            ∑ rs ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.2,
              H (ps.prod * qs.prod * rs.prod) := by
  dsimp only
  congr 1
  have hp := computedGroups_partition D A yz (meshUpper N m) (List.ofFn j)
  rw [actualPrimeSlotBox_product_sum_perm (meshPrimeAlphabet N cap w Z m) hp.symm H,
    actualPrimeSlotBox_product_sum_append]
  apply Finset.sum_congr rfl
  intro ps hps
  rw [actualPrimeSlotBox_product_sum_append]
  apply Finset.sum_congr rfl
  intro qs hqs
  apply Finset.sum_congr rfl
  intro rs hrs
  simp only [mul_assoc]

end
end ImbalancedChen.P5Z.All16FineMeshGateScalar
