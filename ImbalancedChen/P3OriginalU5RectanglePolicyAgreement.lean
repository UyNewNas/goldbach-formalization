import ImbalancedChen.P3OriginalU5CommonPhysicalRoot
import ImbalancedChen.P3OriginalU5RoundedPlateauFamily
import ImbalancedChen.P3OriginalU5NormalizedDensityReserve
import ImbalancedChen.P3OriginalU5RoundedPairDensity
import ImbalancedChen.P3OriginalU5SelectedDensityLower

/-! Every external owner meeting the positive U5 rectangle lies inside
the original constant plateau when the mesh width is at most 1/32000.
The common physical policy and the original policy therefore agree on
all histories of those rows, including all inputs to finite rounding. -/

namespace ImbalancedChen.P3OriginalU5RectanglePolicyAgreement

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P2GammaU5PlateauGeometry (rectangle rectangle_coordinates rectangle_subset_pairSupport
  plateauLevel boxLo boxHi)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairRootRoughProducer (pairPolicy)
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalSelectedPairNativeData (rootSeed selectedPolicy)
open P3OriginalU5CoarseRootV (meshStep ownedCell ownedCell_subset_closedCell
  closedCell_coordinate_error exists_auxiliary_mesh)
open P3OriginalU5CommonPhysicalRoot (physicalSeed rowOwner rowOwner_mem policy)
open P3OriginalU5FullWLayer (level_eq_wLevel_iff)
open P3OriginalU5NormalizedDensityReserve (exists_rounded_U5_normalized_density_reserve)
open P3OriginalU5RoundedCountInsertion (roundedRho roundedSupport rowSignedPrimitive)
open P3OriginalU5RoundedPairDensity (roundedRho_fullModulus_density_eq)
open P3OriginalU5RoundedPlateauFamily (rectangle_harmonic_limit)
open P3OriginalU5SelectedDensityLower (exists_original_U5_selected_row_lower)
open P5OriginalU5CausalFinite (coordinates coordinates_mem_triangle pairSupport)
open P5OriginalU5PlateauPrimeBV (fullModulus)
open Part5OriginalUpsilon5CausalDictionary (level mem_triangle)

/-- Every point in the same cell stays on the plateau, including cells
that meet a boundary of the chosen rectangle. -/
theorem level_on_rectangle_owner (R : PairRange) {m : ℕ} (hm : meshStep R m ≤ 1/32000)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ rectangle N)
    {y : Fin 2 → ℝ} (hy : y ∈ ownedCell R m (rowOwner R m hN (rectangle_subset_pairSupport hN ht)).val) :
    level (y 0) (y 1) = plateauLevel := by
  have hx := rowOwner_mem R m hN (rectangle_subset_pairSupport hN ht)
  have hc := ownedCell_subset_closedCell R m _ hx
  have hcy := ownedCell_subset_closedCell R m _ hy
  have h0 := abs_le.mp (closedCell_coordinate_error R hcy hc 0)
  have h1 := abs_le.mp (closedCell_coordinate_error R hcy hc 1)
  have hu := rectangle_coordinates hN ht 0
  have hv := rectangle_coordinates hN ht 1
  simp only [boxLo, boxHi, Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
  obtain ⟨ha, hlt, hh⟩ := mem_triangle.mp hy.1
  apply (level_eq_wLevel_iff ha hlt hh).mpr
  exact ⟨by linarith only [h1.2, hv.2, hm],
    by linarith only [h0.1, h1.1, hu.1, hv.1, hm]⟩

/-- The infimum defining the physical level and the native seed both
equal the same constant after subtracting their original two buffers. -/
theorem rectangle_seed_equalities (R : PairRange) {m : ℕ} (hm : meshStep R m ≤ 1/32000)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ rectangle N) :
    let s := physicalSeed R b (rowOwner R m hN (rectangle_subset_pairSupport hN ht))
    s = plateauLevel - 2 * (b : ℝ) ∧ s = rootSeed false b N t := by
  let j := rowOwner R m hN (rectangle_subset_pairSupport hN ht)
  let E := (fun y : Fin 2 → ℝ => level (y 0) (y 1)) '' ownedCell R m j.val
  have hx := rowOwner_mem R m hN (rectangle_subset_pairSupport hN ht)
  have hv := level_on_rectangle_owner R hm hN ht hx
  have hp : plateauLevel ∈ E := ⟨coordinates N t, hx, hv⟩
  have hl (v : ℝ) (h : v ∈ E) : plateauLevel ≤ v := by
    obtain ⟨y, hy, rfl⟩ := h
    exact (level_on_rectangle_owner R hm hN ht hy).ge
  have he : sInf E = plateauLevel :=
    le_antisymm (csInf_le ⟨_, hl⟩ hp) (le_csInf ⟨_, hp⟩ hl)
  have hseed : physicalSeed R b j = plateauLevel - 2 * (b : ℝ) :=
    congrArg (fun v => v - 2 * (b : ℝ)) he
  have hnative : rootSeed false b N t = plateauLevel - 2 * (b : ℝ) := by
    change level (coordinates N t 0) (coordinates N t 1) - 2 * (b : ℝ) = _
    rw [hv]
  exact ⟨hseed, hseed.trans hnative.symm⟩

/-- The equality is between entire prefix functions, before deciding
whether any individual word is admitted. -/
theorem rectangle_policy_eq (R : PairRange) {m : ℕ} (hm : meshStep R m ≤ 1/32000)
    {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ rectangle N) :
    policy R bank b m N t = selectedPolicy R bank b false N t := by
  have hs := (rectangle_seed_equalities R hm b hN ht).2
  rw [policy, dif_pos (coordinates_mem_triangle hN (rectangle_subset_pairSupport hN ht))]
  exact congrArg (fun s => pairPolicy (pairPlan R bank (2 * b) s)
    (R.epsilon : ℝ) (ceiling : ℝ) s N t) hs

/-- The physical grid is fixed before the target, candidate bank and all
prime labels. -/
theorem exists_rectangle_agreement_mesh (R : PairRange) :
    ∃ m : ℕ, meshStep R m ≤ 1/32000 ∧
      ∀ {N : ℕ}, 2 ≤ N → ∀ t ∈ rectangle N, ∀ {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ),
        policy R bank b m N t = selectedPolicy R bank b false N t := by
  obtain ⟨m, hm⟩ := exists_auxiliary_mesh R (by norm_num : (0 : ℝ) < 1/1000)
  have hf : meshStep R m ≤ 1/32000 := by linarith only [hm]
  refine ⟨m, hf, ?_⟩
  intro N hN t ht mesh bank b
  exact rectangle_policy_eq R hf bank b hN ht

/-- The identical complete rounded coefficient supplies the exact signed
primitive discrepancy on the rectangle for every rounding choice. -/
theorem rectangle_rounded_rows_eq (R : PairRange) {m : ℕ} (hm : meshStep R m ≤ 1/32000)
    {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ rectangle N) (epsilon tau : ℝ) :
    roundedRho N epsilon tau (policy R bank b m N t) =
        roundedRho N epsilon tau (selectedPolicy R bank b false N t) ∧
      rowSignedPrimitive N epsilon tau (policy R bank b m N t) t =
        rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t := by
  have he := rectangle_policy_eq R hm bank b hN ht
  exact ⟨congrArg (roundedRho N epsilon tau) he,
    congrArg (fun p => rowSignedPrimitive N epsilon tau p t) he⟩

/-- The original full signed sum with the common-root policies inserted
on precisely the positive rectangle. The complementary rows keep every
one of their original signs and moduli. -/
theorem signed_rounded_rectangle_partition (R : PairRange) {m : ℕ} (hm : meshStep R m ≤ 1/32000)
    {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ) :
    (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t) =
      (∑ t ∈ rectangle N, rowSignedPrimitive N epsilon tau (policy R bank b m N t) t) +
        ∑ t ∈ pairSupport N \ rectangle N,
          rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t := by
  let F (t : ℕ × ℕ) := rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t
  calc
    _ = (∑ t ∈ rectangle N, F t) + ∑ t ∈ pairSupport N \ rectangle N, F t := by
      rw [add_comm]
      exact (Finset.sum_sdiff (f := F) (rectangle_subset_pairSupport hN)).symm
    _ = _ := by
      apply congrArg (fun x => x + ∑ t ∈ pairSupport N \ rectangle N, F t)
      exact Finset.sum_congr rfl (fun t ht => (rectangle_rounded_rows_eq R hm bank b hN ht epsilon tau).2.symm)

/-- Positive signed density on this common-level rectangle itself. Half the
row lower constant pays the rounding reserve and half the limiting pair
mass pays the passage to finite targets. Both physical policies use the
same rounded coefficient and modulus bound on every row of this family. -/
theorem exists_rectangle_positive_rounded_density (R : PairRange) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, meshStep R m ≤ 1/32000 →
      ∀ (mesh : ℕ) (epsilonMax : ℝ), 0 < epsilonMax →
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧ epsilon < 1/272 ∧
        ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
          ∀ tau : ℝ, 0 < tau → tau ≤ tau0 → ∀ N ≥ N0, Even N → ∀ bank : CandidateBank mesh,
            c * singularSeries N / Real.log (N : ℝ) ≤
              (∑ t ∈ rectangle N, ∑ k ∈ roundedSupport N epsilon,
                roundedRho N epsilon tau (policy R bank (1/1000) m N t) k /
                  (Nat.totient (fullModulus t k) : ℝ)) ∧
            ∀ t ∈ rectangle N,
              roundedRho N epsilon tau (policy R bank (1/1000) m N t) =
                roundedRho N epsilon tau (selectedPolicy R bank (1/1000) false N t) ∧
              ∀ k : ℕ, roundedRho N epsilon tau (policy R bank (1/1000) m N t) k ≠ 0 →
                (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  obtain ⟨c, hc, Ns, hNs, hselected⟩ := exists_original_U5_selected_row_lower R
  let M := Real.log (11/10 : ℝ) * Real.log (13/12 : ℝ)
  have hM : 0 < M := rectangle_harmonic_limit.1
  have hev : ∀ᶠ N : ℕ in atTop, M/2 < ∑ t ∈ rectangle N, 1 / (Nat.totient (t.1 * t.2) : ℝ) :=
    rectangle_harmonic_limit.2.eventually (lt_mem_nhds (show M/2 < M by linarith only [hM]))
  obtain ⟨Nm, hmass⟩ := eventually_atTop.mp hev
  refine ⟨(c/2) * (M/2), mul_pos (half_pos hc) (half_pos hM), ?_⟩
  intro m hm mesh epsilonMax hmax
  obtain ⟨epsilon, he, he8, heMax, he272, tau0, htau0, Nr, _, hrounded⟩ :=
    exists_rounded_U5_normalized_density_reserve mesh (c/2) epsilonMax (half_pos hc) hmax
  refine ⟨epsilon, he, he8, heMax, he272, tau0, htau0, max Ns (max Nm Nr),
    hNs.trans (le_max_left _ _), ?_⟩
  intro tau htau hsmall N hN hEven bank
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hmN : Nm ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hrN : Nr ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 := hNs.trans hsN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let A := c/2 * singularSeries N / Real.log (N : ℝ)
  have hA : 0 ≤ A := (div_pos (mul_pos (half_pos hc) (singularSeries_pos N)) (Real.log_pos hNr)).le
  refine ⟨?_, ?_⟩
  · calc
      _ = A * (M/2) := by dsimp only [A]; ring
      _ ≤ A * (∑ t ∈ rectangle N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmass N hmN).le hA
      _ = ∑ t ∈ rectangle N, A / (Nat.totient (t.1 * t.2) : ℝ) := by
        simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        have hp := rectangle_subset_pairSupport hN2 ht
        have hs := hselected N hsN hEven bank (1/1000) (by norm_num) le_rfl t hp
        have hr := (hrounded N hrN hEven R bank t hp tau htau hsmall).1
        rw [rectangle_policy_eq R hm bank (1/1000) hN2 ht,
          roundedRho_fullModulus_density_eq hN2 he he8 hp tau (selectedPolicy R bank (1/1000) false N t)]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        calc
          A = c * singularSeries N / Real.log (N : ℝ) - c/2 * singularSeries N / Real.log (N : ℝ) := by
            dsimp only [A]
            ring
          _ ≤ _ := (sub_le_sub_right hs _).trans hr
  · intro t ht
    have hp := rectangle_subset_pairSupport hN2 ht
    have heq := (rectangle_rounded_rows_eq R hm bank (1/1000) hN2 ht epsilon tau).1
    refine ⟨heq, ?_⟩
    rw [heq]
    exact (hrounded N hrN hEven R bank t hp tau htau hsmall).2

end
end ImbalancedChen.P3OriginalU5RectanglePolicyAgreement
