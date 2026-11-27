import ImbalancedChen.P3OriginalU5FullWLayer
import ImbalancedChen.P3OriginalU5OrdinaryRootDensity
import ImbalancedChen.P3OriginalU5RoundedCountInsertion
import Batteries.Tactic.OpenPrivate

/-! The original rounded rows at the constant plateau level. Both signed
partition identities retain the full original complementary rows. An interior
marked-prime rectangle has a common buffered physical root, positive harmonic
mass, and explicit residual and prime-ceiling margins. -/

namespace ImbalancedChen.P3OriginalU5RoundedPlateauFamily

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2GammaU5PlateauGeometry (plateauLevel plateauLevel_exact rectangle boxLo boxHi
  rectangle_coordinates rectangle_subset_pairSupport original_level_on_box)
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (rootLevel rootSeed selectedPolicy)
open P3OriginalU5FullWLayer (wLayer wLayer_eq_marks native_policy_on_wLayer)
open P3OriginalU5OrdinaryRootDensity (ordinaryRootDensity)
open P3OriginalU5RoundedCountInsertion (roundedRho roundedSupport rowSignedPrimitive)
open P5OriginalU5CausalFinite (pairSupport cutoff coordinates)
open P5OriginalU5NativeRootCover (marks policyAt)
open P5OriginalU5PlateauPrimeBV (fullModulus)

open private rectangle_reciprocal_mass from ImbalancedChen.P3OriginalU5OrdinaryRootDensity

private theorem sum_rows_partition (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (f : (ℕ × ℕ) → (List ℕ → Bool) → ℝ) :
    (∑ t ∈ pairSupport N, f t (selectedPolicy R bank b false N t)) =
      (∑ t ∈ wLayer N, f t (policyAt R bank b plateauLevel N t)) +
        ∑ t ∈ pairSupport N \ wLayer N, f t (selectedPolicy R bank b false N t) := by
  let row (t : ℕ × ℕ) := f t (selectedPolicy R bank b false N t)
  have hsub : wLayer N ⊆ pairSupport N := Finset.filter_subset _ _
  calc
    _ = (∑ t ∈ wLayer N, row t) + ∑ t ∈ pairSupport N \ wLayer N, row t := by
      rw [add_comm]
      exact (Finset.sum_sdiff (f := row) hsub).symm
    _ = _ := by
      apply congrArg (fun x => x + ∑ t ∈ pairSupport N \ wLayer N, row t)
      exact Finset.sum_congr rfl (fun t ht => congrArg (f t) (native_policy_on_wLayer R bank b hN ht))

/-- This is the signed primitive term of the actual rounded count reserve. -/
theorem rounded_primitive_wLayer_partition (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ) :
    (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t) =
      (∑ t ∈ wLayer N, rowSignedPrimitive N epsilon tau (policyAt R bank b plateauLevel N t) t) +
        ∑ t ∈ pairSupport N \ wLayer N,
          rowSignedPrimitive N epsilon tau (selectedPolicy R bank b false N t) t :=
  sum_rows_partition R bank b hN (fun t p => rowSignedPrimitive N epsilon tau p t)

/-- The density uses the same rounded rows, signs, full moduli and partition. -/
theorem rounded_density_wLayer_partition (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ) :
    (∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
      roundedRho N epsilon tau (selectedPolicy R bank b false N t) k / (Nat.totient (fullModulus t k) : ℝ)) =
      (∑ t ∈ wLayer N, ∑ k ∈ roundedSupport N epsilon,
        roundedRho N epsilon tau (policyAt R bank b plateauLevel N t) k / (Nat.totient (fullModulus t k) : ℝ)) +
        ∑ t ∈ pairSupport N \ wLayer N, ∑ k ∈ roundedSupport N epsilon,
          roundedRho N epsilon tau (selectedPolicy R bank b false N t) k / (Nat.totient (fullModulus t k) : ℝ) :=
  sum_rows_partition R bank b hN (fun t p => ∑ k ∈ roundedSupport N epsilon,
    roundedRho N epsilon tau p k / (Nat.totient (fullModulus t k) : ℝ))

/-- Physical exponent of the actual ordinary root with buffer 1/1000. -/
def bufferedLevel : ℝ := plateauLevel - 2 * (1 / 1000 : ℝ)

theorem bufferedLevel_exact : bufferedLevel = 90301 / 160000 := by
  norm_num [bufferedLevel, plateauLevel_exact]

def markedExponent (N : ℕ) (t : ℕ × ℕ) : ℝ := coordinate N t.1 + coordinate N t.2

def residual (N : ℕ) (t : ℕ × ℕ) : ℝ := bufferedLevel - markedExponent N t

/-- A positive rectangle of the original selector, with a common physical
level. Its residual denominator contains both marks and its ordinary cutoff
is strictly below the smaller marked prime. -/
structure RectangleRoot (N : ℕ) (t : ℕ × ℕ) : Prop where
  mem_layer : t ∈ wLayer N
  seed_eq : rootSeed false (1 / 1000) N t = bufferedLevel
  residual_power : (N : ℝ) ^ residual N t = (N : ℝ) ^ bufferedLevel / ((t.1 * t.2 : ℕ) : ℝ)
  ordinary_density : ordinaryRootDensity (1 / 1000) N t =
    actualSmallRosserMinusDensity N (Nat.ceil (cutoff N)) (cutoff N)
      ((N : ℝ) ^ bufferedLevel / ((t.1 * t.2 : ℕ) : ℝ))
  residual_lower : 51901 / 160000 < residual N t
  residual_upper : residual N t ≤ 55101 / 160000
  ratio_range : 3 < residual N t / (417 / 5000) ∧ residual N t / (417 / 5000) < 5
  alpha_lower : 9 / 4 < (1 - markedExponent N t) / residual N t
  mark_floor : 1 / 10 ≤ coordinate N t.1
  cutoff_lt_mark : cutoff N < (t.1 : ℝ)

theorem original_U5_rectangle_root {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ rectangle N) :
    RectangleRoot N t := by
  have hpair := rectangle_subset_pairSupport hN ht
  have hu := rectangle_coordinates hN ht 0
  have hv := rectangle_coordinates hN ht 1
  simp only [boxLo, boxHi, Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
  have hlevel : rootLevel false N t = plateauLevel :=
    original_level_on_box hu.1 hu.2.le hv.1 hv.2.le
  have hseed : rootSeed false (1 / 1000) N t = bufferedLevel := by
    norm_num [rootSeed, hlevel, bufferedLevel]
  have hW : t ∈ wLayer N := by
    rw [wLayer_eq_marks hN]
    exact Finset.mem_filter.mpr ⟨hpair, hlevel⟩
  change 1 / 10 ≤ coordinate N t.1 ∧ coordinate N t.1 < 11 / 100 at hu
  change 3 / 25 ≤ coordinate N t.2 ∧ coordinate N t.2 < 13 / 100 at hv
  have hS : 22 / 100 ≤ markedExponent N t ∧ markedExponent N t < 24 / 100 := by
    unfold markedExponent
    constructor <;> linarith only [hu.1, hu.2, hv.1, hv.2]
  have hL : 51901 / 160000 < residual N t ∧ residual N t ≤ 55101 / 160000 := by
    rw [residual, bufferedLevel_exact]
    constructor <;> linarith only [hS.1, hS.2]
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hpr, _, _, _⟩ := Finset.mem_filter.mp hpair
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpr
  have hp' := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq' := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  refine ⟨hW, hseed, ?_, ?_, hL.1, hL.2, ?_, ?_, hu.1, ?_⟩
  · rw [residual, Real.rpow_sub (zero_lt_one.trans hNr), markedExponent,
      Real.rpow_add (zero_lt_one.trans hNr), hp', hq', Nat.cast_mul]
  · rw [ordinaryRootDensity, hseed, Nat.cast_mul]
  · have ha : (0 : ℝ) < 417 / 5000 := by norm_num
    exact ⟨(lt_div_iff₀ ha).mpr (by linarith only [hL.1]),
      (div_lt_iff₀ ha).mpr (by linarith only [hL.2])⟩
  · apply (lt_div_iff₀ ((by norm_num : (0 : ℝ) < 51901 / 160000).trans hL.1)).mpr
    rw [residual, bufferedLevel_exact]
    linarith only [hS.1]
  · change (N : ℝ) ^ (417 / 5000 : ℝ) < (t.1 : ℝ)
    rw [← hp']
    exact Real.rpow_lt_rpow_of_exponent_lt hNr ((by norm_num : (417/5000 : ℝ) < 1/10).trans_le hu.1)

/-- The mass is the actual full-pair reciprocal totient, with both target
deletions; its explicit limiting mass is positive. -/
theorem rectangle_harmonic_limit :
    let m := Real.log (11/10 : ℝ) * Real.log (13/12 : ℝ)
    0 < m ∧ Tendsto (fun N : ℕ => ∑ t ∈ rectangle N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) atTop (𝓝 m) := by
  dsimp only
  refine ⟨mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num)), ?_⟩
  have hl (i : Fin 2) : 0 < boxLo i := by fin_cases i <;> norm_num [boxLo]
  have hlt (i : Fin 2) : boxLo i < boxHi i := by fin_cases i <;> norm_num [boxLo, boxHi]
  have h := tendsto_actualPrimeBoxMass boxLo boxHi hl hlt
  have hm : (∏ i : Fin 2, Real.log (boxHi i / boxLo i)) =
      Real.log (11/10 : ℝ) * Real.log (13/12 : ℝ) := by
    norm_num [Fin.prod_univ_two, boxHi, boxLo]
  rw [hm] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (rectangle_reciprocal_mass hN).symm

end
end ImbalancedChen.P3OriginalU5RoundedPlateauFamily
