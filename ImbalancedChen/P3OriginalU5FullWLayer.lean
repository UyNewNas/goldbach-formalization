import ImbalancedChen.P2OriginalU5PlateauRectangle
import ImbalancedChen.P5OriginalU5NativeRootCover

/-!
# The complete constant-level layer of the original U5 selector

The larger coordinate has a closed upper bound and the sum of the two
coordinates has a closed lower bound. These two gates describe exactly the
original marks at the plateau level, including both boundary lines.
-/

namespace ImbalancedChen.P3OriginalU5FullWLayer

noncomputable section
open Classical
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary (a h level mem_triangle)
open VariableEnvelope (A C v)
open P2GammaU5PlateauGeometry (plateauLevel plateauLevel_exact)
open P5OriginalU5CausalFinite
  (pairSupport coordinates coordinates_mem_triangle signedPrimitiveSum rowSignedPrimitive support rho)
open P5OriginalU5NativeRootCover
  (levels marks policyAt native_policy_at actual_root_gates signed_native_cover)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P2OriginalU5SmallPartnerRootPayment (rootQ)
open P2OriginalSelectedIntegerPrefixSquares (IntegerSquareGates selectedPrimes remainingPrimes)

/-- On the original triangle, these two weak inequalities characterize the
entire level B(a) = 90621/160000. -/
theorem level_eq_wLevel_iff {u t : ℝ} (hu : a ≤ u) (hut : u < t) (ht : t < h) :
    level u t = plateauLevel ↔ t ≤ 10621 / 80000 ∧ 17293 / 80000 ≤ t + u := by
  have htmu : t ≤ VariableEnvelope.mu :=
    ht.le.trans (by norm_num [h, VariableEnvelope.mu])
  have habove : plateauLevel < A (t + u) := by
    rw [plateauLevel_exact]
    unfold A
    unfold a at hu
    linarith only [hu, hut]
  have hlarge : A t ≤ plateauLevel ↔ t ≤ 10621 / 80000 := by
    rw [plateauLevel_exact]
    unfold A
    constructor <;> intro hb <;> linarith only [hb]
  have hsum : C (t + u) ≤ plateauLevel ↔ 17293 / 80000 ≤ t + u := by
    rw [plateauLevel_exact]
    unfold C
    constructor <;> intro hb <;> linarith only [hb]
  change max (v t) (max (v (t + u)) plateauLevel) = plateauLevel ↔ _
  rw [VariableEnvelope.v_eq_A htmu, VariableEnvelope.v_eq_min (t + u)]
  constructor
  · intro heq
    have hbounds := max_le_iff.mp heq.le
    have hmin := (max_le_iff.mp hbounds.2).1
    exact ⟨hlarge.mp hbounds.1, hsum.mp ((min_le_iff.mp hmin).resolve_left habove.not_ge)⟩
  · rintro ⟨htop, hbottom⟩
    have hmin := (min_le_right (A (t + u)) (C (t + u))).trans (hsum.mpr hbottom)
    rw [max_eq_right hmin, max_eq_right (hlarge.mpr htop)]

/-- The two coordinate gates are applied to the original target-dependent
pair support. -/
def wLayer (N : ℕ) : Finset (ℕ × ℕ) :=
  (pairSupport N).filter fun p =>
    coordinates N p 1 ≤ 10621 / 80000 ∧
      17293 / 80000 ≤ coordinates N p 1 + coordinates N p 0

theorem wLayer_eq_marks {N : ℕ} (hN : 2 ≤ N) : wLayer N = marks N plateauLevel := by
  apply Finset.ext
  intro p
  simp only [wLayer, marks, Finset.mem_filter]
  apply and_congr_right
  intro hp
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp (coordinates_mem_triangle hN hp)
  exact (level_eq_wLevel_iff hu hut ht).symm

theorem mem_sdiff_wLayer_iff (N : ℕ) (p : ℕ × ℕ) :
    p ∈ pairSupport N \ wLayer N ↔
      p ∈ pairSupport N ∧
        (10621 / 80000 < coordinates N p 1 ∨
          coordinates N p 1 + coordinates N p 0 < 17293 / 80000) := by
  simp only [Finset.mem_sdiff, wLayer, Finset.mem_filter]
  apply and_congr_right
  intro hp
  simp only [hp, true_and, not_and_or, not_le]

theorem native_policy_on_wLayer (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {p : ℕ × ℕ} (hp : p ∈ wLayer N) :
    selectedPolicy R bank b false N p = policyAt R bank b plateauLevel N p := by
  rw [wLayer_eq_marks hN] at hp
  exact native_policy_at R bank b hp

theorem actual_root_gates_on_wLayer {N : ℕ} (hN : 2 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ wLayer N) {b : ℚ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 1000) :
    let slots := [(p.2, true), (p.1, true)]
    rootQ N p = (N : ℝ) ^ plateauLevel ∧
    IntegerSquareGates N (plateauLevel - 2 * (b : ℝ)) 1 (slots.map Prod.fst) ∧
    IntegerSquareGates N (plateauLevel - 2 * (b : ℝ))
      (selectedPrimes slots).prod (remainingPrimes slots) := by
  rw [wLayer_eq_marks hN] at hp
  exact actual_root_gates hN hp hb hb'

/-- Split the original signed sum, substituting the fixed-level policy only
on its exact layer. The complementary rows retain their original policies. -/
theorem signedPrimitiveSum_wLayer_partition (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (e : ℝ) :
    signedPrimitiveSum N e (selectedPolicy R bank b false N) =
      (∑ p ∈ wLayer N, rowSignedPrimitive N e (policyAt R bank b plateauLevel N p) p) +
      ∑ p ∈ pairSupport N \ wLayer N, rowSignedPrimitive N e (selectedPolicy R bank b false N p) p := by
  let row (p : ℕ × ℕ) := rowSignedPrimitive N e (selectedPolicy R bank b false N p) p
  have hsub : wLayer N ⊆ pairSupport N := Finset.filter_subset _ _
  calc
    _ = (∑ p ∈ wLayer N, row p) + ∑ p ∈ pairSupport N \ wLayer N, row p := by
      rw [add_comm]
      exact (Finset.sum_sdiff (f := row) hsub).symm
    _ = _ := by
      apply congrArg (fun x => x + ∑ p ∈ pairSupport N \ wLayer N, row p)
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg (fun keep => rowSignedPrimitive N e keep p) (native_policy_on_wLayer R bank b hN hp)

/-- The same partition applies to the existing level cover with its original
nonzero-coefficient filter and full physical modulus. -/
theorem signed_native_cover_wLayer_partition (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) (e : ℝ) :
    (∑ v ∈ levels N, ∑ p ∈ marks N v,
      ∑ k ∈ (support N e (policyAt R bank b v N p)).filter
          (fun k => rho N e (policyAt R bank b v N p) k ≠ 0),
        rho N e (policyAt R bank b v N p) k *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((p.1 * p.2) * k)) =
      (∑ p ∈ wLayer N, rowSignedPrimitive N e (policyAt R bank b plateauLevel N p) p) +
      ∑ p ∈ pairSupport N \ wLayer N, rowSignedPrimitive N e (selectedPolicy R bank b false N p) p :=
  (signed_native_cover R bank b N e).symm.trans (signedPrimitiveSum_wLayer_partition R bank b hN e)

end
end ImbalancedChen.P3OriginalU5FullWLayer
