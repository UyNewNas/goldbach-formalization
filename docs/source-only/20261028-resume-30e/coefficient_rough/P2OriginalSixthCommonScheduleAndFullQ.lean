import ImbalancedChen.P2OriginalSixthOmittedArithmeticMass
import ImbalancedChen.P5OriginalCommonRefinedPreservation
import ImbalancedChen.ActualSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One finite compact choice covers all eleven original cells.  Original
compact prime words remain in the ACTUAL common-refined final support by
the independently constructed approval-containment theorem.  Their full
small/rough coefficient is the original signed beta attachment at exactly
q=e*P, with no identification of the old and refined fifth parent.

The omitted reciprocal-totient test bound is uniform in every physical
rho and small factor.  It does NOT sum absolute small factors for free,
nor does it bound an unbounded count-minus-coprime-mean test.  It also
does not assert that every retained word passes the new sixth eligibility
guard against the actual refined fifth parent.
-/

namespace ImbalancedChen.P2OriginalSixthCommonScheduleAndFullQ

noncomputable section
open Classical Filter Set
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthSourceCompactCores P2OriginalSixthSourceLossConvergence
open P2OriginalSixthCompactArithmeticFibre P2OriginalSixthOmittedArithmeticMass
open P2CompactThirdHistorySelection
open P2OriginalFourthCapProducerInterface P1OriginalVariableFifthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1ActualMovingAffineWallMass

local instance : Fintype Cell :=
  ⟨allCells.toFinset,fun c => List.mem_toFinset.mpr (allCells_complete c)⟩

def commonCore (n : ℕ) : Set Physical := ⋃ c : Cell, coreSequence c n

theorem core_subset_common (c : Cell) (n : ℕ) : coreSequence c n ⊆ commonCore n :=
  subset_iUnion (fun c : Cell => coreSequence c n) c

theorem isCompact_commonCore (n : ℕ) : IsCompact (commonCore n) :=
  isCompact_iUnion (fun c : Cell => isCompact_compactCore c _)

theorem exists_commonChoice (n : ℕ) : Nonempty (CompactThirdChoice (commonCore n)) := by
  apply exists_compactThirdChoice _ (isCompact_commonCore n)
  intro t ht
  obtain ⟨c,hc⟩ := mem_iUnion.mp ht
  exact ⟨c,coreSequence_subset_sourceRegion c n hc⟩

def restrictChoice {n : ℕ} (D : CompactThirdChoice (commonCore n)) (c : Cell) :
    CompactThirdChoice (coreSequence c n) where
  e := D.e
  chi := D.chi
  mesh := D.mesh
  roughFloor := D.roughFloor
  e_pos := D.e_pos
  e_small := D.e_small
  chi_pos := D.chi_pos
  chi_small := D.chi_small
  roughFloor_pos := D.roughFloor_pos
  rough_margin := fun t ht => D.rough_margin t (core_subset_common c n ht)
  history_buffer := fun t ht => D.history_buffer t (core_subset_common c n ht)
  selected_cover := fun t ht => D.selected_cover t (core_subset_common c n ht)

/-- The continuous saving loss and the independent arithmetic omitted
test are controlled by the SAME fixed compact index.  The finite table is
then constructed, still before the target N is allowed to grow. -/
theorem exists_common_fixed_schedule (B : ℝ) (hB : 0 ≤ B) (eps : ℝ) (heps : 0 < eps) :
    ∃ (n N₀ : ℕ) (_D : CompactThirdChoice (commonCore n)), 2 ≤ N₀ ∧
      (∀ c : Cell, 0 ≤ omittedGain c n ∧ omittedGain c n < eps) ∧
      (∀ N, N₀ ≤ N → ∀ c F,
        (∀ p ∈ omittedTuples c n N, |F p| ≤ B) → |signedOmitted c n N F| < eps) := by
  obtain ⟨na,N₀,hN₀,ha⟩ := exists_common_signedOmitted_rectangle B hB eps heps
  choose m hm using fun c : Cell => eventually_atTop.mp
    ((tendsto_omittedGain c).eventually (gt_mem_nhds heps))
  let n := max na (Finset.univ.sup m)
  obtain ⟨D⟩ := exists_commonChoice n
  refine ⟨n,N₀,D,hN₀,?_,?_⟩
  · intro c
    exact ⟨omittedGain_nonneg c n,hm c n
      ((Finset.le_sup (f := m) (Finset.mem_univ c)).trans (le_max_right _ _))⟩
  · intro N hN c F hb
    exact ha n (le_max_left _ _) N hN c F hb

def roughProduct (p : Fin 6 → ℕ) : ℕ := [p 5,p 4,p 3,p 2,p 1,p 0].prod

theorem roughProduct_eq (p : Fin 6 → ℕ) : roughProduct p = ∏ i, p i := by
  norm_num [roughProduct,Fin.prod_univ_succ] <;> ring

theorem original_tuple_injective (c : Cell) (N : ℕ) {p : Fin 6 → ℕ}
    (hp : p ∈ originalTuples c N) : Function.Injective p := by
  have hc := (Finset.mem_filter.mp hp).2
  have hs : StrictAnti (actualPrimeTupleLog N p) := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    rcases hc.order with ⟨h54,h43,h32,h21,h10⟩
    fin_cases i <;> assumption
  intro i j hij
  apply hs.injective
  simp only [actualPrimeTupleLog,hij]

theorem original_tuple_weight_eq_reciprocalTotient (c : Cell) (N : ℕ)
    {p : Fin 6 → ℕ} (hp : p ∈ originalTuples c N) :
    tupleWeight p = 1 / (Nat.totient (roughProduct p) : ℝ) := by
  rw [roughProduct_eq]
  exact (actualPrimeBoxTuple_reciprocalTotient (Finset.mem_filter.mp hp).1
    (original_tuple_injective c N hp)).symm

def dataOfChoice {n : ℕ} (D : CompactThirdChoice (commonCore n)) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh)) : OriginalData :=
  ⟨D.e,D.chi,D.mesh,omega,rows4,licensed4,J5,rows5⟩

/-- A real compact original tuple constructs its old retained leaf.  The
independent common-policy preservation theorem carries that same product
into the refined policy8 support.  There is no equality of fifth caps. -/
theorem compact_tuple_mem_refined_rough_support
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ)^(19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh))
    (c : Cell) (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) :
    roughProduct p ∈ fixedRoughSupport
      ((policy8 (dataOfChoice D omega rows4 licensed4 J5 rows5) (N : ℝ)) false)
      N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ)) := by
  let d := dataOfChoice D omega rows4 licensed4 J5 rows5
  let carrier := roughPrimeUniverse N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ))
  obtain ⟨leaf,hleaf,hselected⟩ := compact_tuple_has_actual_retained_fibre c n
    (restrictChoice D c) N cap hN omega homega hcap rows4 licensed4 J5 rows5 p hp (fun _ => 1)
  have hold : roughProduct p ∈ firstExitRetainedModuli
      (P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega (N : ℝ)
        d.rows4 d.licensed4 d.J5 d.rows5) carrier := by
    apply (mem_firstExitRetainedModuli _ _ _).mpr
    refine ⟨leaf,hleaf,?_⟩
    rw [hselected]
    rfl
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (policy8 d (N : ℝ)) (policy8_even d (N : ℝ)) N cap _ _]
  exact original_root_moduli_subset_final d (N : ℝ)
    (by exact_mod_cast hN.le) carrier hold

/-- Exact original beta sign and exact full q=e*P, with no multiplicity
factor and no detached coefficient substituted for the physical rho. -/
theorem compact_fullq_coefficient_eq_pair
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ)^(19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh))
    (c : Cell) (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N)
    (L : ℝ) (e : ℕ) (he : e ∈ actualSmallRosserSupport N cap ((N : ℝ)^omega)) :
    let d := dataOfChoice D omega rows4 licensed4 J5 rows5
    let w := (N : ℝ)^omega
    let z := (N : ℝ)^(19 / 96 : ℝ)
    rho d N cap w z L (e * roughProduct p) =
      smallRoughPairCoefficient (fixedRoughCoefficient ((policy8 d (N : ℝ)) false) N cap w z)
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
        (e,roughProduct p) := by
  dsimp only [rho]
  apply smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt _ N cap _ _ hd)
  · exact he
  · exact compact_tuple_mem_refined_rough_support D N cap hN omega homega hcap
      rows4 licensed4 J5 rows5 c p hp

def omittedFullqTest (d : OriginalData) (c : Cell) (n N cap : ℕ)
    (w z L : ℝ) (e : ℕ) : ℝ :=
  ∑ p ∈ omittedTuples c n N,
    rho d N cap w z L (e * roughProduct p) / (Nat.totient (roughProduct p) : ℝ)

theorem omittedFullqTest_eq_signed (d : OriginalData) (c : Cell) (n N cap : ℕ)
    (w z L : ℝ) (e : ℕ) :
    omittedFullqTest d c n N cap w z L e =
      signedOmitted c n N (fun p => rho d N cap w z L (e * roughProduct p)) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_tuple_weight_eq_reciprocalTotient c N (Finset.mem_filter.mp hp).1]
  ring

/-- A subsequent small-divisor sum retains its real total absolute
weight.  In particular a pointwise one-bound on rho is not a proof that
this small-divisor factor is bounded uniformly in the target. -/
theorem abs_small_sum_omittedFullqTest_le (d : OriginalData) (c : Cell) (n N cap : ℕ)
    (w z L : ℝ) (E : Finset ℕ) (beta : ℕ → ℝ) :
    |∑ e ∈ E, beta e * omittedFullqTest d c n N cap w z L e| ≤
      (∑ e ∈ E, |beta e|) * omittedMass c n N := by
  calc
    _ ≤ ∑ e ∈ E, |beta e * omittedFullqTest d c n N cap w z L e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ E, |beta e| * omittedMass c n N := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul,omittedFullqTest_eq_signed]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h := abs_signedOmitted_le c n N
        (fun p => rho d N cap w z L (e * roughProduct p)) 1
        (fun p hp => actualSmallRoughRho_abs_le_one ((policy8 d (N : ℝ)) false)
          N cap w z L (e * roughProduct p))
      simpa only [one_mul] using h
    _ = _ := by rw [Finset.sum_mul]

/-- Genuine signed arithmetic reciprocal-totient payment, uniform in
the refined physical policy and in the exact small factor/full-q test.
An absolute sum over small factors is intentionally absent here. -/
theorem exists_omittedFullqTest_uniform_rectangle (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N →
      ∀ (d : OriginalData) (c : Cell) (cap : ℕ) (w z L : ℝ) (e : ℕ),
        |omittedFullqTest d c n N cap w z L e| < eps := by
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_common_signedOmitted_rectangle 1 (by norm_num) eps heps
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN d c cap w z L e
  rw [omittedFullqTest_eq_signed]
  apply h n hn N hN c _
  intro p hp
  exact actualSmallRoughRho_abs_le_one ((policy8 d (N : ℝ)) false)
    N cap w z L (e * roughProduct p)

end
end ImbalancedChen.P2OriginalSixthCommonScheduleAndFullQ
