import ImbalancedChen.P2OriginalU6JointAdmissionPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An independently defined arithmetic source: actual even-cube near-boundary
marks of the original variable-root selectedPolicy. Push forward the
literal signed rounded-minus-raw coefficients to the WHOLE physical q.
The classification theorem proves the wall inclusion; source and wall
fibres agree by the actual U6/rough product injection. No source-payment
estimate or coefficient identity is assumed.
-/
namespace ImbalancedChen.P2OriginalU6AdmissionSourceCharge

noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention P2OriginalPairRootRoughProducer
open P2OriginalPairSourceReceiver P2OriginalSelectedPairNativeData
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2ActualPairJointPrefixWallCarrier P2ActualPairWholeQWallPayment
open P2OriginalU6JointAdmissionPayment P2LowerFiniteCellRounding
open P5SelectedMaskTransport

def incomingState (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (p : ℕ × ℕ) (r j : ℕ) : Trace :=
  let seed := rootSeed true buffer N p
  run (pairPlan R bank (2*buffer) seed) R.epsilon ceiling
    (pairRoot N p seed) ((physicalWord N r.primeFactorsList).take j)

/-- Independent source filter: no reference to any affine wall catalogue.
The exact full even rank and the run's frozen cap are tested literally. -/
def admissionMarks (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N enum : ℕ) (omega : ℝ) (j : ℕ) (delta : ℝ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (sixthSupport N ×ˢ universe N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent)).filter
    (fun x => j < x.2.primeFactorsList.length ∧
      let H := incomingState R bank buffer N x.1 x.2 j
      (H.word.length+1)%2 = 0 ∧
        |H.word.sum + 3*(physicalWord N x.2.primeFactorsList).getD j 0 - H.cap| ≤ delta)

def admissionProducts (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N enum : ℕ) (omega : ℝ) (j : ℕ) (delta : ℝ) : Finset ℕ :=
  (admissionMarks R bank buffer N enum omega j delta).image physicalProduct

def admissionDifference (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N enum : ℕ) (omega tau : ℝ) (j : ℕ) (delta : ℝ) (B : ℕ) : ℝ :=
  ∑ x ∈ admissionMarks R bank buffer N enum omega j delta with physicalProduct x = B,
    markDifference (selectedPolicy R bank buffer true N) N enum omega tau x

def admissionCharge (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N enum : ℕ) (omega tau : ℝ) (j : ℕ) (delta : ℝ) : ℝ :=
  ∑ B ∈ admissionProducts R bank buffer N enum omega j delta,
    |admissionDifference R bank buffer N enum omega tau j delta B| / (Nat.totient B : ℝ)

theorem admissionMarks_subset_joint (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (omega : ℝ)
    (j : ℕ) (delta : ℝ) :
    admissionMarks R bank buffer N enum omega j delta ⊆
      jointWallMarks N enum omega (forms j mesh) (heights R bank buffer) delta := by
  intro x hx
  obtain ⟨hcarrier,hj,heven,hnear⟩ := Finset.mem_filter.mp hx
  obtain ⟨hp,hr⟩ := Finset.mem_product.mp hcarrier
  obtain ⟨key,hkey⟩ := actual_admission_key R bank buffer N x.1 x.2 j hj delta hnear
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hp,hr⟩, by omega,
    Fintype.equivFin (WallKey mesh) key, ?_⟩
  simpa only [forms,heights,Equiv.symm_apply_apply] using hkey

theorem admissionProducts_subset_joint (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (omega : ℝ)
    (j : ℕ) (delta : ℝ) :
    admissionProducts R bank buffer N enum omega j delta ⊆
      jointWallProducts N enum omega (forms j mesh) (heights R bank buffer) delta := by
  apply Finset.image_subset_image
  exact admissionMarks_subset_joint R bank buffer N enum omega j delta

theorem admissionDifference_at_product (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (omega tau : ℝ)
    (j : ℕ) (delta : ℝ) {x : (ℕ × ℕ) × ℕ}
    (hx : x ∈ admissionMarks R bank buffer N enum omega j delta) :
    admissionDifference R bank buffer N enum omega tau j delta (physicalProduct x) =
      markDifference (selectedPolicy R bank buffer true N) N enum omega tau x := by
  unfold admissionDifference
  rw [Finset.sum_eq_single x]
  · intro y hy hne
    obtain ⟨hymark,heq⟩ := Finset.mem_filter.mp hy
    exact (hne ((pair_rough_product_injOn N enum omega)
      (Finset.mem_filter.mp hymark).1 (Finset.mem_filter.mp hx).1 heq)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hx,rfl⟩)).elim

/-- The two independently defined pushforwards have the same value on
every actual source product, because its complete marked factorization
is unique. Dropping the pair root would invalidate this argument. -/
theorem admissionDifference_eq_wall (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (omega tau : ℝ)
    (j : ℕ) (delta : ℝ) {B : ℕ}
    (hB : B ∈ admissionProducts R bank buffer N enum omega j delta) :
    admissionDifference R bank buffer N enum omega tau j delta B =
      physicalWallDifference (selectedPolicy R bank buffer true N) N enum omega tau
        (forms j mesh) (heights R bank buffer) delta B := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hB
  rw [admissionDifference_at_product R bank buffer N enum omega tau j delta hx,
    physicalWallDifference_at_product (selectedPolicy R bank buffer true N)
      N enum omega tau (forms j mesh) (heights R bank buffer) delta
      (admissionMarks_subset_joint R bank buffer N enum omega j delta hx)]

theorem admissionCharge_le_whole_q_wall (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (omega tau : ℝ)
    (j : ℕ) (delta : ℝ) :
    admissionCharge R bank buffer N enum omega tau j delta ≤
      wholeQWallCharge (selectedPolicy R bank buffer true N) N enum omega tau
        (forms j mesh) (heights R bank buffer) delta := by
  unfold admissionCharge wholeQWallCharge
  calc
    _ = ∑ B ∈ admissionProducts R bank buffer N enum omega j delta,
        |physicalWallDifference (selectedPolicy R bank buffer true N) N enum omega tau
          (forms j mesh) (heights R bank buffer) delta B| / (Nat.totient B : ℝ) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [admissionDifference_eq_wall R bank buffer N enum omega tau j delta hB]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (admissionProducts_subset_joint R bank buffer N enum omega j delta)
      (by intro B _ _; positivity)

/-- Actual original-source admission charge, after summing ALL physical q
and both external primes. The width precedes the common even-N threshold;
all arithmetic enumeration cutoffs and fine labels remain universal. -/
theorem exists_actual_admission_source_payment (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (j : ℕ)
    (omega : ℝ) (homega : 0 < omega) (hgap : omega < aExponent)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ, ∀ tau : ℝ,
        admissionCharge R bank buffer N enum omega tau j delta < eta := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_original_U6_admission_whole_q_payment
    R bank buffer j omega homega hgap eta heta
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN hEven enum tau
  exact (admissionCharge_le_whole_q_wall R bank buffer N enum omega tau j delta).trans_lt
    (hpay N hN hEven enum tau)

end
end ImbalancedChen.P2OriginalU6AdmissionSourceCharge
