import ImbalancedChen.P2OriginalVariableRootCapAlphabet
import ImbalancedChen.P2CanonicalTentJointAdmissionWallPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original real U6 root and every computed fresh/inherit cap enter a
single pre-N joint affine alphabet. Both external prime coordinates stay
variable. The actual mixed-fibre consumer and whole physical-q charge
are used literally. This is not an identification with the full adopted
W bank or a beta-attached total-density convergence theorem.
-/
namespace ImbalancedChen.P2OriginalU6JointAdmissionPayment

noncomputable section
open scoped Classical BigOperators
open Set P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData P2OriginalVariableRootCapAlphabet
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2ActualPairJointPrefixWallCarrier P2ActualPairWholeQWallPayment
open P2CanonicalTentJointAdmissionWallPayment (jointAdmissionForm
  jointAdmissionForm_ne_zero jointAdmissionForm_actual_coordinate_identity)
open P2ActualMixedWarmDecisionWalls P2LowerFiniteCellRounding
open P2RoundedCausalFibreLossAndLevel P5SelectedMaskTransport

abbrev WallKey (mesh : ℕ) := (Fin 5) ⊕ SourceIndex mesh
abbrev WallIndex (mesh : ℕ) := Fin (Fintype.card (WallKey mesh))

/-- Only the first two slots are root variables. Every rough slot remains
in the admission form with its original coefficient, including the 3. -/
def rootLinear (j : ℕ) (i : Fin 5) : (Fin (2 + (j+1)) → ℝ) →L[ℝ] ℝ :=
  rootTSlope i • ContinuousLinearMap.proj 0 +
    rootUSlope i • ContinuousLinearMap.proj 1

def keyForm (j : ℕ) {mesh : ℕ} : WallKey mesh →
    (Fin (2 + (j+1)) → ℝ) →L[ℝ] ℝ
  | .inl i => jointAdmissionForm j - rootLinear j i
  | .inr _ => jointAdmissionForm j

def keyHeight (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) : WallKey mesh → ℝ
  | .inl i => rootConstant i - 2*(buffer : ℝ)
  | .inr i => sourceHeight R bank (2*buffer) i

def forms (j mesh : ℕ) : WallIndex mesh →
    (Fin (2 + (j+1)) → ℝ) →L[ℝ] ℝ :=
  fun i => keyForm j ((Fintype.equivFin (WallKey mesh)).symm i)

def heights (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) : WallIndex mesh → ℝ :=
  fun i => keyHeight R bank buffer ((Fintype.equivFin (WallKey mesh)).symm i)

/-- Every form is proper, including the constant W(a) branch of the
original root. Evaluating on the all-one vector gives at least j+4. -/
theorem keyForm_ne_zero (j mesh : ℕ) (key : WallKey mesh) : keyForm j key ≠ 0 := by
  cases key with
  | inr i => exact jointAdmissionForm_ne_zero j
  | inl i =>
      intro hz
      have heq := congrArg
        (fun f : (Fin (2 + (j+1)) → ℝ) →L[ℝ] ℝ => f (fun _ => 1)) hz
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      fin_cases i <;>
        simp [keyForm, rootLinear, rootTSlope, rootUSlope, jointAdmissionForm] at heq <;>
        norm_num at heq <;> linarith

theorem forms_ne_zero (j mesh : ℕ) (i : WallIndex mesh) : forms j mesh i ≠ 0 :=
  keyForm_ne_zero j mesh _

theorem joint_root_coordinates (N : ℕ) (p : ℕ × ℕ) (r j : ℕ) :
    actualPrimeTupleLog N (jointPrefix (j+1) p r) 0 = coordinate N p.2 ∧
      actualPrimeTupleLog N (jointPrefix (j+1) p r) 1 = coordinate N p.1 := by
  constructor <;>
    simp [actualPrimeTupleLog, jointPrefix, jointWord, primeHistoryTuple, coordinate]

theorem rootLinear_actual (N : ℕ) (p : ℕ × ℕ) (r j : ℕ) (i : Fin 5) :
    rootLinear j i (actualPrimeTupleLog N (jointPrefix (j+1) p r)) =
      rootTSlope i * coordinate N p.2 + rootUSlope i * coordinate N p.1 := by
  simp only [rootLinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul,
    (joint_root_coordinates N p r j).1, (joint_root_coordinates N p r j).2]

/-- Actual incoming cap classification, with no cap value or finite
alphabet premise. The preserved original root switch is consumed here. -/
theorem actual_admission_key (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (p : ℕ × ℕ) (r j : ℕ)
    (hj : j < r.primeFactorsList.length) (width : ℝ)
    (hw : let seed := rootSeed true buffer N p
      let H := run (pairPlan R bank (2*buffer) seed) R.epsilon ceiling
        (pairRoot N p seed) ((physicalWord N r.primeFactorsList).take j)
      |H.word.sum + 3*(physicalWord N r.primeFactorsList).getD j 0 - H.cap| ≤ width) :
    ∃ key : WallKey mesh,
      |keyForm j key (actualPrimeTupleLog N (jointPrefix (j+1) p r)) -
        keyHeight R bank buffer key| ≤ width := by
  let seed := rootSeed true buffer N p
  let H := run (pairPlan R bank (2*buffer) seed) R.epsilon ceiling
    (pairRoot N p seed) ((physicalWord N r.primeFactorsList).take j)
  let x := actualPrimeTupleLog N (jointPrefix (j+1) p r)
  have hsum : jointAdmissionForm j x =
      H.word.sum + 3*(physicalWord N r.primeFactorsList).getD j 0 := by
    simpa only [x, H, run_word, List.sum_append, pairRoot] using
      jointAdmissionForm_actual_coordinate_identity N p r j hj
  have hw' : |jointAdmissionForm j x - H.cap| ≤ width := by
    rw [hsum]
    exact hw
  rcases original_pair_prefix_cap_cases R bank buffer true N p
      (physicalWord N r.primeFactorsList) j with hi | hf
  · obtain ⟨i, hplane⟩ := original_U6_root_plane (coordinate N p.1) (coordinate N p.2)
    have hroot : seed = rootConstant i - 2*(buffer : ℝ) + rootLinear j i x := by
      change P5U6CausalLevelGeometry.physicalLevel (coordinate N p.1)
        (coordinate N p.2) - 2*(buffer : ℝ) =
          rootConstant i - 2*(buffer : ℝ) +
            rootLinear j i (actualPrimeTupleLog N (jointPrefix (j+1) p r))
      rw [hplane, rootLinear_actual]
      unfold rootPlane
      ring
    refine ⟨.inl i, ?_⟩
    change |(jointAdmissionForm j - rootLinear j i) x -
      (rootConstant i - 2*(buffer : ℝ))| ≤ width
    change H.cap = seed at hi
    rw [hi, hroot] at hw'
    rw [ContinuousLinearMap.sub_apply]
    have halg : jointAdmissionForm j x - rootLinear j i x -
        (rootConstant i - 2*(buffer : ℝ)) =
        jointAdmissionForm j x - (rootConstant i - 2*(buffer : ℝ) + rootLinear j i x) := by
      ring
    rw [halg]
    exact hw'
  · obtain ⟨i, hi⟩ := hf
    refine ⟨.inr i, ?_⟩
    change |jointAdmissionForm j x - sourceHeight R bank (2*buffer) i| ≤ width
    change H.cap = sourceHeight R bank (2*buffer) i at hi
    simpa only [hi] using hw'

/-- The mark being charged, with its own complete residual modulus, enters
the exact G physical-q carrier. It is not an unrelated retained witness. -/
theorem actual_admission_enters_joint_products (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N enum : ℕ) (p : ℕ × ℕ)
    (omega : ℝ) (r j : ℕ) (width : ℝ) (hp : p ∈ sixthSupport N)
    (hr : r ∈ universe N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent))
    (hj : j < r.primeFactorsList.length)
    (hw : let seed := rootSeed true buffer N p
      let H := run (pairPlan R bank (2*buffer) seed) R.epsilon ceiling
        (pairRoot N p seed) ((physicalWord N r.primeFactorsList).take j)
      |H.word.sum + 3*(physicalWord N r.primeFactorsList).getD j 0 - H.cap| ≤ width) :
    (p.1*p.2)*r ∈ jointWallProducts N enum omega
      (forms j mesh) (heights R bank buffer) width := by
  obtain ⟨key, hkey⟩ := actual_admission_key R bank buffer N p r j hj width hw
  apply Finset.mem_image.mpr
  refine ⟨(p,r), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hp,hr⟩, by omega,
    Fintype.equivFin (WallKey mesh) key, ?_⟩
  simpa only [forms, heights, Equiv.symm_apply_apply] using hkey

/-- The original native selectedPolicy is the consumer. Every actual
mixed d is either on a genuine code wall or in this fixed joint catalogue.
The real original root is used; no equality with an adopted policy occurs. -/
theorem original_U6_mixed_code_or_joint_wall (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) {omega tau : ℝ}
    (ha : (R.epsilon : ℝ) ≤ omega) (htau : 0 < tau)
    {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ sixthSupport N) {r : ℕ}
    (hr : r ∈ universe N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent))
    (hm : mixed (selectedPolicy R bank buffer true N p)
      N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent) tau r) :
    ∃ j : ℕ, j < r.primeFactorsList.length ∧
      ((∃ x ∈ (physicalWord N r.primeFactorsList).take (j+1),
        ∃ q : Fin (mesh+2),
          |x - logPrimeMeshPoint R.epsilon ceiling mesh q.val| ≤ tau) ∨
      (p.1*p.2)*r ∈ jointWallProducts N enum omega
        (forms j mesh) (heights R bank buffer) (((j : ℝ)+3)*tau)) := by
  have hab : (R.epsilon : ℝ) < (ceiling : ℝ) := by
    have he : (R.epsilon : ℝ) < 417/5000 := by exact_mod_cast R.epsilon_lt_a
    norm_num [ceiling]
    linarith
  have hb : aExponent ≤ (ceiling : ℝ) := by norm_num [aExponent,ceiling]
  obtain ⟨j,hj,hw⟩ := all_actual_mixed_warm_decision_walls
    (pairPlan R bank (2*buffer) (rootSeed true buffer N p))
    hab ha hb htau hN enum p (rootSeed true buffer N p) hr hm
  refine ⟨j,hj,?_⟩
  rcases hw with hc | hw
  · exact Or.inl hc
  · exact Or.inr (actual_admission_enters_joint_products R bank buffer N enum p omega
      r j (((j : ℝ)+3)*tau) hp hr hj hw.2)

/-- Concrete independently defined canonical source, now with its ORIGINAL
real root. This is a proper specialization, not a full-bank identity. -/
theorem canonical_original_U6_mixed_cover (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) {omega tau : ℝ} (ha : (R.epsilon : ℝ) ≤ omega)
    (htau : 0 < tau) {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ)
    {p : ℕ × ℕ} (hp : p ∈ sixthSupport N) {r : ℕ}
    (hr : r ∈ universe N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent))
    (hm : mixed (selectedPolicy R
      (P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor) buffer true N p)
      N enum ((N : ℝ)^omega) ((N : ℝ)^aExponent) tau r) :
    ∃ j : ℕ, j < r.primeFactorsList.length ∧
      ((∃ x ∈ (physicalWord N r.primeFactorsList).take (j+1),
        ∃ q : Fin (mesh+2),
          |x - logPrimeMeshPoint R.epsilon ceiling mesh q.val| ≤ tau) ∨
      (p.1*p.2)*r ∈ jointWallProducts N enum omega (forms j mesh)
        (heights R (P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor) buffer)
        (((j : ℝ)+3)*tau)) :=
  original_U6_mixed_code_or_joint_wall R _ buffer ha htau hN enum hp hr hm

/-- Delta and the even-N threshold are chosen for the fixed source bank
before N. The charge retains all external pairs, all residual moduli, and
the literal rounded-minus-raw coefficients of original selectedPolicy. -/
theorem exists_original_U6_admission_whole_q_payment (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (j : ℕ)
    (omega : ℝ) (homega : 0 < omega) (hgap : omega < aExponent)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ, ∀ tau : ℝ,
        wholeQWallCharge (selectedPolicy R bank buffer true N) N enum omega tau
          (forms j mesh) (heights R bank buffer) delta < eta := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_uniform_whole_q_joint_wall_payment
    omega homega hgap (forms j mesh) (heights R bank buffer)
    (forms_ne_zero j mesh) eta heta
  exact ⟨delta,hd,N0,hN0,fun N hN hEven enum tau =>
    hpay N hN hEven enum (selectedPolicy R bank buffer true N) tau⟩

end
end ImbalancedChen.P2OriginalU6JointAdmissionPayment
