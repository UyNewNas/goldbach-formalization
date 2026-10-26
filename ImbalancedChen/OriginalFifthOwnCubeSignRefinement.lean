import ImbalancedChen.OriginalFifthNativeAtomChoices

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

An additional finite PRIMITIVE affine bank controls the terminal own-cube
test against EVERY original raw candidate limb and the genuine Gamma seed.
The two tests for old and new caps are separate. Their equality states
remain in the partition and both strict gates fail on their own equality
wall. No old-own-cube pass is imposed on a restored fifth tuple.

Primitive sign transport constructs the native raw owner and both terminal
flags on each occupied refined atom. The signed original density then has
an exact fixed-flag expression, with its variable cap values unchanged.
This is geometric accounting, with no analytic distribution license or
archived chronology premise/conclusion.
-/

namespace ImbalancedChen.OriginalFifthOwnCubeSignRefinement20261026b

noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1ActualVariableFourthFifthCellTestLimit
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthNativeAtomChoices20261026b

abbrev CubeGuard (R4 : List FourthWireRow) (R5 : List FifthWireRow) := CandidateKey R4 R5 × Bool
abbrev CubeWord (R4 : List FourthWireRow) (R5 : List FifthWireRow) := CubeGuard R4 R5 → Bool × Bool

/-- The common 2e buffer is included BEFORE each primitive comparison. -/
def cubeWall (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (k : CubeGuard R4 R5) (t : Fin 5 → ℝ) : ℝ :=
  primeTupleOwnCubeForm t + 2 * (e : ℝ) - affinePiece R4 R5 e m j k.1 k.2 t

theorem continuous_cubeWall (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (k : CubeGuard R4 R5) :
    Continuous (cubeWall R4 R5 e m j k) := by
  have hc : Continuous (fun t : Fin 5 → ℝ => primeTupleOwnCubeForm t) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  exact (hc.add continuous_const).sub (continuous_affinePiece R4 R5 e m j k.1 k.2)

def actualCubeWord (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) : CubeWord R4 R5 :=
  fun k => (decide (cubeWall R4 R5 e m j k t < 0), decide (cubeWall R4 R5 e m j k t ≤ 0))

def cubeAtom (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) : Set (Fin 5 → ℝ) :=
  {t | actualCubeWord R4 R5 e m j t = v}

def refinedAtom (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5) (v : CubeWord R4 R5) :
    Set (Fin 5 → ℝ) :=
  signAtom R4 R5 e m j w ∩ cubeAtom R4 R5 e m j v

theorem cube_strict_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (k : CubeGuard R4 R5) :
    cubeWall R4 R5 e m j k t < 0 ↔ cubeWall R4 R5 e m j k u < 0 := by
  have hb := congrArg (fun z => (z k).1) (ht.trans hu.symm)
  have hi : (actualCubeWord R4 R5 e m j t k).1 = true ↔
      (actualCubeWord R4 R5 e m j u k).1 = true := by rw [hb]
  simpa only [actualCubeWord, decide_eq_true_eq] using hi

theorem cube_weak_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (k : CubeGuard R4 R5) :
    cubeWall R4 R5 e m j k t ≤ 0 ↔ cubeWall R4 R5 e m j k u ≤ 0 := by
  have hb := congrArg (fun z => (z k).2) (ht.trans hu.symm)
  have hi : (actualCubeWord R4 R5 e m j t k).2 = true ↔
      (actualCubeWord R4 R5 e m j u k).2 = true := by rw [hb]
  simpa only [actualCubeWord, decide_eq_true_eq] using hi

theorem cube_wall_equality_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (k : CubeGuard R4 R5) :
    cubeWall R4 R5 e m j k t = 0 ↔ cubeWall R4 R5 e m j k u = 0 := by
  have hle := cube_weak_transport R4 R5 e m j v ht hu k
  have hlt := cube_strict_transport R4 R5 e m j v ht hu k
  constructor
  · intro hz
    exact le_antisymm (hle.mp hz.le)
      (le_of_not_gt (fun h => (not_lt_of_ge hz.ge) (hlt.mpr h)))
  · intro hz
    exact le_antisymm (hle.mpr hz.le)
      (le_of_not_gt (fun h => (not_lt_of_ge hz.ge) (hlt.mp h)))

/-- Native strict own-cube gate = BOTH primitive affine inequalities. -/
theorem literal_ownCube_iff_limbs
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (c : CandidateKey R4 R5) (t : Fin 5 → ℝ) :
    primeTupleOwnCubeForm t < literalValue R4 R5 e m j c t ↔
      cubeWall R4 R5 e m j (c, false) t < 0 ∧ cubeWall R4 R5 e m j (c, true) t < 0 := by
  simp only [literalValue, cubeWall, lt_sub_iff_add_lt, lt_min_iff, sub_neg]

theorem literal_ownCube_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (c : CandidateKey R4 R5) :
    primeTupleOwnCubeForm t < literalValue R4 R5 e m j c t ↔
      primeTupleOwnCubeForm u < literalValue R4 R5 e m j c u := by
  rw [literal_ownCube_iff_limbs, literal_ownCube_iff_limbs]
  exact and_congr (cube_strict_transport R4 R5 e m j v ht hu (c, false))
    (cube_strict_transport R4 R5 e m j v ht hu (c, true))

theorem parent_ownCube_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (p : ParentPosition R4) :
    primeTupleOwnCubeForm t < parentValue R4 e m j p t ↔
      primeTupleOwnCubeForm u < parentValue R4 e m j p u := by
  refine Fin.cases ?_ (fun k => ?_) p
  · simpa only [literal_seed] using literal_ownCube_transport R4 R5 e m j v ht hu seedKey
  · simpa only [literal_fourth] using literal_ownCube_transport R4 R5 e m j v ht hu (fourthKey k)

theorem successor_ownCube_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (p : ParentPosition R4) (q : FifthPosition R5) :
    primeTupleOwnCubeForm t < slotValue R4 R5 e m j p t q ↔
      primeTupleOwnCubeForm u < slotValue R4 R5 e m j p u q := by
  refine Fin.cases ?_ (fun k => ?_) q
  · exact parent_ownCube_transport R4 R5 e m j v ht hu p
  · simpa only [literal_fifth] using literal_ownCube_transport R4 R5 e m j v ht hu (fifthKey k)

def nativeGateFlags (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (t : Fin 5 → ℝ) : Bool × Bool :=
  (decide (primeTupleOwnCubeForm t < parentValue R4 e m j p.1 t),
    decide (primeTupleOwnCubeForm t < slotValue R4 R5 e m j p.1 t p.2))

theorem nativeGateFlags_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ cubeAtom R4 R5 e m j v) (hu : u ∈ cubeAtom R4 R5 e m j v)
    (p : JointPosition R4 R5) :
    nativeGateFlags R4 R5 e m j p t = nativeGateFlags R4 R5 e m j p u := by
  unfold nativeGateFlags
  rw [propext (parent_ownCube_transport R4 R5 e m j v ht hu p.1),
    propext (successor_ownCube_transport R4 R5 e m j v ht hu p.1 p.2)]

abbrev FrozenData (R4 : List FourthWireRow) (R5 : List FifthWireRow) :=
  JointPosition R4 R5 × (Bool × Bool)

def dataAt (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (t : Fin 5 → ℝ) : FrozenData R4 R5 :=
  (jointOwner R4 R5 e m j L t, nativeGateFlags R4 R5 e m j (jointOwner R4 R5 e m j L t) t)

theorem dataAt_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (v : CubeWord R4 R5) {t u : Fin 5 → ℝ}
    (ht : t ∈ refinedAtom R4 R5 e m j w v) (hu : u ∈ refinedAtom R4 R5 e m j w v) :
    dataAt R4 R5 e m j L t = dataAt R4 R5 e m j L u := by
  have hp := native_joint_constant R4 R5 e m j L w ht.1 hu.1
  unfold dataAt
  rw [hp]
  exact Prod.ext rfl (nativeGateFlags_constant R4 R5 e m j v ht.2 hu.2 _)

/-- Reference data exist only for inhabited fibers, and are proved valid
at EVERY point of that fiber. Nothing is supplied as the desired result. -/
def frozenData (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (v : CubeWord R4 R5) (h : (refinedAtom R4 R5 e m j w v).Nonempty) : FrozenData R4 R5 :=
  dataAt R4 R5 e m j L h.choose

theorem frozenData_spec
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (v : CubeWord R4 R5) (h : (refinedAtom R4 R5 e m j w v).Nonempty)
    {t : Fin 5 → ℝ} (ht : t ∈ refinedAtom R4 R5 e m j w v) :
    dataAt R4 R5 e m j L t = frozenData R4 R5 e m j L w v h :=
  dataAt_constant R4 R5 e m j L w v ht h.choose_spec

def fixedFlagKernel (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (d : FrozenData R4 R5) (t : Fin 5 → ℝ) : ℝ :=
  ((if d.2.2 then primeTupleMinusProfile (slotValue R4 R5 e m j d.1.1 t d.1.2) t else 0) -
    (if d.2.1 then primeTupleMinusProfile (parentValue R4 e m j d.1.1 t) t else 0)) * ∏ q, 1 / t q

theorem jointKernel_eq_fixedFlagKernel
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (t : Fin 5 → ℝ) :
    jointSavingKernel R4 R5 e m j p t =
      fixedFlagKernel R4 R5 e m j (p, nativeGateFlags R4 R5 e m j p t) t := by
  simp only [jointSavingKernel, fixedFlagKernel, nativeGateFlags,
    decide_eq_true_eq, primeOwnCubeGatedProfile]

/-- Exact original signed density on every refined atom, including old
failure/new success, both failure, equality, and inherited-seed branches. -/
theorem actualKernel_eq_frozenData
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (w : SignWord R4 R5) (v : CubeWord R4 R5)
    (h : (refinedAtom R4 R5 e m j w v).Nonempty) {t : Fin 5 → ℝ}
    (ht : t ∈ refinedAtom R4 R5 e m j w v) (hm : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1ActualVariableFifthPositiveCellLimit.variableCellKernel e chi m omega j
        (fourthFamily R4) L (fifthFamily R5 m) t =
      fixedFlagKernel R4 R5 e m j (frozenData R4 R5 e m j L w v h) t := by
  have hd := frozenData_spec R4 R5 e m j L w v h ht
  have hr : t ∈ jointRegion R4 R5 e m j L univ (jointOwner R4 R5 e m j L t) :=
    (mem_jointRegion R4 R5 e m j L univ _ t).mpr ⟨mem_univ t, rfl⟩
  rw [actualKernel_eq_jointSavingKernel R4 R5 e chi m omega J j hj L univ _ t hr hm,
    jointKernel_eq_fixedFlagKernel]
  change fixedFlagKernel R4 R5 e m j (dataAt R4 R5 e m j L t) t = _
  rw [hd]

end
end ImbalancedChen.OriginalFifthOwnCubeSignRefinement20261026b
