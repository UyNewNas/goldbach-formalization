import ImbalancedChen.Part5OriginalH430MixedNativeL1

namespace ImbalancedChen.Part5OriginalH430FixedProgramL1
noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical
open P5OriginalActionMassBound P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430FullMemberStrips
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430FullRootAmplitude
open Part5OriginalH430FrozenRootMass Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FullMemberMeasurable
open Part5OriginalH430NativeMovingDensity Part5OriginalH430MixedNativeL1
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

abbrev shapes {mesh d : ℕ} (code : Program mesh d) := fun i => (code i).1

private theorem assigned {mesh d : ℕ} {p : TypedNode} {code : Program mesh d}
    {z : Coordinates d} (hm : Member 0 1 d p code z) :
    canonicalProgram 0 1 mesh (shapes code) z = code := by
  induction d generalizing p with
  | zero => funext i; exact Fin.elim0 i
  | succ d ih =>
    have ht := ih hm.2.2.2
    apply funext
    apply Fin.cases
    · apply Prod.ext
      · rfl
      · exact cellMember_unique (by norm_num : (0:ℝ) < 1)
          (physicalLabel_member hm.1.1 hm.1.2.1) hm.1
    · intro i
      exact congrFun ht i

def owner {mesh d : ℕ} (code : Program mesh d) : Set (NativeSlot (shapes code) → ℝ) :=
  {x | nativeProgram mesh (shapes code) x = code}

/-- The source-level QueryMember for this specified sequence of actions
and physical cells, on exactly its own prime slots. -/
def fixedSet {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (v : Option ℕ) : Set (NativeSlot (shapes code) → ℝ) := {x |
  let t := nativeRootCoordinate x
  let p := match v with | none => sourceRoot k 0 t | some n => frozenRoot n k (finiteTau n) t
  QueryMember 0 1 p code (nativeCoordinates (shapes code) x) lower atom}

theorem fixedSet_eq {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (v : Option ℕ) :
    fixedSet k code lower atom v = nativeSet mesh k (shapes code) lower atom v ∩ owner code := by
  ext x
  let z := nativeCoordinates (shapes code) x
  let t := nativeRootCoordinate x
  let p := match v with | none => sourceRoot k 0 t | some n => frozenRoot n k (finiteTau n) t
  let cc := nativeProgram mesh (shapes code) x
  change QueryMember 0 1 p code z lower atom ↔ QueryMember 0 1 p cc z lower atom ∧ cc = code
  constructor
  · intro h
    have hown : cc = code := assigned h.1
    exact ⟨by rwa [hown],hown⟩
  · rintro ⟨h,he⟩
    rwa [he] at h

theorem fixed_density {mesh d : ℕ} (k : Root) (code : Program mesh d) (v : Option ℕ)
    (x : NativeSlot (shapes code) → ℝ) :
    let t := nativeRootCoordinate x
    let p := match v with | none => sourceRoot k 0 t | some n => frozenRoot n k (finiteTau n) t
    density mesh k (shapes code) v x =
      physicalWeight (realize d p code (nativeCoordinates (shapes code) x)).physical := by
  cases v <;> exact congrArg (fun q : TypedNode => physicalWeight q.physical)
    (realize_eq_of_shapes _ (nativeProgram mesh (shapes code) x) code _ (fun _ => rfl))

theorem fixedSet_measurable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (v : Option ℕ) : MeasurableSet (fixedSet k code lower atom v) := by
  let s := shapes code
  have hr : Measurable (nativeRootCoordinate : (NativeSlot s → ℝ) → ℝ) := measurable_pi_apply _
  have hz : Measurable (nativeCoordinates s) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    unfold nativeCoordinates
    split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const
  cases v with
  | none => exact ((actual_joint_QueryMember_measurable 0 1 0 k 0 code lower atom).1).preimage (hr.prodMk hz)
  | some n => exact ((actual_joint_QueryMember_measurable 0 1 n k (finiteTau n) code lower atom).2).preimage (hr.prodMk hz)

theorem fixed_fine_integrable {mesh d : ℕ} (hd : d ≤ 440) (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) {n : ℕ} (hn : meshError n ≤ 11/384) :
    let s := shapes code
    IntegrableOn ((fixedSet k code lower atom none).indicator (density mesh k s none)) (region k s) ∧
    IntegrableOn ((fixedSet k code lower atom (some n)).indicator (density mesh k s (some n))) (region k s) := by
  let s := shapes code
  have each (v : Option ℕ) (h : IntegrableOn ((nativeSet mesh k s lower atom v).indicator
      (density mesh k s v)) (region k s)) :
      IntegrableOn ((fixedSet k code lower atom v).indicator (density mesh k s v)) (region k s) := by
    have hf := h.indicator (fixedSet_measurable k code lower atom v)
    have eqn : (fixedSet k code lower atom v).indicator ((nativeSet mesh k s lower atom v).indicator
        (density mesh k s v)) = (fixedSet k code lower atom v).indicator (density mesh k s v) := by
      funext x
      by_cases hx : x ∈ fixedSet k code lower atom v
      · have hx' := hx
        rw [fixedSet_eq] at hx'
        have hg : x ∈ nativeSet mesh k s lower atom v := hx'.1
        simp only [indicator_of_mem hx,indicator_of_mem hg]
      · simp only [indicator_of_notMem hx]
    rwa [eqn] at hf
  have h := fine_extended_integrable hd mesh k s lower atom hn
  exact ⟨each none h.1,each (some n) h.2⟩

def fixedDifference {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) :=
  let I := fixedSet k code lower atom none
  let S := fixedSet k code lower atom (some n)
  (I \ S) ∪ (S \ I)

theorem fixedDifference_eq {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) :
    fixedDifference k code lower atom n = difference mesh k (shapes code) lower atom n ∩ owner code := by
  ext x
  simp only [fixedDifference,fixedSet_eq,difference,mem_union,mem_diff,mem_inter_iff]
  tauto

def fixedError {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) :=
  let s := shapes code
  ∫ x in region k s, |(fixedSet k code lower atom none).indicator (density mesh k s none) x -
    (fixedSet k code lower atom (some n)).indicator (density mesh k s (some n)) x|

theorem fixedError_le {mesh d : ℕ} (hd : d ≤ 440) (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) {n : ℕ} (hn : meshError n ≤ 11/384) :
    fixedError k code lower atom n ≤ nativeError mesh k (shapes code) lower atom n := by
  let s := shapes code
  let I := nativeSet mesh k s lower atom none
  let S := nativeSet mesh k s lower atom (some n)
  let W := density mesh k s none
  let V := density mesh k s (some n)
  have h := fine_extended_integrable hd mesh k s lower atom hn
  have ha : IntegrableOn (fun x => |I.indicator W x - S.indicator V x|) (region k s) :=
    (h.1.sub h.2).abs
  unfold fixedError nativeError
  rw [fixedSet_eq,fixedSet_eq]
  apply integral_mono_of_nonneg (.of_forall (fun _ => abs_nonneg _)) ha
  apply Eventually.of_forall
  intro x
  change |(I ∩ owner code).indicator W x - (S ∩ owner code).indicator V x| ≤
    |I.indicator W x - S.indicator V x|
  by_cases hO : x ∈ owner code
  · by_cases hI : x ∈ I <;> by_cases hS : x ∈ S <;> simp [hI,hS,hO]
  · simpa only [indicator_of_notMem (fun h => hO h.2 : x ∉ I ∩ owner code),
      indicator_of_notMem (fun h => hO h.2 : x ∉ S ∩ owner code),sub_zero,abs_zero]
      using abs_nonneg (I.indicator W x - S.indicator V x)

/-- One precision threshold for all prescribed Programs and all their
fixed physical cells. Both endpoint estimates use the full absolute
native scale. -/
theorem all_fixed_program_threshold (mesh : ℕ) {eps : ℝ} (he : 0 < eps) :
    ∃ T : ℕ, ∀ n ≥ T, ∀ d ≤ 440, ∀ code : Program mesh d, ∀ k : Root,
      ∀ lower : Bool, ∀ atom : FloorAtom, fixedError k code lower atom n < eps ∧
      volume.real (region k (shapes code) ∩ fixedDifference k code lower atom n) < eps := by
  obtain ⟨T,hT⟩ := finite_mixed_native_threshold mesh he
  obtain ⟨U,hU⟩ := eventually_atTop.1 eventually_fine_mesh
  refine ⟨max T U,?_⟩
  intro n hn d hd code k lower atom
  let s := shapes code
  let v : Family := ⟨⟨d,by omega⟩,s⟩
  have h := hT n ((le_max_left T U).trans hn) v k lower atom
  refine ⟨(fixedError_le hd k code lower atom (hU n ((le_max_right T U).trans hn))).trans_lt h.1,?_⟩
  rw [fixedDifference_eq]
  have hb : volume (region k s) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hsub : region k s ∩ (difference mesh k s lower atom n ∩ owner code) ⊆
      region k s ∩ difference mesh k s lower atom n := fun _ hx => ⟨hx.1,hx.2.1⟩
  exact (ENNReal.toReal_mono (ne_top_of_le_ne_top hb.ne (measure_mono inter_subset_left))
    (measure_mono hsub)).trans_lt h.2

end
end ImbalancedChen.Part5OriginalH430FixedProgramL1
