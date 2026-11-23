import ImbalancedChen.Part5OriginalH430DisagreementCounts
import ImbalancedChen.Part5OriginalH430AllEmittedReceiptLanes

/-! Independently resolve a scalar or specified-cell read in the ideal and
frozen chart at a common incoming program. Every disagreement of owners,
old-table winner lanes or read values is paid on actual additive labels. -/
namespace ImbalancedChen.Part5OriginalH430ReselectedReceivers
noncomputable section
open Set Filter Topology
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedBranches
open Part5OriginalH430SameQHistoryCells Part5OriginalH430IntegerItineraries
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenIntegerSupport
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter (iterate)
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPhysicalTransition
open P5OriginalFeedbackTableKernels Part5OriginalUpsilon5CausalDictionary (FloorAtom)
open Part5OriginalH430ClosedOwner Part5OriginalH430RequestedReads Part5OriginalH430RequestedHistory
open Part5OriginalH430AllEmittedReceiptLanes Part5OriginalH430NativeQueryPaths
open Part5OriginalH430PhysicalRoots Part5OriginalH430FullMemberStrips
open Part5OriginalH430NativeMovingDensity Part5OriginalH430FixedProgramL1
open Part5OriginalH430PrimeProgramWord Part5OriginalH430FixedPrimeScreen
open Part5OriginalH430SharpPrimeBox Part5OriginalH430FullPrimeTheta
open Part5OriginalH430AllReceiverPrimePassage Part5OriginalH430DisagreementCounts
open P5OriginalU5FrozenSource (receiver)

variable {mesh d r : ℕ}

private theorem owner_eq {r s : Request} (hu : r.node.upper=s.node.upper) (hm : r.mode=s.mode)
    (ha : ∀ b : FloorAtom,r.node.physical.argument∈tableAtomSet (!r.node.upper) b ↔
      s.node.physical.argument∈tableAtomSet (!s.node.upper) b) (G : ℕ) :
    resolve G r=resolve G s := by
  cases hr : r.mode with
  | cell i => simp only [resolve,hr,hm.symm.trans hr]
  | scalar =>
      have hs := hm.symm.trans hr
      by_cases he : ∃ b : FloorAtom,r.node.physical.argument∈tableAtomSet (!r.node.upper) b
      · let b := Classical.choose he
        have hb : r.node.physical.argument∈tableAtomSet (!r.node.upper) b := Classical.choose_spec he
        have hb' := (ha b).mp hb
        have he' : ∃ c : FloorAtom,s.node.physical.argument∈tableAtomSet (!s.node.upper) c := ⟨b,hb'⟩
        have hc : Classical.choose he'=b := tableAtom_unique (Classical.choose_spec he') hb'
        simp only [resolve,hr,hs,dif_pos he,dif_pos he']
        rw [hc,hu]
      · have he' : ¬∃ c : FloorAtom,s.node.physical.argument∈tableAtomSet (!s.node.upper) c :=
          fun ⟨c,hc⟩ => he ⟨c,(ha c).mpr hc⟩
        simp only [resolve,hr,hs,dif_neg he,dif_neg he']

def chartRequest (k : Root) (code : Program mesh d) (v : Option ℕ) (x : NativeSlot (shapes code) → ℝ)
    (mode : ReadMode) (w : List ℕ) : Request :=
  ⟨realize d (base k v (nativeRootCoordinate x)) code (nativeCoordinates (shapes code) x),w,mode⟩

def chartMember (k : Root) (code : Program mesh d) (v : Option ℕ) (x : NativeSlot (shapes code) → ℝ) :=
  Member 0 1 d (base k v (nativeRootCoordinate x)) code (nativeCoordinates (shapes code) x)

def emittedCoordinates {N : ℕ} (mesh p : ℕ) (es : List (Edge N)) :
    NativeSlot (shapes (pathCode mesh es)) → ℝ
  | .inl _ => physicalPrime N p
  | .inr ⟨i,j⟩ => physicalPrime N (pathPrimes es i ⟨j.val,j.isLt.trans_le (arity_le_two _)⟩)

private theorem canonical_unused (s : StepShape) (q) (hq : canonicalPoint s q)
    (j : Fin 2) (hj : ¬j.val<arity s) : q j=1 := by
  cases s <;> fin_cases j <;> simp_all [arity,canonicalPoint]

private theorem emitted_tail {N : ℕ} (mesh p : ℕ) (es : List (Edge N)) :
    nativeCoordinates (shapes (pathCode mesh es)) (emittedCoordinates mesh p es)=
      physicalCoordinates N (pathPrimes es) := by
  funext i j
  by_cases hj : j.val<arity (shapes (pathCode mesh es) i)
  · simp only [nativeCoordinates,dif_pos hj,emittedCoordinates,physicalCoordinates]
  · simp only [nativeCoordinates,dif_neg hj,physicalCoordinates,
      canonical_unused _ _ (path_canonical mesh es i) j hj,physicalPrime,Nat.cast_one,Real.log_one,zero_div]

/-- Frozen chart is the original occupied Request, including the old integer
word and the mode carried by the last emitted edge (or the scalar origin). -/
theorem frozen_chart_is_emitted {N n p : ℕ} {k : Root} {o : Occurrence N} (mesh : ℕ)
    (ho : o∈rootHistory N n k (finiteTau n) p) :
    chartRequest k (pathCode mesh o.path) (some n) (emittedCoordinates mesh p o.path)
      o.current.mode o.current.old = o.current := by
  have hh := (rootHistory_realization mesh ho).1
  change (⟨realize o.path.length _ _ _,o.current.old,o.current.mode⟩ : Request)=_
  rw [emitted_tail]
  change (⟨historyNode N n k (finiteTau n) p (pathCode mesh o.path) (pathPrimes o.path),
    o.current.old,o.current.mode⟩ : Request)=_
  rw [hh]

/-- The old table, generation, mode and integer word are shared data. The
two resolvers query independently realized arguments on their own sides. -/
def sameReading (G : ℕ) (r s : Request) : Prop :=
  resolve G r = resolve G s ∧ laneAt G r = laneAt G s ∧
  requestValue (iterate G) r = requestValue (iterate G) s

theorem common_chart_disagreement {k : Root} {code : Program mesh d} {n : ℕ}
    {x : NativeSlot (shapes code) → ℝ} (hr : x∈region k (shapes code))
    (hi : chartMember k code none x) (hs : chartMember k code (some n) x)
    (mode : ReadMode) (w : List ℕ) (G : ℕ)
    (hbad : ¬sameReading G (chartRequest k code none x mode w) (chartRequest k code (some n) x mode w)) :
    ∃ (l : Bool) (a : FloorAtom), x∈region k (shapes code) ∩ fixedDifference k code l a n := by
  let I := chartRequest k code none x mode w
  let S := chartRequest k code (some n) x mode w
  have hu : I.node.upper=S.node.upper := realize_upper_eq (by rfl) code _
  by_contra h
  have atoms (a : FloorAtom) : I.node.physical.argument∈tableAtomSet (!I.node.upper) a ↔
      S.node.physical.argument∈tableAtomSet (!S.node.upper) a := by
    let l := !I.node.upper
    have hEq : x∈fixedSet k code l a none ↔ x∈fixedSet k code l a (some n) := by
      by_contra he
      exact h ⟨l,a,hr,by change (_∧¬_)∨(_∧¬_); tauto⟩
    change I.node.physical.argument∈tableAtomSet l a ↔ _
    rw [←hu]
    change I.node.physical.argument∈tableAtomSet l a ↔ S.node.physical.argument∈tableAtomSet l a
    change (chartMember k code none x ∧ I.node.physical.argument∈tableAtomSet l a) ↔
      (chartMember k code (some n) x ∧ S.node.physical.argument∈tableAtomSet l a) at hEq
    simpa only [hi,hs,true_and] using hEq
  have hor (g : ℕ) := owner_eq (r:=I) (s:=S) hu rfl atoms g
  apply hbad
  refine ⟨hor G,?_,?_⟩
  · cases G with
    | zero => rfl
    | succ g => simp only [laneAt,hor (g+1),hu]
  · cases hh : resolve G I with
    | none => rw [resolve_none_value hh,resolve_none_value ((hor G).symm.trans hh)]
    | some i => rw [resolve_value hh,resolve_value ((hor G).symm.trans hh),hu]

def readerChange (k : Root) (code : Program mesh d) (n G : ℕ) (mode : ReadMode)
    (w : List ℕ) (x : NativeSlot (shapes code) → ℝ) : Prop :=
  x∈region k (shapes code) ∧ chartMember k code none x ∧ chartMember k code (some n) x ∧
    ¬sameReading G (chartRequest k code none x mode w) (chartRequest k code (some n) x mode w)

def readerLoss (N n m G : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (mode : (Fin r → ℕ) → ReadMode)
    (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ => 0) (fun _ => 1),
    if readerChange k code n G (mode p) (originalWord code e p) (view e (actualPrimeTupleLog N p))
    then |observed N n m k code e p E f / singularNormalization N| else 0

private theorem readerLoss_le (N n m G : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (mode) (E) (f) :
    readerLoss N n m G k code e mode E f ≤
      ∑ l : Bool, ∑ a : FloorAtom, screenCount N n m k code e l a 0 E f := by
  let F := fun (p : Fin r → ℕ) (l : Bool) (a : FloorAtom) =>
    if actualPrimeTupleLog N p∈screen k code e l a n
    then |observed N n m k code e p E f/singularNormalization N| else 0
  have hn (p l a) : 0≤F p l a := by dsimp [F]; split_ifs <;> positivity
  unfold readerLoss
  calc
    _ ≤ ∑ p∈actualPrimeBoxTuples N (fun _=>0) (fun _=>1), ∑ l : Bool, ∑ a : FloorAtom, F p l a := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs with hh
      · obtain ⟨l,a,ha⟩ := common_chart_disagreement hh.1 hh.2.1 hh.2.2.1 _ _ _ hh.2.2.2
        have hb : actualPrimeTupleLog N p∈screen k code e l a n := ha
        have ha' := Finset.single_le_sum (f:=fun b => F p l b) (fun b _=>hn p l b) (Finset.mem_univ a)
        have hl' := Finset.single_le_sum (f:=fun z => ∑ b : FloorAtom,F p z b)
          (fun z _=>Finset.sum_nonneg (fun b _=>hn p z b)) (Finset.mem_univ l)
        simpa only [F,if_pos hb] using ha'.trans hl'
      · exact Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ => hn p l a
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm

/-- A common threshold, uniform also in the actual per-word read mode and
generation. The atom sum is finite before the arithmetic parameter grows. -/
theorem reselected_actual_receivers (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : Programs mesh) (k : Root)
      (m G : ℕ) (mode) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell, E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      readerLoss N n m G k v.2 (order v.2) mode E f < eps := by
  let L : ℝ := (Fintype.card Bool:ℝ)*(Fintype.card FloorAtom:ℝ)
  have hl : 0≤L := by dsimp [L]; positivity
  let delta := eps/(L+1)
  have hd : 0<delta := div_pos he (by linarith)
  obtain ⟨T,hT⟩ := all_program_true_count_threshold mesh hd
  refine ⟨T,fun n hn => ?_⟩
  obtain ⟨N₀,hN₀⟩ := hT n hn
  refine ⟨N₀,fun N hN hev v k m G mode E f hE hf => ?_⟩
  apply (readerLoss_le ..).trans_lt
  have hsum : (∑ l : Bool, ∑ a : FloorAtom, screenCount N n m k v.2 (order v.2) l a 0 E f) ≤
      ∑ _l : Bool, ∑ _a : FloorAtom, delta := Finset.sum_le_sum (fun l _ => Finset.sum_le_sum
        (fun a _ => (hN₀ N hN hev v k l a m E f hE hf).le))
  apply hsum.trans_lt
  have hid := div_mul_cancel₀ eps (by linarith : L+1≠0)
  change delta*(L+1)=eps at hid
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change _ < eps
  dsimp only [L] at hid
  nlinarith only [hd,hid]

end
end ImbalancedChen.Part5OriginalH430ReselectedReceivers
