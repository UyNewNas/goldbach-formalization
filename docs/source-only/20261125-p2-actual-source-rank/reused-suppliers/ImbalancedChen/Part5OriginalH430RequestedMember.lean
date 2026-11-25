import ImbalancedChen.Part5OriginalH430RequestedAdmission

/-!
Canonical production Member for the actual generated request path.
SOURCE ONLY / UNCOMPILED. No arbitrary Member, generation assignment,
mark or source-count identity is a premise of the root theorems.
All path labels survive; existence of a catalog label is NOT an injective
quotient of the occurrence list, and is never used to drop multiplicities.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedMember

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430CutoffCoherence
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission

/-- Deterministic physical cell label on each EXISTING edge, not a new
choice of an action or a residual-coordinate mesh at a later prime. -/
def pathCode {N : ℕ} (mesh : ℕ) : (es : List (Edge N)) → Program mesh es.length
  | [] => Fin.elim0
  | e::es => Fin.cases
      (edgeShape e,physicalLabel 0 1 mesh (edgeCoordinates e)) (pathCode mesh es)

def pathPrimes {N : ℕ} : (es : List (Edge N)) → IntegerCoordinates es.length
  | [] => Fin.elim0
  | e::es => Fin.cases (edgePrimes e) (pathPrimes es)

/-- An exact equation between the old physical evaluator and request
replay; it holds before any primality/admission proof. -/
theorem realize_path {N : ℕ} (mesh : ℕ) (r : Request) (es : List (Edge N)) :
    realize es.length r.node (pathCode mesh es) (physicalCoordinates N (pathPrimes es)) =
      (replay r es).node := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih =>
      change realize es.length (nextRequest r e).node (pathCode mesh es)
        (physicalCoordinates N (pathPrimes es)) = (replay (nextRequest r e) es).node
      exact ih (nextRequest r e)

theorem integerWord_path {N : ℕ} (mesh : ℕ) (r : Request) (es : List (Edge N)) :
    integerWord es.length r.old (pathCode mesh es) (pathPrimes es) = (replay r es).old := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih => exact ih (nextRequest r e)

theorem path_canonical {N : ℕ} (mesh : ℕ) (es : List (Edge N)) :
    ∀ i, canonicalPoint (pathCode mesh es i).1 (pathPrimes es i) := by
  induction es with
  | nil => intro i; exact Fin.elim0 i
  | cons e es ih => intro i; exact Fin.cases (edge_canonical e) ih i

theorem chosen_coherent {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hr : Coherent N Q r) (hp : ChosenPath N Q g r es) : Coherent N Q (replay r es) := by
  induction es generalizing g r with
  | nil => exact hr
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hp
      | succ g => exact ih (child_coherent hr hp.1) hp.2

theorem chosen_primeLetters {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (mesh : ℕ) (hr : Coherent N Q r) (hp : ChosenPath N Q g r es) :
    PrimeLetters N (pathCode mesh es) (pathPrimes es) := by
  induction es generalizing g r with
  | nil => intro i; exact Fin.elim0 i
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hp
      | succ g =>
          intro i
          exact Fin.cases (child_admission hr hp.1).2.2
            (ih (child_coherent hr hp.1) hp.2) i

/-- All generated edges supply their OWN local membership. No arbitrary
Member predicate is accepted at the root-facing boundary. -/
theorem chosen_member {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (mesh : ℕ) (hr : Coherent N Q r) (hp : ChosenPath N Q g r es) :
    Member 0 1 es.length r.node (pathCode mesh es) (physicalCoordinates N (pathPrimes es)) := by
  induction es generalizing g r with
  | nil => trivial
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hp
      | succ g =>
          have hstep := child_admission hr hp.1
          exact ⟨physicalLabel_member (child_coordinate_bounds hr hp.1 0)
              (child_coordinate_bounds hr hp.1 1),hstep.1,hstep.2.1,
            ih (child_coherent hr hp.1) hp.2⟩

theorem root_coherent {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root) :
    Coherent N (rootQ N precision root tau p) (rootRequest N precision root tau p) := by
  refine ⟨hN,trivial,?_,?_,rfl,?_,?_,?_,?_⟩
  · simp [rootRequest,frozenRoot,sourceRoot,word]
  · intro q hq
    have he : q = p := List.mem_singleton.mp hq
    subst q
    exact hp
  · exact (frozenLevel_bounds (root_total_bounds htau htauhi ht) precision).1.trans
      (root_total_bounds htau htauhi ht).2
  · exact (by norm_num : (0:ℝ) < 11/384).trans_le
      (frozenRoot_residual_bounds htau htauhi ht hn).1
  · exact Part5OriginalH430PrimeChildAdmission.physicalPrime_pos hN hp.1
  · exact frozenRoot_cutoffFits precision tau ht

theorem rootHistory_coherent {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root)
    (ho : o ∈ rootHistory N precision root tau p) :
    Coherent N (rootQ N precision root tau p) o.current := by
  rw [(history_facts ho).2.2]
  exact chosen_coherent (root_coherent hN htau htauhi hn hp ht) (history_facts ho).1

theorem rootHistory_member {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (mesh : ℕ) (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root)
    (ho : o ∈ rootHistory N precision root tau p) :
    Member 0 1 o.path.length (frozenRoot precision root tau (physicalPrime N p))
      (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) :=
  chosen_member mesh (root_coherent hN htau htauhi hn hp ht) (history_facts ho).1

/-- Concrete state and word identities, with occurrence labels unchanged. -/
theorem rootHistory_realization {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (mesh : ℕ) (ho : o ∈ rootHistory N precision root tau p) :
    historyNode N precision root tau p (pathCode mesh o.path) (pathPrimes o.path) = o.current.node ∧
    historyWord p (pathCode mesh o.path) (pathPrimes o.path) = o.current.old := by
  have he := (history_facts ho).2.2
  constructor
  · change realize o.path.length (rootRequest N precision root tau p).node
      (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) = _
    rw [realize_path]
    exact congrArg Request.node he.symm
  · change integerWord o.path.length (rootRequest N precision root tau p).old
      (pathCode mesh o.path) (pathPrimes o.path) = _
    rw [integerWord_path]
    exact congrArg Request.old he.symm

/-- All former geometric row inputs are supplied on every generated
occurrence. The original selected-count identity is still a different claim. -/
theorem rootHistory_support {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root)
    (ho : o ∈ rootHistory N precision root tau p) :
    let Q := rootQ N precision root tau p
    let L := physicalLevel N Q o.current.old
    parentWindow N Q o.current.old o.current.node.physical.ceiling ∧
    residual o.current.node.physical = L ∧ frozenResidualFloor ≤ L ∧
    o.current.node.physical.argument ∈ Icc (1:ℝ) 6 ∧
    2 ≤ P2OriginalChildPhysicalNormalization.alpha
      (Real.log (parentProduct o.current.old:ℝ)/Real.log (N:ℝ)) L ∧
    Q = (parentProduct o.current.old:ℝ)*(N:ℝ)^L := by
  have hc := root_coherent hN htau htauhi hn hp ht
  have hchosen := (history_facts ho).1
  have hlen := (history_facts ho).2.1
  have hmem := rootHistory_member 0 hN htau htauhi hn hp ht ho
  have hprime := chosen_primeLetters 0 hc hchosen
  have h := history_support hN htau htauhi hn (by omega : o.path.length ≤ 440)
    hp ht hprime hmem
  have hid := rootHistory_realization 0 ho
  dsimp only at h
  rw [hid.1,hid.2] at h
  exact h

/-- Geometric catalog coverage, NOT a claim that different occurrences
have different catalog labels, and NOT original count-source completeness. -/
theorem rootHistory_catalog {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (mesh : ℕ) (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root)
    (ho : o ∈ rootHistory N precision root tau p) :
    ∃ h : Label N mesh, h ∈ catalog N precision mesh tau ∧
      labelNode precision tau h = o.current.node ∧ labelWord h = o.current.old ∧
      labelCode precision tau h = Part5OriginalH430FrozenRootRefinement.rootCode precision
        (sourceRoot root tau (physicalPrime N p)).physical.total := by
  have hc := root_coherent hN htau htauhi hn hp ht
  have hchosen := (history_facts ho).1
  have hlen := (history_facts ho).2.1
  have h := natural_history_mem_catalog hN htau htauhi (by omega : o.path.length ≤ 440)
    hp ht (chosen_primeLetters mesh hc hchosen) (path_canonical mesh o.path)
    (rootHistory_member mesh hN htau htauhi hn hp ht ho)
  have hid := rootHistory_realization mesh ho
  simpa only [hid.1,hid.2] using h

/-- Existing full/selected gates are preserved when present. We do not
invent them at the classical root or identify every original filter. -/
theorem rootHistory_gates {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((precision:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand root)
    (ho : o ∈ rootHistory N precision root tau p)
    (hf : fullGates (frozenRoot precision root tau (physicalPrime N p)).physical)
    (hs : selectedGates (frozenRoot precision root tau (physicalPrime N p)).physical) :
    fullGates o.current.node.physical ∧ selectedGates o.current.node.physical := by
  have h := realize_gates_alpha hf hs (frozenRoot_alpha htau htauhi ht hn)
    (rootHistory_member 0 hN htau htauhi hn hp ht ho)
  have hid := (rootHistory_realization 0 ho).1
  change historyNode N precision root tau p (pathCode 0 o.path)
    (pathPrimes o.path) = o.current.node at hid
  change fullGates (historyNode N precision root tau p (pathCode 0 o.path)
      (pathPrimes o.path)).physical ∧
    selectedGates (historyNode N precision root tau p (pathCode 0 o.path)
      (pathPrimes o.path)).physical ∧ _ at h
  rw [hid] at h
  exact ⟨h.1,h.2.1⟩

end
end ImbalancedChen.Part5OriginalH430RequestedMember
