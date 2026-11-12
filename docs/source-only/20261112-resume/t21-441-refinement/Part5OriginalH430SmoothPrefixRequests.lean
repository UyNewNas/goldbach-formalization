import ImbalancedChen.Part5OriginalCausalSmoothAtlas
import ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge
import ImbalancedChen.Part5OriginalH430RequestedMember

/-! Pull the SAME finite smooth chart back to every emitted 430 request.
No arbitrary source, alternative winner, cutoff, common Q or parent mark
is supplied. The finite-mesh disintegration is exact at every permitted N;
it is not an induction licensing every original selected count. Source only. -/
namespace ImbalancedChen.Part5OriginalH430SmoothPrefixRequests
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430FixedReadDictionary Part5OriginalH430BankSlotTargets
open Part5OriginalH430ActualFeedbackQuotientRemainders P2Selected430CausalOccurrenceExporter
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430ActualNextTableThetaFloorBridge

def logs (N : ℕ) (xs : List ℕ) (i : Fin xs.length) : ℝ := physicalPrime N (xs.get i)

theorem physicalPrime_unit {N p : ℕ} (hN : 1 < N) (hp : 1 ≤ p) (hpN : p ≤ N) :
    physicalPrime N p ∈ Icc (0:ℝ) 1 := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hpr : (1:ℝ) ≤ p := by exact_mod_cast hp
  change 0 ≤ Real.log (p:ℝ)/Real.log (N:ℝ) ∧ Real.log (p:ℝ)/Real.log (N:ℝ) ≤ 1
  refine ⟨div_nonneg (Real.log_nonneg hpr) (Real.log_pos hNR).le,?_⟩
  apply (div_le_iff₀ (Real.log_pos hNR)).mpr
  simpa only [one_mul] using Real.log_le_log (zero_lt_one.trans_le hpr) (by exact_mod_cast hpN)

theorem coherent_prime_unit {N : ℕ} {Q : ℝ} {r : Request} (hr : Coherent N Q r)
    {p : ℕ} (hp : p ∈ r.old) : physicalPrime N p ∈ Icc (0:ℝ) 1 := by
  have hw := coherent_window hr
  have hpd : p ≤ parentProduct r.old := Nat.le_of_dvd hw.2.1 (List.dvd_prod hp)
  have hdN : parentProduct r.old ≤ N := by exact_mod_cast hw.2.2.1.le.trans hw.2.2.2.1
  exact physicalPrime_unit hr.target_gt_one (hr.letters p hp).1.one_lt.le (hpd.trans hdN)

def added {N : ℕ} (xs : List (Edge N)) : List ℕ :=
  xs.flatMap (fun e => appendedWord (edgeShape e) (edgePrimes e))

theorem replay_append {N : ℕ} (r : Request) (a b : List (Edge N)) :
    replay r (a ++ b) = replay (replay r a) b := by
  induction a generalizing r with
  | nil => rfl
  | cons e a ih => exact ih (nextRequest r e)

theorem replay_old_word {N : ℕ} (r : Request) (xs : List (Edge N)) :
    (replay r xs).old = r.old ++ added xs := by
  induction xs generalizing r with
  | nil => simp [replay,added]
  | cons e xs ih =>
    change (replay (nextRequest r e) xs).old = _
    rw [ih]
    simp [nextRequest,added,List.append_assoc]

/-- At a split of the exact generated path the old requests are chosen with
their *own* decreasing fuel. In particular retention is not re-evaluated
against a final 430 table inherited from the end of the path. -/
theorem chosen_prefix_suffix {N : ℕ} {Q : ℝ} (a b : List (Edge N))
    {g : ℕ} {r : Request} (h : ChosenPath N Q g r (a ++ b)) :
    ChosenPath N Q g r a ∧ ChosenPath N Q (g-a.length) (replay r a) b := by
  induction a generalizing g r with
  | nil => exact ⟨trivial, by simpa only [List.length_nil,Nat.sub_zero,replay] using h⟩
  | cons e a ih =>
    cases g with
    | zero => exact False.elim h
    | succ g =>
      obtain ⟨ha,hb⟩ := ih (g := g) (r := nextRequest r e) h.2
      exact ⟨⟨h.1,ha⟩, by simpa only [List.length_cons,Nat.succ_sub_succ_eq_sub,replay] using hb⟩

/-- Prefix/suffix chart on a real chronological integer path. The computed
word uses `appendedWord`, i.e. the larger then smaller slot for a pair.
Empty-arity edges do not introduce a log(1) slot. Every old gate is still
tested on the old slots; only future smooth labels are summed out. -/
theorem actual_prefix_marginal (P : Plan) {N g : ℕ} {Q : ℝ} {r : Request}
    (a b : List (Edge N)) (hr : Coherent N Q r) (h : ChosenPath N Q g r (a++b)) :
    let u := replay r a
    let v := replay r (a++b)
    v.old = u.old ++ added b ∧
    (∀ G : List Slot → Prop, G (v.node.physical.slots.take u.node.physical.slots.length) ↔
      G u.node.physical.slots) ∧
    ∀ j : Box P u.old.length,
      (∑ k : Box P (added b).length,
        atom P (Fin.append j k) (Fin.append (logs N u.old) (logs N (added b)))) =
      atom P j (logs N u.old) := by
  dsimp only
  have hv := chosen_coherent hr h
  have hw : (replay r (a++b)).old = (replay r a).old ++ added b := by
    rw [replay_append,replay_old_word (replay r a) b]
  refine ⟨hw,?_,?_⟩
  · intro G
    rw [replay_append]
    exact replay_ancestor_filter (replay r a) b G
  · intro j
    apply prefix_marginal
    intro i
    apply coherent_prime_unit hv
    rw [hw]
    exact List.mem_append_right _ (List.get_mem _ i)

/-- A finite source-sum disintegration on the SAME original list positions.
A mask can be applied to any signed value, but `split` only decomposes the
sum and does not turn an aggregate inequality into inequalities on masks. -/
def split (P : Plan) {N n : ℕ} {root : Root} {tau : ℝ} {p : ℕ} {g : Fin 430}
    (S : Finset (Index N n root tau p g)) (f : Index N n root tau p g → ℝ) : ℝ :=
  ∑ l ∈ S, ∑ j : Box P (levelOccurrence l).current.old.length,
    atom P j (logs N (levelOccurrence l).current.old) * f l

theorem split_exact (P : Plan) {N n : ℕ} {root : Root} {tau : ℝ} {p : ℕ} {g : Fin 430}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand root)
    (S : Finset (Index N n root tau p g)) (f : Index N n root tau p g → ℝ) :
    split P S f = ∑ l ∈ S, f l := by
  apply Finset.sum_congr rfl
  intro l _
  apply integrate_constant
  intro i
  exact coherent_prime_unit (rootHistory_coherent hN ht ht' hn hp hb
    (levelOccurrence_source l).1) (List.get_mem _ i)

/-- No new carrier: every active position still has its own canonical Member,
remaining generation, literal frozen Q and old path mark on every smooth read. -/
theorem position_certificate (P : Plan) {N n : ℕ} {root : Root} {tau : ℝ}
    {p mesh : ℕ} {g : Fin 430} (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand root) (l : Index N n root tau p g) :
    let o := levelOccurrence l
    Member 0 1 o.path.length (frozenRoot n root tau (physicalPrime N p))
        (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) ∧
      (N:ℝ)^o.current.node.physical.total = rootQ N n root tau p ∧
      predecessor o.remaining = some g ∧
      (∑ j : Box P o.current.old.length, atom P j (logs N o.current.old) * levelMark l) = levelMark l := by
  dsimp only
  have hl := (levelOccurrence_source l).1
  have hpred := level_predecessor l
  refine ⟨rootHistory_member mesh hN ht ht' hn hp hb hl,rootHistory_sameQ hl,hpred,?_⟩
  exact integrate_constant P (fun i =>
    coherent_prime_unit (rootHistory_coherent hN ht ht' hn hp hb hl) (List.get_mem _ i)) _

/-- Same smoothing for the actual selected base, the integer-floor payment
and the SIGNED Θ−1 correction of the literal next-table read. No `F`/closed
cell estimate appears: these are exact changes of summation only. -/
theorem same_base_floor_theta (P : Plan) {N n : ℕ} {root : Root} {tau : ℝ}
    {p : ℕ} (g : Fin 430) (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand root) :
    (∑ a : Original106Action, split P (selectedLevel N n root tau p g a)
      (fun l => occurrenceScale N n root tau p g l * baseValue a)) =
      selectedBankBaseMass N n root tau p g ∧
    (∑ a : Original106Action, split P (selectedLevel N n root tau p g a)
      (fun l => occurrenceScale N n root tau p g l * feedbackRoundingLoss (iterate g.val) a)) =
      selectedBankRoundingLoss N n root tau p g ∧
    split P (Finset.univ : Finset (Index N n root tau p g))
      (fun l => levelMark l * ((occurrenceTheta N n root tau p g l - 1) *
        requestValue (iterate (g.val+1)) (levelOccurrence l).current)) =
      actualThetaReadCorrection N n root tau p g := by
  have hsplit := split_exact (g := g) P hN ht ht' hn hp hb
  constructor
  · unfold selectedBankBaseMass
    exact Finset.sum_congr rfl (fun a _ => hsplit _ _)
  constructor
  · unfold selectedBankRoundingLoss
    exact Finset.sum_congr rfl (fun a _ => hsplit _ _)
  · exact hsplit _ _

end
end ImbalancedChen.Part5OriginalH430SmoothPrefixRequests
