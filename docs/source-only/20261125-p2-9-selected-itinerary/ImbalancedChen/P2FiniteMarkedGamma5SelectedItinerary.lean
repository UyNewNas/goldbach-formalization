import ImbalancedChen.Part5OriginalH430EmittedPathMultiplicity

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedItinerary
noncomputable section
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430BankSlotTargets Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430EmittedPathMultiplicity
open scoped Classical BigOperators

/-- A fixed action and a literal edge determine a test on the original
production carrier. Fixed reads introduce no arithmetic slot. -/
def bankTest {N : ℕ} (Q : ℝ) (r : Request) : Original106Action → Edge N → Prop
  | .inl (a,b), .w1Fixed i j => a = i ∧ b = j
  | .inl (a,b), .w1Prime i j p => a = i ∧ b = j ∧
      p ∈ singleChildren (.w1 i j) N Q r.old r.node.physical.ceiling
  | .inr a, .w2Fixed j _ => a = j
  | .inr a, .w2Prime j k p => a = j ∧
      p ∈ singleChildren (.w2 j k) N Q r.old r.node.physical.ceiling
  | .inr a, .w2Pair j k pp => a = j ∧
      pp ∈ pairChildren j k N Q r.old r.node.physical.ceiling
  | _, _ => False

theorem bank_mem_iff {N : ℕ} (Q : ℝ) (r : Request) (a : Original106Action) (e : Edge N) :
    e ∈ bankEdges N Q r a ↔ bankTest Q r a e := by
  cases a with
  | inl ab =>
    obtain ⟨a,b⟩ := ab
    cases e with
    | w1Fixed i j =>
      by_cases hi : a = i <;> by_cases hj : b = j <;> simp_all [bankEdges, bankTest, w1Edges]
    | w1Prime i j p =>
      by_cases hi : a = i <;> by_cases hj : b = j <;> simp_all [bankEdges, bankTest, w1Edges]
    | _ => simp [bankEdges, bankTest, w1Edges]
  | inr a =>
    cases e with
    | w2Fixed j b =>
      cases b <;> simp [bankEdges, bankTest, w2SingleEdges, w2PairEdges, eq_comm]
    | w2Prime j k p =>
      fin_cases k <;> by_cases he : a = j <;>
        simp_all [bankEdges, bankTest, w2SingleEdges, w2PairEdges]
    | w2Pair j k pp =>
      fin_cases k <;> by_cases he : a = j <;>
        simp_all [bankEdges, bankTest, w2SingleEdges, w2PairEdges]
    | _ => simp [bankEdges, bankTest, w2SingleEdges, w2PairEdges]

def branchTest {N : ℕ} (Q : ℝ) (r : Request) (i : Fin 200) : Choice → Edge N → Prop
  | .retained, .retained j => i = j
  | .buchstab, .buchstab upper p => r.node.upper = upper ∧
      p ∈ singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling
  | .bank slot, e => bankTest Q r (actionOfSlot slot) e
  | _, _ => False

theorem branch_mem_iff {N : ℕ} (Q : ℝ) (r : Request) (i : Fin 200) (c : Choice)
    (e : Edge N) : e ∈ branchEdges N Q r i c ↔ branchTest Q r i c e := by
  cases c with
  | retained => cases e <;> simp [branchEdges, branchTest, eq_comm]
  | buchstab => cases e <;> simp [branchEdges, branchTest, eq_comm, and_comm]
  | bank slot => exact bank_mem_iff Q r _ e

/-- All fields are evaluated at the supplied request, including its
specified/scalar read mode. No emitted-position hypothesis is used. -/
def stepTest {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (e : Edge N) : Prop :=
  ∃ (i : Fin 200) (c : Choice), resolve (g+1) r = some i ∧
    (roundDecision (iterate g) r.node.upper i).choice = c ∧ branchTest Q r i c e

theorem child_iff {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (e : Edge N) :
    e ∈ children N Q g r ↔ stepTest Q g r e := by
  constructor
  · intro he
    obtain ⟨i,c,hs,hb⟩ := child_source he
    exact ⟨i,c,hs.1,hs.2,(branch_mem_iff Q r i c e).mp hb⟩
  · rintro ⟨i,c,hr,hc,hb⟩
    simpa only [children,hr,hc] using (branch_mem_iff Q r i c e).mpr hb

theorem specified_child_iff {N : ℕ} {Q : ℝ} {g : ℕ} {r : Request} {i : Fin 200}
    {c : Choice} (hr : resolve (g+1) r = some i)
    (hc : (roundDecision (iterate g) r.node.upper i).choice = c) (e : Edge N) :
    e ∈ children N Q g r ↔ branchTest Q r i c e := by
  simpa only [children,hr,hc] using branch_mem_iff Q r i c e

def accepts {N : ℕ} (Q : ℝ) : ℕ → Request → List (Edge N) → Prop
  | _, _, [] => True
  | 0, _, _::_ => False
  | g+1, r, e::es => stepTest Q g r e ∧ accepts Q g (nextRequest r e) es

theorem accepts_iff_chosen {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (es : List (Edge N)) :
    accepts Q g r es ↔ ChosenPath N Q g r es := by
  induction es generalizing g r with
  | nil => cases g <;> rfl
  | cons e es ih =>
    cases g with
    | zero => rfl
    | succ g => exact and_congr (child_iff Q g r e).symm (ih g (nextRequest r e))

def finish {N : ℕ} (g : ℕ) (r : Request) (es : List (Edge N)) : Occurrence N :=
  ⟨es, replay r es, g-es.length⟩

theorem finish_mem_iff {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (es : List (Edge N)) :
    finish g r es ∈ history N Q g r ↔ accepts Q g r es := by
  constructor
  · intro hm
    exact (accepts_iff_chosen Q g r es).mpr (history_facts hm).1
  · induction es generalizing g r with
    | nil =>
      intro _
      cases g <;> simp [finish,replay,history,origin]
    | cons e es ih =>
      cases g with
      | zero => exact False.elim
      | succ g =>
        rintro ⟨he,hs⟩
        have h := ih g (nextRequest r e) hs
        have hx : finish (g+1) r (e::es) = prepend e (finish g (nextRequest r e) es) := by
          simp [finish,prepend,replay,List.length_cons]
        rw [hx,history]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨e,(child_iff Q g r e).mpr he,List.mem_map.mpr ⟨_,h,rfl⟩⟩)

private theorem path_sum {N : ℕ} (es : List (Edge N)) (os : List (Occurrence N))
    (hn : (os.map itinerary).Nodup) :
    ((os.filter (fun o => decide (o.path = es))).map mark).sum =
      if es ∈ os.map Occurrence.path then (es.map edgeWeight).prod else 0 := by
  induction os with
  | nil => simp
  | cons o os ih =>
    obtain ⟨hne,ht⟩ := List.nodup_cons.mp hn
    by_cases he : o.path = es
    · have hrest : es ∉ os.map Occurrence.path := by
        intro h
        obtain ⟨u,hu,he'⟩ := List.mem_map.mp h
        apply hne
        exact List.mem_map.mpr ⟨u,hu,by simp [itinerary,he,he']⟩
      simp [he,hrest,ih ht,mark]
    · simp [he,Ne.symm he,ih ht]

/-- Exact weight at positions whose literal full path equals the
specified edge list. A missing edge or a rejected owner gives zero. -/
theorem fixed_path_mark {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (es : List (Edge N)) :
    (((history N Q g r).filter (fun o => decide (o.path = es))).map mark).sum =
      if accepts Q g r es then (es.map edgeWeight).prod else 0 := by
  classical
  rw [path_sum es _ (history_itinerary_nodup N Q g r)]
  have hmem : es ∈ (history N Q g r).map Occurrence.path ↔ accepts Q g r es := by
    constructor
    · intro h
      obtain ⟨o,ho,rfl⟩ := List.mem_map.mp h
      exact (accepts_iff_chosen Q g r o.path).mpr (history_facts ho).1
    · intro h
      exact List.mem_map.mpr ⟨_,(finish_mem_iff Q g r es).mpr h,rfl⟩
  simp only [hmem]

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedItinerary
