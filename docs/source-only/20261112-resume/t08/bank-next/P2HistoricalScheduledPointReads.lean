import ImbalancedChen.P2Historical248Authentication
import ImbalancedChen.P2HistoricalHighPointAncestry

/-!
The two historical point slots stay attached to the JSON row through the
three possible effective W2 bases. Projection of the ordered tagged list is
the original schedule, not merely a bijection of a set of parameters. Only
source support/point geometry is newly checked here; no original numerical
iteration, saved integer or row certificate is recomputed by this file.
-/
namespace ImbalancedChen.P2HistoricalScheduledPointReads

noncomputable section
open P2HistoricalSourceJSON P2Historical248Authentication
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalLowerBankAncestry P2HistoricalBankLogWeights P2HistoricalHighPointAncestry
open P2HistoricSavedOrdinaryDefectAssembly (BankEndpointLicences)

def HighPoint (i : Fin 200) (x : ℚ) : Prop :=
  100 ≤ i.val ∧ 3 < x ∧ gridAt i.val < x ∧ x ≤ gridAt (i.val+1)

instance (i : Fin 200) (x : ℚ) : Decidable (HighPoint i x) := by
  unfold HighPoint; infer_instance

def targetsLow (ts : List (Fin 200)) : Bool := ts.all (fun i => decide (i.val < 100))
def w1Geometry (a : SourceW1) : Bool :=
  targetsLow a.targets && decide (HighPoint a.pointIndex a.s0)

def anchor0 (v : Value) : ℚ := rational (at (field v "parameters") 1)
def anchor1 (v : Value) : ℚ := rational (at (field v "parameters") 2)

def w2Geometry (v : Value) (a : W2Action) : Bool :=
  targetsLow a.targets && (match a.points with
    | [p,r] => decide (p.multiplicity = 4 ∧ r.multiplicity = 1 ∧
        HighPoint p.index (anchor0 v) ∧ HighPoint r.index (anchor1 v))
    | _ => false)

def oldRows : List Value := items (field jsonOldW2 "actions")
def addedRows : List Value := items (field jsonNewW2 "actions")

/-- The only new closed decision: targets and the two argument/index/multiplicity
slots of the raw archive. No iteration, h/H entry, baseline, weight value,
17,572-row check or point comparison with an analytic function is evaluated. -/
private theorem archive_geometry :
    w1Original.all w1Geometry = true ∧
    oldRows.all (fun v => w2Geometry v (readW2 v)) = true ∧
    addedRows.all (fun v => w2Geometry v (readW2 v)) = true := by decide

/- Prefix zips here use the exact source update list.  Length correctness
is already the domain of the historical schema, and is not needed to make
the projection equality or the per-occurrence implications true. -/
private theorem left_mem_zip {α β : Type*} {xs : List α} {ys : List β} {b : α × β}
    (hb : b ∈ xs.zip ys) : b.1 ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at hb
  | cons x xs ih =>
    cases ys with
    | nil => simp at hb
    | cons y ys =>
      change b ∈ (x,y) :: xs.zip ys at hb
      rcases List.mem_cons.mp hb with h | h
      · subst b; exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih h)

theorem scheduled_w1_geometry (n : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule n) :
    w1Geometry a = true := by
  unfold sourceW1Schedule at ha
  split at ha
  · exact List.all_eq_true.mp archive_geometry.1 a ha
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact List.all_eq_true.mp archive_geometry.1 b.1 (left_mem_zip hb)

def tag (vs : List Value) : List (Value × W2Action) := vs.map (fun v => (v,readW2 v))
def reprice : List Value → List Value → List (Value × W2Action)
  | v::vs, u::us => (v, { readW2 v with base := integer (field u "new_base") }) :: reprice vs us
  | _, _ => []

def taggedW2 (n : ℕ) : List (Value × W2Action) :=
  if n < 24 then []
  else if n < 56 then tag oldRows
  else if n < 120 then reprice oldRows (items (field json120 "W2_baseline_updates"))
  else if n < 184 then reprice oldRows (items (field json184 "W2_baseline_updates"))
  else reprice oldRows (items (field json184 "W2_baseline_updates")) ++ tag addedRows

private theorem tag_snd (vs : List Value) :
    (tag vs).map Prod.snd = vs.map readW2 := by simp [tag, List.map_map, Function.comp_def]

private theorem reprice_snd (vs us : List Value) :
    (reprice vs us).map Prod.snd =
      ((vs.map readW2).zip us).map
        (fun p => { p.1 with base := integer (field p.2 "new_base") }) := by
  induction vs generalizing us with
  | nil => cases us <;> rfl
  | cons v vs ih =>
    cases us with
    | nil => rfl
    | cons u us =>
      change _ :: (reprice vs us).map Prod.snd = _ :: _
      rw [ih]

/-- Original chronological lists, including duplicate owners and order. -/
theorem tagged_schedule_eq (n : ℕ) : (taggedW2 n).map Prod.snd = designatedW2 n := by
  unfold taggedW2 designatedW2 sourceW2Schedule
  split_ifs <;> simp [List.map_append, tag_snd, reprice_snd, w2Original, w2Added,
    w2LowerK, w2Retained, oldRows, addedRows]

private theorem tag_geom (vs : List Value)
    (hs : vs.all (fun v => w2Geometry v (readW2 v)) = true) :
    ∀ b ∈ tag vs, w2Geometry b.1 b.2 = true := by
  intro b hb
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact List.all_eq_true.mp hs v hv

private theorem reprice_geom (vs us : List Value)
    (hs : vs.all (fun v => w2Geometry v (readW2 v)) = true) :
    ∀ b ∈ reprice vs us, w2Geometry b.1 b.2 = true := by
  induction vs generalizing us with
  | nil => cases us <;> simp [reprice]
  | cons v vs ih =>
    cases us with
    | nil => simp [reprice]
    | cons u us =>
      intro b hb
      change b ∈ _ :: reprice vs us at hb
      rcases List.mem_cons.mp hb with h | h
      · subst b
        exact List.all_eq_true.mp hs v (by simp)
      · exact ih us (List.all_eq_true.mpr fun x hx =>
          List.all_eq_true.mp hs x (List.mem_cons_of_mem v hx)) b h

theorem scheduled_w2_geometry (n : ℕ) {b : Value × W2Action} (hb : b ∈ taggedW2 n) :
    w2Geometry b.1 b.2 = true := by
  unfold taggedW2 at hb
  split_ifs at hb
  · simp at hb
  · exact tag_geom _ archive_geometry.2.1 b hb
  · exact reprice_geom _ _ archive_geometry.2.1 b hb
  · exact reprice_geom _ _ archive_geometry.2.1 b hb
  · rcases List.mem_append.mp hb with h | h
    · exact reprice_geom _ _ archive_geometry.2.1 b h
    · exact tag_geom _ archive_geometry.2.2 b h

theorem scheduled_w1_point (n : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule n) :
    HighPoint a.pointIndex a.s0 := by
  have hg := scheduled_w1_geometry n ha
  simpa only [w1Geometry, Bool.and_eq_true, decide_eq_true_eq] using
    (show decide (HighPoint a.pointIndex a.s0) = true from (Bool.and_eq_true.mp hg).2)

theorem scheduled_w2_points (n : ℕ) {b : Value × W2Action} (hb : b ∈ taggedW2 n) :
    ∃ p r : P2OriginalW2CandidateIntegerABI.PointRow,
      b.2.points = [p,r] ∧ p.multiplicity = 4 ∧ r.multiplicity = 1 ∧
      HighPoint p.index (anchor0 b.1) ∧ HighPoint r.index (anchor1 b.1) := by
  have hg := (Bool.and_eq_true.mp (scheduled_w2_geometry n hb)).2
  cases h : b.2.points with
  | nil => simp [h] at hg
  | cons p ps =>
    cases ps with
    | nil => simp [h] at hg
    | cons r rs =>
      cases rs with
      | nil => exact ⟨p,r,rfl,by simpa [h] using hg⟩
      | cons r' rs' => simp [h] at hg

/-- This now has *no* geometric or numerical premise for the actual history. -/
theorem designated_low_writes : LowWrites designatedW1 designatedW2 := by
  constructor
  · intro n a ha i hi
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    have hlow := (Bool.and_eq_true.mp (scheduled_w1_geometry n hv)).1
    exact of_decide_eq_true (List.all_eq_true.mp hlow i hi)
  · intro n a ha i hi
    rw [← tagged_schedule_eq n] at ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    have hlow := (Bool.and_eq_true.mp (scheduled_w2_geometry n hb)).1
    exact of_decide_eq_true (List.all_eq_true.mp hlow i hi)

abbrev outputAt := iterate designatedW1 designatedW2

theorem actual_w1_point_suffix (n : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule (n+1)) :
    outputAt (n+1) true a.pointIndex = suffixNumerator historicalLogWeights
      (outputAt n) false (max 50 (a.pointIndex.val-49)) :=
  high_last_suffix _ _ designated_low_writes n _ (scheduled_w1_point _ ha).1

theorem actual_w2_point_sum (n : ℕ) {b : Value × W2Action} (hb : b ∈ taggedW2 (n+1)) :
    ∃ p r : P2OriginalW2CandidateIntegerABI.PointRow,
      HighPoint p.index (anchor0 b.1) ∧ HighPoint r.index (anchor1 b.1) ∧
      sourcePointSum (outputAt (n+1)) b.2.points =
        4 * suffixNumerator historicalLogWeights (outputAt n) false (max 50 (p.index.val-49)) +
        suffixNumerator historicalLogWeights (outputAt n) false (max 50 (r.index.val-49)) := by
  obtain ⟨p,r,he,hm,hm',hp,hr⟩ := scheduled_w2_points _ hb
  refine ⟨p,r,hp,hr,?_⟩
  simp only [he, sourcePointSum, hm, hm', mul_one, add_zero]
  rw [high_last_suffix _ _ designated_low_writes n p.index hp.1,
      high_last_suffix _ _ designated_low_writes n r.index hr.1]
  ring

/-- At the actual 17,572-row consumer, no independent high H247 endpoint
certificate remains. The first hundred upper entries still need analytic
estimates. This is a reduction, not an unconditional bank licence. -/
theorem actual_bank_from_low_upper {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (low : ∀ i : Fin 200, i.val < 100 →
      (outputAt 247 true i : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1))) :
    BankEndpointLicences δ :=
  bankEndpointLicences_from_H247 hd hd'
    (upper_endpoints_from_low _ _ hd hd' designated_low_writes 247 low 247 le_rfl)

end
end ImbalancedChen.P2HistoricalScheduledPointReads
