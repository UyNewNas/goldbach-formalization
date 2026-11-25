import ImbalancedChen.P2FiniteMarkedGamma5RealSelectedPrefix
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.List.Nodup

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact reindexing of the original positive seed positions. The finite
shape/read index is independent of N. No product-fibre quotient, new
analytic estimate or smooth realization of an arbitrary subset is used.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5NativeSeedSum
noncomputable section
open Finset
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430IntegerItineraries Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430SeedHistoryMass
open Part5OriginalH430NativeQueryPaths Part5OriginalH430EmittedNativeQueries
open Part5OriginalH430EmittedPathMultiplicity
open P2FiniteMarkedGamma5SelectedItinerary P2FiniteMarkedGamma5SelectedSeedTerminal
open P2FiniteMarkedGamma5FixedNativeItinerary
open scoped Classical BigOperators

/-- A fixed shape and its literal owner/choice reads. There is no N field. -/
abbrev Index (d : ℕ) :=
  {i : (Fin d → StepShape) × (Fin d → ReadLabel) // ∀ j, noTransport (i.1 j)}

instance indexFinite (d : ℕ) : Finite (Index d) := by
  letI := fixed_indices_finite d
  infer_instance

instance indexFintype (d : ℕ) : Fintype (Index d) := Fintype.ofFinite _

abbrev Coordinate (N d : ℕ) := (i : Index d) × (NativeSlot i.val.1 → Fin (N+1))

def coordinateRoot {N d : ℕ} (c : Coordinate N d) : Fin (N+1) := c.2 (.inl ())

def coordinatePath {N d : ℕ} (c : Coordinate N d) : List (Edge N) :=
  pathAt c.1.val.1 c.1.property c.1.val.2 c.2

def coordinateReads {N d : ℕ} (c : Coordinate N d) :
    Fin (coordinatePath c).length → ReadLabel :=
  readsAt c.1.val.1 c.1.property c.1.val.2 c.2

@[simp] theorem coordinatePath_length {N d : ℕ} (c : Coordinate N d) :
    (coordinatePath c).length = d := by simp [coordinatePath,pathAt]

/-- N=0 is only a coordinate-independent evaluation of the old edge
coefficient. It asserts no prime or accepted path at target zero. -/
def fixedWeight {d : ℕ} (i : Index d) : ℝ :=
  ((pathAt i.val.1 i.property i.val.2
    (fun _ : NativeSlot i.val.1 => (0 : Fin (0+1)))).map edgeWeight).prod

theorem coordinate_weight {N d : ℕ} (c : Coordinate N d) :
    ((coordinatePath c).map edgeWeight).prod = fixedWeight c.1 :=
  pathAt_weight_independent c.1.val.1 c.1.property c.1.val.2 c.2 (fun _ => 0)

def coordinateOld {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (c : Coordinate N 430) : List ℕ :=
  (replay (rootRequest N n k t (coordinateRoot c).val) (coordinatePath c)).old

/-- The indicator is the original positive seed occurrence together with
its actual assigned read labels. It is not a new terminal predicate. -/
def literalSelected {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (c : Coordinate N 430) : Prop :=
  (coordinateRoot c).val ∈ originalBand N k ∧
    (∃ l ∈ seedPositions N n k t (coordinateRoot c).val,
      (levelOccurrence l).path = coordinatePath c) ∧
    assigned 430 (rootRequest N n k t (coordinateRoot c).val)
      (coordinatePath c) (coordinateReads c)

private theorem literal_checked {N n : ℕ} {k : Root} {t : ℝ} {c : Coordinate N 430}
    (hc : literalSelected n k t c) :
    checked (rootQ N n k t (coordinateRoot c).val) 430
      (rootRequest N n k t (coordinateRoot c).val) (coordinatePath c) (coordinateReads c) := by
  have hacc := ((fixed_path_seed_iff N n k t _ _).mp hc.2.1).2.1
  exact (checked_iff _ _ _ _ _).mpr ⟨hacc,hc.2.2⟩

private theorem edgeAt_injective {N : ℕ} (s : StepShape) (hs : noTransport s) (i : Fin 200) :
    Function.Injective (edgeAt (N := N) s hs i) := by
  intro x y h
  cases s with
  | transport j => exact False.elim (hs j rfl)
  | _ =>
    funext j
    fin_cases j <;> simp_all [edgeAt]

/-- Full ordered coordinates and literal read labels are recovered from
the root and path. Equal products are never used for this injection. -/
private theorem coordinate_ext {N d g : ℕ} {Q : ℝ} {r : Request}
    {c c' : Coordinate N d} (hroot : coordinateRoot c = coordinateRoot c')
    (hpath : coordinatePath c = coordinatePath c')
    (hc : checked Q g r (coordinatePath c) (coordinateReads c))
    (hc' : checked Q g r (coordinatePath c') (coordinateReads c')) : c = c' := by
  rcases c with ⟨⟨⟨sh,a⟩,hs⟩,x⟩
  rcases c' with ⟨⟨⟨sh',a'⟩,hs'⟩,y⟩
  dsimp only [coordinateRoot,coordinatePath,coordinateReads] at *
  have hsh : sh = sh' := by
    apply List.ofFn_injective
    simpa only [pathAt,List.map_ofFn,Function.comp_def,edgeAt_shape] using
      congrArg (List.map edgeShape) hpath
  subst sh'
  have ht : checked Q g r (pathAt sh hs a x)
      (fun i => a' (Fin.cast (by simp [pathAt]) i)) := by
    unfold readsAt at hc'
    rw [← hpath] at hc'
    exact hc'
  obtain ⟨b,hb,hu⟩ := (accepts_iff_unique_reads Q g r (pathAt sh hs a x)).mp
    (accepts_of_checked _ hc)
  have he : readsAt sh hs a x =
      (fun i => a' (Fin.cast (by simp [pathAt]) i)) :=
    (hu _ hc).trans (hu _ ht).symm
  have ha : a = a' := by
    funext i
    have H := congrFun he (Fin.cast (by simp [pathAt]) i)
    simpa [readsAt] using H
  subst a'
  have hedge :
      (fun i => edgeAt (sh i) (hs i) (a i).1 (fun j => x (.inr ⟨i,j⟩))) =
      (fun i => edgeAt (sh i) (hs i) (a i).1 (fun j => y (.inr ⟨i,j⟩))) :=
    List.ofFn_injective hpath
  have hxy : x = y := by
    funext j
    rcases j with u | ⟨i,j⟩
    · cases u
      exact hroot
    · exact congrFun (edgeAt_injective (sh i) (hs i) (a i).1 (congrFun hedge i)) j
  subst y
  rfl

private theorem exists_coordinate {N d g : ℕ} {Q : ℝ} {r : Request}
    {es : List (Edge N)} (p : Fin (N+1)) (hd : es.length = d)
    (ha : accepts Q g r es) :
    ∃ c : Coordinate N d, coordinateRoot c = p ∧ coordinatePath c = es ∧
      checked Q g r (coordinatePath c) (coordinateReads c) := by
  subst d
  obtain ⟨a,ha,_⟩ := (accepts_iff_unique_reads Q g r es).mp ha
  let i : Index es.length := ⟨(shapes es,a),fun j => emitted_noTransport (es.get j)⟩
  let c : Coordinate N es.length := ⟨i,coordinates p es⟩
  have he := recover_path p ha
  refine ⟨c,rfl,he,?_⟩
  change checked Q g r (pathAt (shapes es) _ a (coordinates p es))
    (readsAt (shapes es) _ a (coordinates p es))
  unfold readsAt
  simpa only [he,Fin.cast_eq_self] using ha

private theorem original_root_lt {N p : ℕ} {k : Root} (hp : p ∈ originalBand N k) : p < N := by
  have hc : p ∈ chenAdditivePrimeCarrier N := by
    cases k <;> exact (mem_filter.mp hp).1
  exact (mem_chenAdditivePrimeCarrier.mp hc).1

private theorem level_path_injective {N n p dep : ℕ} {k : Root} {t : ℝ} :
    Function.Injective (fun l : LevelIndex N n k t p dep => (levelOccurrence l).path) := by
  intro l l' he
  have H := history_itinerary_nodup N (rootQ N n k t p) 430 (rootRequest N n k t p)
  have ho : levelOccurrence l = levelOccurrence l' :=
    List.inj_on_of_nodup_map H (levelOccurrence_source l).1 (levelOccurrence_source l').1
      (congrArg (List.map letter) he)
  have hnd := List.Nodup.filter (fun o : Occurrence N => decide (o.remaining = dep))
    (List.Nodup.of_map itinerary H)
  exact hnd.injective_get ho

private theorem position_coordinate {N n p : ℕ} {k : Root} {t : ℝ}
    (hp : p ∈ originalBand N k) {l : LevelIndex N n k t p 0}
    (hl : l ∈ seedPositions N n k t p) :
    ∃ c : Coordinate N 430, literalSelected n k t c ∧
      (coordinateRoot c).val = p ∧ coordinatePath c = (levelOccurrence l).path := by
  have H := (fixed_path_seed_iff N n k t p (levelOccurrence l).path).mp ⟨l,hl,rfl⟩
  let p' : Fin (N+1) := ⟨p,by have := original_root_lt hp; omega⟩
  obtain ⟨c,hroot,hpath,hchecked⟩ := exists_coordinate p' H.1 H.2.1
  have hr : (coordinateRoot c).val = p := congrArg Fin.val hroot
  refine ⟨c,?_,hr,hpath⟩
  unfold literalSelected
  rw [hr]
  exact ⟨hp,⟨l,hl,hpath.symm⟩,((checked_iff _ _ _ _ _).mp hchecked).2⟩

/-- Exact finite coordinate formula before replacing the literal seed
test by the existing real selected domain. No positivity of F is needed. -/
theorem seed_sum_eq_literal_coordinates (N n : ℕ) (k : Root) (t : ℝ)
    (F : ℕ → List ℕ → ℝ) :
    (∑ p ∈ originalBand N k, ∑ l ∈ seedPositions N n k t p,
      levelMark l * F p (levelOccurrence l).current.old) =
    ∑ i : Index 430, ∑ x : NativeSlot i.val.1 → Fin (N+1),
      if literalSelected n k t ⟨i,x⟩ then
        fixedWeight i * F (x (.inl ())).val (coordinateOld n k t ⟨i,x⟩) else 0 := by
  let S := (originalBand N k).sigma (seedPositions N n k t)
  let T : Finset (Coordinate N 430) := univ.filter (literalSelected n k t)
  let E (s : (p : ℕ) × LevelIndex N n k t p 0) (hs : s ∈ S) : Coordinate N 430 :=
    Classical.choose (position_coordinate (mem_sigma.mp hs).1 (mem_sigma.mp hs).2)
  have H (s : (p : ℕ) × LevelIndex N n k t p 0) (hs : s ∈ S) :
      literalSelected n k t (E s hs) ∧ (coordinateRoot (E s hs)).val = s.1 ∧
        coordinatePath (E s hs) = (levelOccurrence s.2).path :=
    Classical.choose_spec (position_coordinate (mem_sigma.mp hs).1 (mem_sigma.mp hs).2)
  have hsum :
      (∑ s ∈ S, levelMark s.2 * F s.1 (levelOccurrence s.2).current.old) =
      ∑ c ∈ T, fixedWeight c.1 * F (coordinateRoot c).val (coordinateOld n k t c) := by
    apply sum_bij E
    · intro s hs
      exact mem_filter.mpr ⟨mem_univ _,(H s hs).1⟩
    · intro s hs s' hs' he
      rcases s with ⟨p,l⟩
      rcases s' with ⟨p',l'⟩
      have hp : p = p' := (H ⟨p,l⟩ hs).2.1.symm.trans
        ((congrArg (fun c => (coordinateRoot c).val) he).trans (H ⟨p',l'⟩ hs').2.1)
      subst p'
      have hl : l = l' := level_path_injective
        ((H ⟨p,l⟩ hs).2.2.symm.trans
          ((congrArg coordinatePath he).trans (H ⟨p,l'⟩ hs').2.2))
      cases hl
      rfl
    · intro c hc
      have hc' := (mem_filter.mp hc).2
      obtain ⟨l,hl,he⟩ := hc'.2.1
      let s : (p : ℕ) × LevelIndex N n k t p 0 := ⟨(coordinateRoot c).val,l⟩
      have hs : s ∈ S := mem_sigma.mpr ⟨hc'.1,hl⟩
      refine ⟨s,hs,?_⟩
      have hroot : coordinateRoot (E s hs) = coordinateRoot c := Fin.ext (H s hs).2.1
      have hpath : coordinatePath (E s hs) = coordinatePath c := (H s hs).2.2.trans he
      have hchecked : checked (rootQ N n k t (coordinateRoot c).val) 430
          (rootRequest N n k t (coordinateRoot c).val)
          (coordinatePath (E s hs)) (coordinateReads (E s hs)) := by
        simpa only [(H s hs).2.1] using literal_checked (H s hs).1
      exact coordinate_ext hroot hpath hchecked (literal_checked hc')
    · intro s hs
      have hroot := (H s hs).2.1
      have hpath := (H s hs).2.2
      have hm : levelMark s.2 = fixedWeight (E s hs).1 := by
        change ((levelOccurrence s.2).path.map edgeWeight).prod = _
        rw [← hpath]
        exact coordinate_weight (E s hs)
      have hold : (levelOccurrence s.2).current.old = coordinateOld n k t (E s hs) := by
        unfold coordinateOld
        rw [hroot,hpath]
        exact congrArg Request.old (history_facts (levelOccurrence_source s.2).1).2.2
      rw [hm,hold,hroot]
  calc
    _ = ∑ s ∈ S, levelMark s.2 * F s.1 (levelOccurrence s.2).current.old :=
      (sum_sigma (originalBand N k) (seedPositions N n k t) _).symm
    _ = _ := hsum
    _ = _ := by simp only [T,sum_filter,Fintype.sum_sigma,coordinateRoot]

private theorem slots_mem_append {N : ℕ} (e : Edge N) (j : Fin (arity (edgeShape e))) :
    (slots e j).val ∈ appendedWord (edgeShape e) (edgePrimes e) := by
  cases e with
  | buchstab b p =>
    cases b <;> fin_cases j <;> simp [slots,edgeShape,edgePrimes,appendedWord]
  | _ => fin_cases j <;> simp [slots,edgeShape,edgePrimes,appendedWord]

private theorem chosen_slot_primes {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hr : Coherent N Q r) (he : ChosenPath N Q g r es) :
    ∀ i : Fin es.length, ∀ j, (slots (es.get i) j).val.Prime ∧
      (slots (es.get i) j).val.Coprime N := by
  induction es generalizing g r with
  | nil => intro i; exact Fin.elim0 i
  | cons e es ih =>
    cases g with
    | zero => exact False.elim he
    | succ g =>
      intro i
      refine Fin.cases ?_ (fun i => ih (child_coherent hr he.1) he.2 i) i
      intro j
      exact (child_admission hr he.1).2.2 _ (slots_mem_append e j)

private theorem prime_of_edgeAt {N : ℕ} (s : StepShape) (hs : noTransport s)
    (a : Fin 200) (x : Fin (arity s) → Fin (N+1))
    (h : ∀ j, (slots (edgeAt s hs a x) j).val.Prime ∧
      (slots (edgeAt s hs a x) j).val.Coprime N) :
    ∀ j, (x j).val.Prime ∧ (x j).val.Coprime N := by
  cases s with
  | transport i => exact False.elim (hs i rfl)
  | retain | w1Fixed | w2Fixed => intro j; exact Fin.elim0 j
  | buchstabUpper | buchstabLower | w1Singleton | w2Singleton =>
    intro j
    fin_cases j
    exact h 0
  | w2Pair =>
    intro j
    fin_cases j
    · exact h 0
    · exact h 1

private theorem literal_primes {N n : ℕ} {k : Root} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) {c : Coordinate N 430}
    (hc : literalSelected n k t c) :
    ∀ j, (c.2 j).val.Prime ∧ (c.2 j).val.Coprime N := by
  have hroot := original_band_prime hc.1
  have hcoh := root_coherent (by omega : 1 < N) ht ht' hn hroot
    (original_band_geometry hN hc.1)
  have hacc := accepts_of_checked (coordinateReads c) (literal_checked hc)
  have hchosen := (accepts_iff_chosen _ _ _ _).mp hacc
  intro j
  rcases j with u | ⟨i,j⟩
  · cases u
    exact hroot
  · have H := chosen_slot_primes hcoh hchosen (stageEquiv c.1.val.1 c.1.property c.1.val.2 c.2 i)
    have hget :
        (coordinatePath c).get (stageEquiv c.1.val.1 c.1.property c.1.val.2 c.2 i) =
        edgeAt (c.1.val.1 i) (c.1.property i) (c.1.val.2 i).1
          (fun j => c.2 (.inr ⟨i,j⟩)) := by
      simp [coordinatePath,stageEquiv,pathAt]
    rw [hget] at H
    exact prime_of_edgeAt _ _ _ _ H j

def primeTuples (N : ℕ) (k : Root) (i : Index 430) :
    Finset (NativeSlot i.val.1 → Fin (N+1)) :=
  univ.filter fun x => (x (.inl ())).val ∈ originalBand N k ∧
    ∀ j, (x j).val.Prime ∧ (x j).val.Coprime N

/-- Primality and coprimality in this exact formula come from the
original root selector and original child carriers, not a new deletion. -/
theorem literal_iff_selected {N n : ℕ} {k : Root} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    literalSelected n k t ⟨i,x⟩ ↔
      ((x (.inl ())).val ∈ originalBand N k ∧
        ∀ j, (x j).val.Prime ∧ (x j).val.Coprime N) ∧
      (fun j => physicalPrime N (x j).val) ∈
        P2FiniteMarkedGamma5RealSelectedPrefix.selected n k t i.val.1 i.val.2 := by
  constructor
  · intro hc
    have hx := literal_primes hN ht ht' hn hc
    refine ⟨⟨hc.1,hx⟩,?_⟩
    exact (P2FiniteMarkedGamma5RealSelectedPrefix.fixed_prime_selected_iff
      hN ht ht' hn hc.1 i.val.1 i.property i.val.2 x rfl hx).mpr hc.2
  · rintro ⟨⟨hp,hx⟩,hsel⟩
    exact ⟨hp,(P2FiniteMarkedGamma5RealSelectedPrefix.fixed_prime_selected_iff
      hN ht ht' hn hp i.val.1 i.property i.val.2 x rfl hx).mp hsel⟩

/-- The original marked seed sum is exactly one finite coordinate sum
with the existing literal selected-domain indicator. The same arbitrary
old-word test is transported; no smoothness or positivity is assumed.
All native coordinates retain their order and may have repeated values. -/
theorem seed_marked_sum_eq_selected_coordinates (N n : ℕ) (k : Root) (t : ℝ)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (F : ℕ → List ℕ → ℝ) :
    (∑ p ∈ originalBand N k, ∑ l ∈ seedPositions N n k t p,
      levelMark l * F p (levelOccurrence l).current.old) =
    ∑ i : Index 430, ∑ x ∈ primeTuples N k i,
      if (fun j => physicalPrime N (x j).val) ∈
          P2FiniteMarkedGamma5RealSelectedPrefix.selected n k t i.val.1 i.val.2 then
        fixedWeight i * F (x (.inl ())).val (coordinateOld n k t ⟨i,x⟩) else 0 := by
  rw [seed_sum_eq_literal_coordinates]
  apply sum_congr rfl
  intro i hi
  rw [primeTuples,sum_filter]
  apply sum_congr rfl
  intro x hx
  have H := literal_iff_selected hN ht ht' hn i x
  by_cases hp : (x (.inl ())).val ∈ originalBand N k ∧
      ∀ j, (x j).val.Prime ∧ (x j).val.Coprime N
  all_goals
    by_cases hs : (fun j => physicalPrime N (x j).val) ∈
      P2FiniteMarkedGamma5RealSelectedPrefix.selected n k t i.val.1 i.val.2
    all_goals simp [H,hp,hs]

end
end ImbalancedChen.P2FiniteMarkedGamma5NativeSeedSum
