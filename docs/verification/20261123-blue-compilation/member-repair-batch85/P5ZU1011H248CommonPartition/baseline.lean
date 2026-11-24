import ImbalancedChen.P5ZU1011H248ClampPrimeBox
import ImbalancedChen.P5ZU1011AdaptivePrimeMeshError

/-!
Exact common H248 partition for the nonlinear finite minimum. Each policy
retains every open table atom, every marked knot and a zero-exterior
state. The common state is a function on the actual finite policy bank.
This partitions the ORIGINAL guarded finite minimum before it is summed,
rather than distributing a nonlinear minimum over a linear H lookup.

Knot 50 includes the entire clamp half-space L <= 2*w. No atom is deleted
as a null set. Eligibility and arbitrary tuple masks remain unchanged.
All statements are pointwise or finite exact identities; no table license,
Rosser estimate, AP bound or original full mean is assumed or proved.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011H248Partition

open Set
open Classical
open U11Integral U11H248 U1011H248Clamp U1011AdaptivePrimeError
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

noncomputable section

/-- `none` is the exact zero-exterior state, not an omitted boundary. -/
abbrev AtomState := Option FloorAtom

def scalarCell : AtomState → Set ℝ
  | none => {s | ∀ b : FloorAtom, max 2 s ∉ upperAtomSet b}
  | some b => {s | max 2 s ∈ upperAtomSet b}

def stateValue : AtomState → ℝ
  | none => 0
  | some b => floorAtomValue H248Numerators b

theorem scalarCell_unique {s : ℝ} {a b : AtomState}
    (ha : s ∈ scalarCell a) (hb : s ∈ scalarCell b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact (ha b hb).elim
  | some a =>
    cases b with
    | none => exact (hb a ha).elim
    | some b => exact congrArg some (upperAtom_unique ha hb)

theorem exists_scalarCell (s : ℝ) : ∃ a : AtomState, s ∈ scalarCell a := by
  by_cases h : ∃ b : FloorAtom, max 2 s ∈ upperAtomSet b
  · obtain ⟨b, hb⟩ := h
    exact ⟨some b, hb⟩
  · exact ⟨none, fun b hb => h ⟨b, hb⟩⟩

def chosenState (s : ℝ) : AtomState := Classical.choose (exists_scalarCell s)

theorem chosenState_mem (s : ℝ) : s ∈ scalarCell (chosenState s) :=
  Classical.choose_spec (exists_scalarCell s)

/-- Exact lookup on all states; the exterior has the literal zero value. -/
theorem H248_eq_stateValue {s : ℝ} {a : AtomState} (ha : s ∈ scalarCell a) :
    H248 (max 2 s) = stateValue a := by
  cases a with
  | none =>
    unfold H248 upperFloor stateValue
    apply Finset.sum_eq_zero
    intro b _
    exact indicator_of_notMem (ha b) _
  | some b => exact H248_eq_atom ha

/-- The serialized grid has no holes. A greatest grid point below the
query gives either its marked knot or its following open interval. -/
theorem exists_upperAtom_of_mem {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 5) :
    ∃ b : FloorAtom, s ∈ upperAtomSet b := by
  let J : Finset (Fin 201) := Finset.univ.filter (fun j => floorGrid j.val ≤ s)
  have hJ : J.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [floorGrid] using hs.1
  let j : Fin 201 := J.max' hJ
  have hj : j ∈ J := Finset.max'_mem J hJ
  have hjs : floorGrid j.val ≤ s := (Finset.mem_filter.mp hj).2
  by_cases heq : s = floorGrid j.val
  · exact ⟨.inr j, hs, heq⟩
  · have hjlt : j.val < 200 := by
      by_contra hn
      have hval : j.val = 200 := by omega
      have hgrid : floorGrid j.val = 5 := by rw [hval]; norm_num [floorGrid]
      rw [hgrid] at hjs
      exact heq (by rw [hgrid]; exact le_antisymm hs.2 hjs)
    let k : Fin 201 := ⟨j.val + 1, by omega⟩
    have hkn : k ∉ J := by
      intro hk
      have hle : k ≤ j := Finset.le_max' J k hk
      have hval : k.val ≤ j.val := hle
      dsimp [k] at hval
      omega
    have hupper : s < floorGrid (j.val + 1) := by
      by_contra hn
      have hk : k ∈ J := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, le_of_not_gt hn⟩
      exact hkn hk
    have hlower : floorGrid j.val < s := by
      by_contra hn
      exact heq (le_antisymm (le_of_not_gt hn) hjs)
    exact ⟨.inl ⟨j.val, hjlt⟩, hs, hlower, hupper⟩

/-- In particular the zero-exterior state is EXACTLY the query above
five. All queries below two belong to knot 50, rather than to exterior. -/
theorem mem_scalarCell_none_iff (s : ℝ) : s ∈ scalarCell none ↔ 5 < s := by
  constructor
  · intro hs
    by_contra hn
    have hquery : max 2 s ∈ Icc (1 : ℝ) 5 :=
      ⟨by linarith [le_max_left (2 : ℝ) s],
        max_le (by norm_num) (le_of_not_gt hn)⟩
    obtain ⟨b, hb⟩ := exists_upperAtom_of_mem hquery
    exact hs b hb
  · intro hs b hb
    have hle : max 2 s ≤ 5 := by cases b <;> exact hb.1.2
    linarith [le_max_right (2 : ℝ) s]

/-- The marked knot-50 state is a full half-space, not the equality L=2w. -/
theorem mem_scalarCell_clamp_iff (L w : ℝ) (hw : 0 < w) :
    L / w ∈ scalarCell (some (.inr clampKnot)) ↔ L ≤ 2 * w := by
  change (max 2 (L / w) ∈ Icc (1 : ℝ) 5 ∧
    max 2 (L / w) = floorGrid 50) ↔ _
  rw [floorGrid_fifty]
  constructor
  · intro h
    exact (div_le_iff₀ hw).1 ((le_max_right (2 : ℝ) (L / w)).trans_eq h.2)
  · intro h
    rw [max_eq_left ((div_le_iff₀ hw).2 h)]
    norm_num

/-- Every nonempty open state above the clamp is the exact affine
strict cell. Index 50 is the first open cell immediately above two. -/
theorem mem_scalarCell_open_iff (i : Fin 200) (hi : 50 ≤ i.val)
    (L w : ℝ) (hw : 0 < w) :
    L / w ∈ scalarCell (some (.inl i)) ↔
      floorGrid i.val * w < L ∧ L < floorGrid (i.val + 1) * w := by
  have hiR : (50 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hi
  have hiNat : i.val + 1 ≤ 200 := by omega
  have hiR' : (i.val : ℝ) + 1 ≤ 200 := by exact_mod_cast hiNat
  have h2 : (2 : ℝ) ≤ floorGrid i.val := by dsimp [floorGrid]; linarith
  have h5 : floorGrid (i.val + 1) ≤ 5 := by
    simp only [floorGrid, Nat.cast_add, Nat.cast_one]
    linarith
  constructor
  · intro hs
    change max 2 (L / w) ∈ Icc (1 : ℝ) 5 ∩
      Ioo (floorGrid i.val) (floorGrid (i.val + 1)) at hs
    have hlq : floorGrid i.val < L / w := by
      rcases lt_max_iff.mp hs.2.1 with hbad | hq
      · exact (not_lt_of_ge h2 hbad).elim
      · exact hq
    have hm : max 2 (L / w) = L / w := max_eq_right (h2.trans hlq.le)
    have huq : L / w < floorGrid (i.val + 1) := by
      simpa only [hm] using hs.2.2
    exact ⟨(lt_div_iff₀ hw).1 hlq, (div_lt_iff₀ hw).1 huq⟩
  · rintro ⟨hlo, hhi⟩
    have hlq := (lt_div_iff₀ hw).2 hlo
    have huq := (div_lt_iff₀ hw).2 hhi
    change max 2 (L / w) ∈ Icc (1 : ℝ) 5 ∩
      Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    rw [max_eq_right (h2.trans hlq.le)]
    exact ⟨⟨by linarith, huq.le.trans h5⟩, hlq, huq⟩

/-- Every marked knot above two, including the final knot 200, has
its literal affine equality pullback and keeps its adjacent-min value. -/
theorem mem_scalarCell_knot_iff (j : Fin 201) (hj : 50 < j.val)
    (L w : ℝ) (hw : 0 < w) :
    L / w ∈ scalarCell (some (.inr j)) ↔ L = floorGrid j.val * w := by
  have hjR : (50 : ℝ) < (j.val : ℝ) := by exact_mod_cast hj
  have hjNat : j.val ≤ 200 := by omega
  have hjR' : (j.val : ℝ) ≤ 200 := by exact_mod_cast hjNat
  have h2 : (2 : ℝ) < floorGrid j.val := by dsimp [floorGrid]; linarith
  have h5 : floorGrid j.val ≤ 5 := by dsimp [floorGrid]; linarith
  constructor
  · intro hs
    change max 2 (L / w) ∈ Icc (1 : ℝ) 5 ∧
      max 2 (L / w) = floorGrid j.val at hs
    have hq : 2 ≤ L / w := by
      by_contra hn
      have hm : max 2 (L / w) = 2 := max_eq_left (le_of_lt (lt_of_not_ge hn))
      have heq := hs.2
      rw [hm] at heq
      linarith
    have heq : L / w = floorGrid j.val := by
      simpa only [max_eq_right hq] using hs.2
    exact (div_eq_iff hw.ne').1 heq
  · intro hL
    have hq : L / w = floorGrid j.val := (div_eq_iff hw.ne').2 hL
    change max 2 (L / w) ∈ Icc (1 : ℝ) 5 ∧
      max 2 (L / w) = floorGrid j.val
    rw [hq, max_eq_right h2.le]
    exact ⟨⟨by linarith, h5⟩, rfl⟩

/-- Queries beyond the serialized upper endpoint retain an explicit
zero state. They are not silently assigned the last nonzero cell. -/
theorem mem_scalarCell_none_of_five_lt {s : ℝ} (hs : 5 < s) :
    s ∈ scalarCell none := by
  intro b hb
  have hle : max 2 s ≤ 5 := by cases b <;> exact hb.1.2
  linarith [le_max_right (2 : ℝ) s]

/-- Every policy gets its own exact table state on the COMMON partition. -/
abbrev CommonState (bank : Finset ℕ) := {j : ℕ // j ∈ bank} → AtomState

def commonCell (bank : Finset ℕ) (L : ℕ → LogFour → ℝ)
    (sigma : CommonState bank) : Set LogFour :=
  {v | ∀ j : {j : ℕ // j ∈ bank}, L j.val v / v 3 ∈ scalarCell (sigma j)}

def commonState (bank : Finset ℕ) (L : ℕ → LogFour → ℝ) (v : LogFour) :
    CommonState bank := fun j => chosenState (L j.val v / v 3)

theorem commonState_mem (bank : Finset ℕ) (L : ℕ → LogFour → ℝ) (v : LogFour) :
    v ∈ commonCell bank L (commonState bank L v) := fun _ => chosenState_mem _

theorem commonCell_unique {bank : Finset ℕ} {L : ℕ → LogFour → ℝ}
    {v : LogFour} {sigma tau : CommonState bank}
    (hsigma : v ∈ commonCell bank L sigma) (htau : v ∈ commonCell bank L tau) :
    sigma = tau := by
  funext j
  exact scalarCell_unique (hsigma j) (htau j)

theorem commonCells_disjoint {bank : Finset ℕ} {L : ℕ → LogFour → ℝ}
    {sigma tau : CommonState bank} (hne : sigma ≠ tau) :
    Disjoint (commonCell bank L sigma) (commonCell bank L tau) := by
  exact Set.disjoint_left.mpr (fun _ hs ht => hne (commonCell_unique hs ht))

/-- The complete finite common partition covers every point, with no
positivity or upper-query assumption and with every zero-exterior state. -/
theorem iUnion_commonCell (bank : Finset ℕ) (L : ℕ → LogFour → ℝ) :
    (⋃ sigma : CommonState bank, commonCell bank L sigma) = Set.univ := by
  ext v
  constructor
  · intro _
    exact Set.mem_univ v
  · intro _
    exact Set.mem_iUnion.mpr ⟨commonState bank L v, commonState_mem bank L v⟩

/-- A state formula changes the H lookup only. The actual residual
and original eligibility predicates are left at their original point. -/
def stateOrdinary (bank : Finset ℕ) (L : ℕ → LogFour → ℝ)
    (sigma : CommonState bank) (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j ∈ bank then 4 * (1 - stateValue (sigma ⟨j, hj⟩)) / L j v else 0

theorem ordinary_eq_state {bank : Finset ℕ} {L : ℕ → LogFour → ℝ}
    {sigma : CommonState bank} {v : LogFour} (hv : v ∈ commonCell bank L sigma)
    (j : ℕ) (hj : j ∈ bank) :
    ordinaryKernel H248 L j v = stateOrdinary bank L sigma j v := by
  unfold ordinaryKernel stateOrdinary
  rw [dif_pos hj, H248_eq_stateValue (hv ⟨j, hj⟩)]

/-- Each guarded candidate agrees on the common state; ineligible
policies still use the same switched fallback. -/
theorem guarded_eq_state {bank : Finset ℕ} {L : ℕ → LogFour → ℝ}
    {sigma : CommonState bank} {v : LogFour} (hv : v ∈ commonCell bank L sigma)
    (eligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ)
    (c : ℕ) (hc : c ∈ tags bank) :
    guarded eligible switched (ordinaryKernel H248 L) c v =
      guarded eligible switched (stateOrdinary bank L sigma) c v := by
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simp only [guarded, if_pos rfl]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    by_cases helig : eligible j v
    · simpa [guarded, helig] using ordinary_eq_state hv j hj
    · simp [guarded, helig]

theorem envelope_eq_state {bank : Finset ℕ} {L : ℕ → LogFour → ℝ}
    {sigma : CommonState bank} {v : LogFour} (hv : v ∈ commonCell bank L sigma)
    (eligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ) :
    envelope bank (guarded eligible switched (ordinaryKernel H248 L)) v =
      envelope bank (guarded eligible switched (stateOrdinary bank L sigma)) v := by
  have h := envelope_abs_sub_le bank
    (guarded eligible switched (ordinaryKernel H248 L))
    (guarded eligible switched (stateOrdinary bank L sigma)) v 0 (fun c hc => by
      rw [guarded_eq_state hv eligible switched c hc]
      simp)
  have heq := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  linarith

/-- Nonlinear finite minimum decomposed on ONE common finite partition.
The original H248 value and every marked knot are retained exactly. -/
theorem minimum_eq_sum_states (bank : Finset ℕ) (L : ℕ → LogFour → ℝ)
    (eligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ) (v : LogFour) :
    envelope bank (guarded eligible switched (ordinaryKernel H248 L)) v =
      ∑ sigma : CommonState bank, (commonCell bank L sigma).indicator
        (envelope bank (guarded eligible switched (stateOrdinary bank L sigma))) v := by
  symm
  calc
    _ = (commonCell bank L (commonState bank L v)).indicator
        (envelope bank (guarded eligible switched
          (stateOrdinary bank L (commonState bank L v)))) v := by
      apply Finset.sum_eq_single (commonState bank L v)
      · intro sigma _ hne
        exact indicator_of_notMem
          (fun hs => hne (commonCell_unique hs (commonState_mem bank L v))) _
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by
      rw [indicator_of_mem (commonState_mem bank L v)]
      exact (envelope_eq_state (commonState_mem bank L v) eligible switched).symm

/-- A signed weight, including any keep indicator, is retained pointwise. -/
theorem weighted_minimum_eq_sum_states (bank : Finset ℕ) (L : ℕ → LogFour → ℝ)
    (eligible : ℕ → LogFour → Prop) (switched W : LogFour → ℝ) (v : LogFour) :
    envelope bank (guarded eligible switched (ordinaryKernel H248 L)) v * W v =
      ∑ sigma : CommonState bank, (commonCell bank L sigma).indicator
        (fun x => envelope bank (guarded eligible switched
          (stateOrdinary bank L sigma)) x * W x) v := by
  rw [minimum_eq_sum_states bank L eligible switched v, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro sigma _
  by_cases hv : v ∈ commonCell bank L sigma <;> simp [hv]

private theorem masked_weighted_minimum_eq_sum_states
    (bank : Finset ℕ) (L : ℕ → LogFour → ℝ)
    (eligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ)
    (v : LogFour) (weight : ℝ) (keep : Prop) :
    (if keep then weight * envelope bank
        (guarded eligible switched (ordinaryKernel H248 L)) v else 0) =
      ∑ sigma : CommonState bank, if keep ∧ v ∈ commonCell bank L sigma then
        weight * envelope bank (guarded eligible switched
          (stateOrdinary bank L sigma)) v else 0 := by
  by_cases hk : keep
  · simp only [hk, true_and, if_true]
    rw [minimum_eq_sum_states bank L eligible switched v, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    by_cases hv : v ∈ commonCell bank L sigma <;> simp [hv]
  · simp [hk]

/-- Exact actual-prime accounting with arbitrary tuple-dependent keep
masks. The same mask occurs inside every common atom; no mask is frozen
or replaced by a constant, and no alternative is added on an overlap. -/
theorem actual_masked_minimum_eq_sum_states (N : ℕ) (a b : Fin 4 → ℝ)
    (keep : (Fin 4 → ℕ) → Prop) (bank : Finset ℕ)
    (L : ℕ → LogFour → ℝ) (eligible : ℕ → LogFour → Prop)
    (switched : LogFour → ℝ) :
    maskedTestSum N a b keep
        (envelope bank (guarded eligible switched (ordinaryKernel H248 L))) =
      ∑ sigma : CommonState bank,
        maskedTestSum N a b
          (fun p => keep p ∧ actualPrimeTupleLog N p ∈ commonCell bank L sigma)
          (envelope bank (guarded eligible switched (stateOrdinary bank L sigma))) := by
  unfold maskedTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact masked_weighted_minimum_eq_sum_states bank L eligible switched
    (actualPrimeTupleLog N p) (∏ i, 1 / ((p i : ℝ) - 1)) (keep p)

end

end ImbalancedChen.P5Z.U1011H248Partition
