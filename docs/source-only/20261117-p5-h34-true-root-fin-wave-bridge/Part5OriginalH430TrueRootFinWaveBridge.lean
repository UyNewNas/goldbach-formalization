import ImbalancedChen.Part5OriginalH430PositivePhysicalSourcePartition

/-!
P5.6 h34: finite genuine rootHistory-to-Fin bridge. Every original
list occurrence, its path mark and its scalar/specified-cell Request
is preserved. Zero-generation seed is not charged as another 430 stage.
The resulting explicit root bound still needs quantitative Buchstab and
bank payments and original U3/U4 arithmetic ownership.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TrueRootFinWaveBridge
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430ActualRequestAllActionWave
open Part5OriginalH430WeightedPhysicalTelescope
open Part5OriginalH430PositivePhysicalSourcePartition

/-- Repeated list positions remain distinct when summing over Fin. -/
private theorem sum_get_map {α : Type*} (xs : List α) (f : α → ℝ) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa [Fin.sum_univ_succ] using
        congrArg (fun t : ℝ => f x + t) ih

private theorem sum_filter_ite {α : Type*} (xs : List α)
    (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    ((xs.filter (fun x => decide (P x))).map f).sum =
      (xs.map (fun x => if P x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : P x <;> simp [hx, ih]

private theorem sum_map_congr {α : Type*} (xs : List α)
    (f h : α → ℝ) :
    (∀ x ∈ xs, f x = h x) →
      (xs.map f).sum = (xs.map h).sum := by
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro heq
      simp only [List.map_cons, List.sum_cons]
      rw [heq x (by simp)]
      exact congrArg (fun t : ℝ => h x + t)
        (ih (by
          intro y hy
          exact heq y (by simp [hy])))

private theorem sum_fin_list_comm {α : Type*} (xs : List α)
    (F : Fin 430 → α → ℝ) :
    (∑ g : Fin 430, (xs.map (F g)).sum) =
      (xs.map (fun x => ∑ g : Fin 430, F g x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- Exact same-root, fixed-generation Fin slice of the actual selected
history. In particular the level's Fin position is not a product owner. -/
theorem root_wave_level_slice
    (N n : ℕ) (root : Root) (tau : ℝ) (p generation : ℕ)
    (F : Request → ℝ) :
    (∑ l : LevelIndex N n root tau p generation,
      levelMark l * F (levelOccurrence l).current) =
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (fun j s => if j = generation then F s else 0) := by
  let f : Occurrence N → ℝ := fun o => mark o * F o.current
  have hf :
      (∑ l : LevelIndex N n root tau p generation,
        levelMark l * F (levelOccurrence l).current) =
      ((levelRequests N n root tau p generation).map f).sum := by
    change (∑ l : Fin (levelRequests N n root tau p generation).length,
      f ((levelRequests N n root tau p generation).get l)) = _
    exact sum_get_map _ _
  calc
    _ = ((levelRequests N n root tau p generation).map f).sum := hf
    _ = ((rootHistory N n root tau p).map
        (fun o => if o.remaining = generation then f o else 0)).sum := by
          simpa only [levelRequests] using
            (sum_filter_ite (rootHistory N n root tau p)
              (fun o => o.remaining = generation) f)
    _ = waveAccount N (rootQ N n root tau p) 430
          (rootRequest N n root tau p)
          (fun j s => if j = generation then F s else 0) := by
            simp [waveAccount, rootHistory, f, mul_ite]

/-- Exact 430-stage partition of a wave whose zero-generation charge
vanishes. The only reindexing key is o.remaining, proved <=430. -/
private theorem time_slice_partition
    (V : ℕ → Request → ℝ) (hzero : ∀ s, V 0 s = 0)
    (j : ℕ) (hj : j ≤ 430) (s : Request) :
    V j s =
      ∑ g : Fin 430, if j = g.val+1 then V j s else 0 := by
  cases j with
  | zero => simp [hzero s]
  | succ k =>
      have hk : k < 430 := by omega
      symm
      calc
        (∑ g : Fin 430, if k+1 = g.val+1 then V (k+1) s else 0) =
          (if k+1 = (⟨k,hk⟩ : Fin 430).val+1
            then V (k+1) s else 0) := by
              apply Finset.sum_eq_single (⟨k,hk⟩ : Fin 430)
              · intro b hb hne
                have hn : k+1 ≠ b.val+1 := by
                  intro heq
                  apply hne
                  apply Fin.ext
                  omega
                simp [hn]
              · intro hn
                exact (hn (Finset.mem_univ _)).elim
        _ = V (k+1) s := by simp

private theorem wave_zero_free_sum_430
    (N : ℕ) (Q : ℝ) (r : Request)
    (V : ℕ → Request → ℝ) (hzero : ∀ s, V 0 s = 0) :
    waveAccount N Q 430 r V =
      ∑ g : Fin 430,
        waveAccount N Q 430 r
          (fun j s => if j = g.val+1 then V j s else 0) := by
  let xs := history N Q 430 r
  have hbound (o : Occurrence N) (ho : o ∈ xs) : o.remaining ≤ 430 := by
    have hh := (history_facts ho).2.1
    omega
  have hpoint (o : Occurrence N) (ho : o ∈ xs) :
      mark o * V o.remaining o.current =
      ∑ g : Fin 430, mark o * (if o.remaining = g.val+1
        then V o.remaining o.current else 0) := by
    calc
      _ = mark o * (∑ g : Fin 430,
          if o.remaining = g.val+1
            then V o.remaining o.current else 0) := by
              rw [time_slice_partition V hzero o.remaining
                (hbound o ho) o.current]
      _ = _ := by rw [Finset.mul_sum]
  calc
    waveAccount N Q 430 r V =
      (xs.map (fun o => mark o * V o.remaining o.current)).sum := rfl
    _ = (xs.map (fun o => ∑ g : Fin 430,
        mark o * (if o.remaining = g.val+1
          then V o.remaining o.current else 0))).sum :=
            sum_map_congr xs _ _ hpoint
    _ = ∑ g : Fin 430,
        (xs.map (fun o => mark o * (if o.remaining = g.val+1
          then V o.remaining o.current else 0))).sum := by
            symm
            exact sum_fin_list_comm xs (fun g o =>
              mark o * (if o.remaining = g.val+1
                then V o.remaining o.current else 0))
    _ = _ := rfl

/-- Previously separate root physical wave and 430 genuine Fin levels
now have exactly the same occurrences, marks, generation and same Q. -/
theorem physical_source_root_wave_eq_430_fin
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (positivePhysicalSource N (rootQ N n root tau p)) =
    ∑ g : Fin 430, fullPhysicalSource N n root tau p g := by
  let Q := rootQ N n root tau p
  have hz : ∀ s, positivePhysicalSource N Q 0 s = 0 := by
    intro s
    simp [positivePhysicalSource, physicalDefectAt]
  calc
    _ = ∑ g : Fin 430,
      waveAccount N Q 430 (rootRequest N n root tau p)
        (fun j s => if j = g.val+1
          then positivePhysicalSource N Q j s else 0) :=
            wave_zero_free_sum_430 N Q (rootRequest N n root tau p)
              (positivePhysicalSource N Q) hz
    _ = ∑ g : Fin 430, fullPhysicalSource N n root tau p g := by
      apply Finset.sum_congr rfl
      intro g _
      have hfun :
          (fun j s => if j = g.val+1 then positivePhysicalSource N Q j s else 0) =
          (fun j s => if j = g.val+1
            then positivePhysicalSource N Q (g.val+1) s else 0) := by
        funext j s
        by_cases hj : j = g.val+1
        · subst j
          simp
        · simp [hj]
      rw [hfun]
      simpa [fullPhysicalSource, Index] using
        (root_wave_level_slice N n root tau p (g.val+1)
          (fun s => positivePhysicalSource N Q (g.val+1) s)).symm

/-- The actual selected action partition consumes only strict-prime
Buchstab and the winning original 106-bank positions at each stage. -/
theorem physical_source_root_wave_eq_buchstab_bank
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (positivePhysicalSource N (rootQ N n root tau p)) =
    ∑ g : Fin 430,
      (buchstabPhysicalSource N n root tau p g +
        bankPhysicalSource N n root tau p g) := by
  rw [physical_source_root_wave_eq_430_fin]
  apply Finset.sum_congr rfl
  intro g _
  exact full_physical_source_eq_buchstab_plus_bank N n root tau p g

/-- The terminal seed is the REAL generation-zero Fin list, not a
wrapped predecessor or an extra positive stage. -/
theorem positive_weighted_seed_eq_generation_zero_fin
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (fun j s => max 0 (weightedSeed N (rootQ N n root tau p) j s)) =
    ∑ l : LevelIndex N n root tau p 0,
      levelMark l *
        max 0 (weightedRequest N (rootQ N n root tau p) 0
          (levelOccurrence l).current) := by
  let Q := rootQ N n root tau p
  have hfun :
      (fun j s => max 0 (weightedSeed N Q j s)) =
      (fun j s => if j = 0 then max 0 (weightedRequest N Q 0 s) else 0) := by
    funext j s
    cases j <;> simp [weightedSeed]
  rw [hfun]
  exact (root_wave_level_slice N n root tau p 0
    (fun s => max 0 (weightedRequest N Q 0 s))).symm

/-- Concrete same-root one-sided payment ledger in actual Fin owners,
without any unproved claim that the two positive sources are small or
that the original U3/U4 count source equals these request values. -/
theorem frozen_root_430_le_actual_fin_payments
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    weightedRequest N (rootQ N n root tau p) 430
      (rootRequest N n root tau p) ≤
    (∑ l : LevelIndex N n root tau p 0,
      levelMark l *
        max 0 (weightedRequest N (rootQ N n root tau p) 0
          (levelOccurrence l).current)) +
    ∑ g : Fin 430,
      (buchstabPhysicalSource N n root tau p g +
        bankPhysicalSource N n root tau p g) := by
  have h := frozen_root_430_le_positive_physical_source N n root tau p
  rw [positive_weighted_seed_eq_generation_zero_fin,
    physical_source_root_wave_eq_buchstab_bank] at h
  exact h

end
end ImbalancedChen.Part5OriginalH430TrueRootFinWaveBridge
