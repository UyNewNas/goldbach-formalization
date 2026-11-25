import ImbalancedChen.P2FiniteMarkedGamma5ActualHistoryScale
import ImbalancedChen.P2FiniteMarkedGamma5InnerComparison
import ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount
import ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount

namespace ImbalancedChen.P2FiniteMarkedGamma5ActualProperPayment
noncomputable section
open Filter Finset Real
open Part5OriginalH430FrozenRootRefinement (RootCode frozenLeafCutoffFloor)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430SameQHistoryCells (cellQ)
open P2FiniteMarkedGamma5ActualRootCells
open P2FiniteMarkedGamma5ActualRadialAggregate
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos)
open P2FiniteMarkedGamma5RadialRoughMass (cut norm eventually_cut_le_half_floor)
open P2FiniteMarkedGamma5SharpTupleCount (Tuple)
open P2FiniteMarkedGamma5InnerComparison (properStripTuples)
open scoped Classical BigOperators Topology

/-- A tuple determines its full old word. Keep it only if that word has
positive total selected mark in the same cell. -/
private def supported (N n dep : ℕ) (t h : ℝ) (c : RootCode n) (s : Split)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : Finset (Tuple N s) :=
  (Part3.labelledPrimeTuples (s.1.val + (2+s.2.val)) (2*N)).filter fun v =>
    v ∈ properStripTuples N (cellQ N n c) h (tuplePrefix (tupleValues v)) s ∧
      prefixWeight N n dep t c B (tuplePrefix (tupleValues v)) ≠ 0

private theorem cell_exponent {n : ℕ} (c : RootCode n) :
    ∃ ν : ℝ, ∀ N : ℕ, 2 ≤ N → log (cellQ N n c) / log (N : ℝ) = ν := by
  refine ⟨_, ?_⟩
  intro N hN
  have h1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  unfold cellQ
  rw [log_rpow (zero_lt_one.trans h1), mul_div_cancel_right₀ _ (log_pos h1).ne']

private theorem width_le_one {h : ℝ} (hh : 0 < h) (h8 : h ≤ 1/8) :
    radialWidth h ≤ 1 := by
  unfold radialWidth
  have := Real.log_le_sub_one_of_pos (show 0 < 1+h by linarith)
  linarith

/-- The reindexing uses the original full coordinate order. -/
private def renumber {N : ℕ} {s : Split} (v : Tuple N s) :
    P2FiniteMarkedGamma5NonemptyTailWallCount.Tuple N s.1.val s.2.val :=
  fun i => v (Fin.cast (by omega) i)

private theorem renumber_injective {N : ℕ} {s : Split} :
    Function.Injective (@renumber N s) := by
  intro v u h
  funext i
  exact congrFun h (Fin.cast (by omega) i)

private theorem nonempty_card {N n dep : ℕ} {t h : ℝ} {c : RootCode n} {s : Split}
    {B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)}
    (hN : 2 ≤ N) (hh : 0 < h) (hcut : cut N ≤ (N : ℝ)^frozenLeafCutoffFloor/2) :
    (supported N n dep t h c s B).card ≤
      (P2FiniteMarkedGamma5NonemptyTailWallCount.properTuples N s.1.val s.2.val
        (cellQ N n c) (radialWidth h)).card := by
  refine card_le_card_of_injOn renumber ?_ (fun _ _ _ _ he => renumber_injective he)
  intro v hv
  obtain ⟨hvprime, hvstrip, _⟩ := mem_filter.mp hv
  obtain ⟨_, _, _, hne, hcap, hcop, hstrip⟩ := mem_filter.mp hvstrip
  have h0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  obtain ⟨hfloor, _⟩ := P2FiniteMarkedGamma5IntegerSupport.finPhysicalProfile_nonzero_support
    (rpow_pos_of_pos h0 _) h0 (radialWidth_pos hh) hne
  have hprime : renumber v ∈ Part3.labelledPrimeTuples _ (2*N) := by
    refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
    exact (mem_filter.mp hvprime).2 (Fin.cast (by omega) i)
  have heq : Part3.labelledProduct (renumber v) = Part3.labelledProduct v := by
    unfold Part3.labelledProduct renumber
    exact Fintype.prod_equiv (finCongr (by omega)) _ _ (fun _ => rfl)
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hprime, fun i => hcut.trans (hfloor _).le, ?_, ?_⟩, ?_⟩
  · rw [heq]
    have : Part3.labelledProduct v ≤ N := by exact_mod_cast hcap
    omega
  · simpa only [heq] using hcop
  · exact hstrip

private theorem unit_card {N n dep : ℕ} {t h : ℝ} {c : RootCode n}
    (j : Fin (P2FiniteMarkedGamma5ActualRank.frozenSourceRankBound+1))
    {B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)}
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12) :
    (supported N n dep t h c (j,0) B).card ≤
      (P2FiniteMarkedGamma5UnitTailCount.unitTuples N j.val (cellQ N n c) (radialWidth h)).card := by
  apply card_le_card
  intro v hv
  obtain ⟨hp, hvstrip, hw⟩ := mem_filter.mp hv
  obtain ⟨_, _, _, hne, _⟩ := mem_filter.mp hvstrip
  obtain ⟨_, hf, _, hs⟩ :=
    P2FiniteMarkedGamma5ActualHistoryScale.of_prefixWeight_ne_zero hn hN ht ht' hw
  have hd : P2FiniteMarkedGamma5UnitTailCount.oldProduct v =
      ((tuplePrefix (tupleValues v)).prod : ℝ) := by
    change (∏ i : Fin j.val, ((v (i.castAdd (2+0))).val : ℝ)) = _
    simp only [tuplePrefix, tupleValues, List.prod_ofFn, Nat.cast_prod]
  exact mem_filter.mpr ⟨hp, hne, by simpa only [hd] using hf, by simpa only [hd] using hs⟩

private theorem occurrence_rearrange {N n dep : ℕ} {t h : ℝ} (c : RootCode n)
    (s : Split) (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    (∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p, levelMark l *
      ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ)) =
    ∑ v ∈ supported N n dep t h c s B,
      prefixWeight N n dep t c B (tuplePrefix (tupleValues v)) := by
  let A := Part3.labelledPrimeTuples (s.1.val+(2+s.2.val)) (2*N)
  let T := properStripTuples N (cellQ N n c) h
  have H (w : List ℕ) :
      ((T w s).card : ℝ) = ∑ v ∈ A, if v ∈ T w s then (1:ℝ) else 0 := by
    have he : A.filter (fun v => v ∈ T w s) = T w s := by
      ext v
      exact mem_filter.trans ⟨And.right, fun hv => ⟨(mem_filter.mp hv).1, hv⟩⟩
    rw [← sum_filter, he]
    simp
  change (∑ p ∈ _, ∑ l ∈ B p, levelMark l * ((T _ s).card : ℝ)) = _
  simp_rw [H, mul_sum]
  calc
    _ = ∑ p ∈ _, ∑ v ∈ A, ∑ l ∈ B p, levelMark l *
          (if v ∈ T (levelOccurrence l).current.old s then 1 else 0) :=
      sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ v ∈ A, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
          levelMark l * (if v ∈ T (levelOccurrence l).current.old s then 1 else 0) := sum_comm
    _ = _ := by
      unfold supported
      rw [sum_filter]
      apply sum_congr rfl
      intro v hv
      let w := tuplePrefix (tupleValues v)
      have hm (u : List ℕ) : v ∈ T u s ↔ u = w ∧ v ∈ T w s := by
        constructor
        · intro hmem
          have hu : u = w := (mem_filter.mp hmem).2.2.1
          exact ⟨hu, hu ▸ hmem⟩
        · rintro ⟨rfl, hmem⟩
          exact hmem
      by_cases hmem : v ∈ T w s
      · have hx : (∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
            levelMark l * (if v ∈ T (levelOccurrence l).current.old s then 1 else 0)) =
          prefixWeight N n dep t c B w := by
          unfold prefixWeight
          apply sum_congr rfl
          intro p hp
          apply sum_congr rfl
          intro l hl
          by_cases he : (levelOccurrence l).current.old = w <;> simp [hm _, he, hmem]
        rw [hx]
        change prefixWeight N n dep t c B w = if v ∈ T w s ∧ prefixWeight N n dep t c B w ≠ 0 then _ else _
        by_cases hz : prefixWeight N n dep t c B w = 0 <;> simp [hmem, hz]
      · have hx (u : List ℕ) : v ∉ T u s := fun hu => hmem ((hm u).mp hu).2
        simp only [if_neg (hx _), mul_zero, sum_const_zero]
        change 0 = if v ∈ T w s ∧ _ then _ else _
        simp [hmem]

private theorem split_payment (n : ℕ) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (c : RootCode n) (s : Split) {e : ℝ} (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, ∀ (dep : ℕ) (t h : ℝ), 0 ≤ t → t ≤ 1/12 →
      0 < h → h ≤ 1/8 → ∀ B, norm N * ((supported N n dep t h c s B).card : ℝ) ≤ e := by
  by_cases ha : admissibleSplit s
  · by_cases hr : 0 < s.2.val
    · obtain ⟨ν,hν⟩ := cell_exponent c
      filter_upwards [P2FiniteMarkedGamma5NonemptyTailWallCount.eventually_properTuples_payment
        s.1.val s.2.val hr ν he, eventually_cut_le_half_floor, eventually_ge_atTop (2:ℕ)]
        with N hpaid hcut hN
      intro dep t h _ _ hh h8 B
      have h1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      have hnorm : 0 ≤ norm N := div_nonneg (log_pos h1).le (by linarith)
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (nonempty_card hN hh hcut)) hnorm).trans
        (hpaid _ _ (hν N hN) (radialWidth_pos hh) (width_le_one hh h8))
    · obtain ⟨j,r⟩ := s
      have hz : r = 0 := Fin.ext (by change r.val = 0; simpa using Nat.eq_zero_of_not_pos hr)
      subst r
      filter_upwards [P2FiniteMarkedGamma5UnitTailCount.eventually_unitTuples_payment he,
        eventually_ge_atTop (2:ℕ)] with N hpaid hN
      intro dep t h ht ht' hh h8 B
      have h1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      have hnorm : 0 ≤ norm N := div_nonneg (log_pos h1).le (by linarith)
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (unit_card j hn hN ht ht')) hnorm).trans
        (hpaid _ _ j.val (radialWidth_pos hh) (width_le_one hh h8) (by simpa [admissibleSplit] using ha))
  · filter_upwards with N
    intro dep t h ht ht' hh h8 B
    have hem : supported N n dep t h c s B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact ha (mem_filter.mp (mem_filter.mp hv).2.1).2.1
    simpa [hem] using he.le

/-- One threshold at fixed n pays every selected level family, every
allowed root parameter and every allowed physical smoothing parameter. -/
theorem absolute_cell_proper_payment (n : ℕ) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (dep : ℕ) (t h : ℝ), 0 ≤ t → t ≤ 1/12 →
      0 < h → h ≤ 1/8 → ∀ (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)),
      norm N * (∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B p, levelMark l * ∑ s : Split,
          ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ))
        ≤ ε := by
  let e := ε / ((aggregateCard n : ℝ)+1)
  have he' : 0 < e := div_pos he (by positivity)
  have H : ∀ᶠ N : ℕ in atTop, ∀ c : RootCode n, ∀ s : Split,
      ∀ (dep : ℕ) (t h : ℝ), 0 ≤ t → t ≤ 1/12 → 0 < h → h ≤ 1/8 →
      ∀ B, norm N * ((supported N n dep t h c s B).card : ℝ) ≤ e :=
    eventually_all.mpr (fun c => eventually_all.mpr (fun s => split_payment n hn c s he'))
  filter_upwards [H, eventually_ge_atTop (2:ℕ)] with N hpaid hN
  intro dep t h ht ht' hh h8 B
  have h1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hnorm : 0 ≤ norm N := div_nonneg (log_pos h1).le (by linarith)
  have Hc (c : RootCode n) :
      (∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p, levelMark l * ∑ s : Split,
        ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ)) =
      ∑ s : Split, ∑ v ∈ supported N n dep t h c s B,
        prefixWeight N n dep t c B (tuplePrefix (tupleValues v)) := by
    simp_rw [mul_sum]
    calc
      _ = ∑ p ∈ _, ∑ s : Split, ∑ l ∈ B p, levelMark l *
            ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ) :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = ∑ s : Split, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p, levelMark l *
            ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ) := sum_comm
      _ = _ := sum_congr rfl (fun s _ => occurrence_rearrange c s B)
  simp_rw [Hc, mul_sum]
  calc
    _ ≤ ∑ _c : RootCode n, ∑ _s : Split, (shapeWords.card : ℝ) * e := by
      apply sum_le_sum
      intro c hc
      apply sum_le_sum
      intro s hs
      calc
        _ ≤ ∑ _v ∈ supported N n dep t h c s B, norm N * (shapeWords.card : ℝ) :=
          sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
            (prefixWeight_le_shapeCard N n dep t c B (tuplePrefix (tupleValues v))) hnorm)
        _ = (shapeWords.card : ℝ) * (norm N * ((supported N n dep t h c s B).card : ℝ)) := by
          simp only [sum_const, nsmul_eq_mul]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpaid c s dep t h ht ht' hh h8 B) (Nat.cast_nonneg _)
    _ = (aggregateCard n : ℝ) * e := by
      simp only [sum_const, card_univ, nsmul_eq_mul, aggregateCard, Nat.cast_mul]
      ring
    _ ≤ ((aggregateCard n : ℝ)+1) * e := mul_le_mul_of_nonneg_right (by linarith) he'.le
    _ = ε := by dsimp [e]; field_simp [show ((aggregateCard n : ℝ)+1) ≠ 0 by positivity]

theorem absolute_all_depth_cell_proper_payment (n : ℕ) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (t h : ℝ), 0 ≤ t → t ≤ 1/12 → 0 < h → h ≤ 1/8 →
      ∀ (B : (dep : Fin 431) → (p : ℕ) → Finset (LevelIndex N n .U4 t p dep.val)),
      norm N * (∑ dep : Fin 431, ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B dep p, levelMark l * ∑ s : Split,
          ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ))
        ≤ ε := by
  filter_upwards [absolute_cell_proper_payment n hn (div_pos he (by norm_num : (0:ℝ)<431))]
    with N hpaid
  intro t h ht ht' hh h8 B
  rw [mul_sum]
  calc
    _ ≤ ∑ _dep : Fin 431, ε / 431 :=
      sum_le_sum (fun dep _ => hpaid dep.val t h ht ht' hh h8 (B dep))
    _ = ε := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualProperPayment
