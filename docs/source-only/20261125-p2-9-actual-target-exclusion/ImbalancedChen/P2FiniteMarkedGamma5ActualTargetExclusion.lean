import ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate
import ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The target-noncoprime part of the same bounded physical-profile sum on
the original U4 selected-history positions. The original root prime,
dependent B p, positive levelMark, complete old prefix and all tuple
coordinates remain literal. The previously proved prefix coefficient
bound is used before the fixed RootCode and split factors are paid.

The ordinary exception count is the existing actual-cutoff all-rank
noncoprimeCount. Its eventual bound is uniform in every allowed physical
width, root parameter and selected subfamily. The final fixed sum over
Fin 431 retains all original remaining-depth choices. This is a discrete
marked-profile deletion, not an ordinaryBad/J identification or a smooth
realization of the selected-history masks.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualTargetExclusion
noncomputable section
open Filter Finset Real
open Part5OriginalH430FrozenRootRefinement (RootCode frozenLeafCutoffFloor)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430SameQHistoryCells (cellQ)
open P2FiniteMarkedGamma5ActualRootCells
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5PhysicalExtension (physicalProfile_bounds)
open P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile finToPhysical)
open P2FiniteMarkedGamma5IntegerSupport (finPhysicalProfile_nonzero_support)
open P2FiniteMarkedGamma5RadialRoughMass (cut eventually_cut_le_half_floor)
open P2FiniteMarkedGamma5RadialProfileCollar
  (radialWidth radialWidth_pos exp_radialWidth_lt_two)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5ActualRadialAggregate
  (Split admissibleSplit tuplePrefix boundedProfileWeight
    prefixWeight prefixWeight_le_shapeCard shapeWords aggregateCard)
open P2FiniteMarkedGamma5TargetExclusion
  (noncoprimeTuples noncoprimeCount rank_card_le_noncoprimeCount
    absolute_noncoprime_payment)
open scoped Classical Topology BigOperators

/-- The target-noncoprime nonzero support of the unchanged profile, on
the same ordered-prime enumerator as boundedProfileWeight. -/
def profileNoncoprimeTuples (N k r : ℕ) (logQ h : ℝ) :
    Finset (Fin (k + (2 + r)) → Fin (2 * N + 1)) :=
  (Part3.labelledPrimeTuples (k + (2 + r)) (2 * N)).filter (fun v =>
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ)) ≠ 0 ∧
      ¬ Nat.Coprime (Part3.labelledProduct v) N)

def profileNoncoprimeMass (N k r : ℕ) (logQ h : ℝ) : ℝ :=
  ∑ v ∈ profileNoncoprimeTuples N k r logQ h,
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ))

/-- A literal restriction of the previously defined marked-prefix
weight. Zero terms are retained in this original bounded sum. -/
def noncoprimeSlice (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) : ℝ :=
  ∑ v ∈ Part3.labelledPrimeTuples (k + (2 + r)) (2 * N),
    if Nat.Coprime (Part3.labelledProduct v) N then 0
    else boundedProfileWeight N k r logQ h old v

theorem noncoprimeSlice_eq_filtered (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) :
    noncoprimeSlice N k r logQ h old =
      ∑ v ∈ profileNoncoprimeTuples N k r logQ h,
        boundedProfileWeight N k r logQ h old v := by
  unfold noncoprimeSlice profileNoncoprimeTuples
  rw [sum_filter]
  apply sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime (Part3.labelledProduct v) N
  · simp [hc]
  · by_cases hz : finPhysicalProfile logQ (N : ℝ) (radialWidth h)
        ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ)) = 0
    · simp [hc, hz, boundedProfileWeight]
    · simp [hc, hz]

/-- The actual profile supplies both its prime floor and its complete
product cap. No new support hypothesis is assumed for its coordinates. -/
theorem profile_noncoprime_subset {N k r : ℕ} {logQ h : ℝ}
    (hN : 0 < N) (hp : 0 < h) (h8 : h ≤ 1 / 8)
    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2) :
    profileNoncoprimeTuples N k r logQ h ⊆
      noncoprimeTuples N (k + (2 + r)) := by
  intro v hv
  obtain ⟨hprime, hne, hcop⟩ := mem_filter.mp hv
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hfloor, hcap⟩ := finPhysicalProfile_nonzero_support
    (rpow_pos_of_pos hN0 frozenLeafCutoffFloor) hN0 (radialWidth_pos hp) hne
  have hcap' : (Part3.labelledProduct v : ℝ) < 2 * (N : ℝ) := by
    simpa only [Part3.labelledProduct, Nat.cast_prod] using
      hcap.trans (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hp h8) hN0)
  exact mem_filter.mpr
    ⟨hprime, (fun i => hcut.trans (hfloor i).le), hcap'.le, hcop⟩

theorem profileNoncoprimeMass_le_count {N k r : ℕ} {logQ h : ℝ}
    (hN : 0 < N) (hp : 0 < h) (h8 : h ≤ 1 / 8)
    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2)
    (hkr : k + 2 + r ≤ frozenSourceRankBound) :
    profileNoncoprimeMass N k r logQ h ≤ noncoprimeCount N := by
  have hweight : profileNoncoprimeMass N k r logQ h ≤
      ((profileNoncoprimeTuples N k r logQ h).card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ profileNoncoprimeTuples N k r logQ h, (1 : ℝ) := by
        apply sum_le_sum
        intro v hv
        exact (physicalProfile_bounds logQ (N : ℝ) (radialWidth h)
          ((N : ℝ) ^ frozenLeafCutoffFloor)
          (finToPhysical k r (fun i => ((v i).val : ℝ)))).2
      _ = _ := by simp
  have hcard : ((profileNoncoprimeTuples N k r logQ h).card : ℝ) ≤
      ((noncoprimeTuples N (k + (2 + r))).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card (profile_noncoprime_subset hN hp h8 hcut))
  exact hweight.trans (hcard.trans
    (rank_card_le_noncoprimeCount N (k + (2 + r)) (by omega)))

/-- The same original p, dependent history positions, levelMark and
complete old word as in selectedProfileMass, restricted by target
noncoprimality of the complete tuple product. -/
def selectedNoncoprimeMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, if admissibleSplit s then
      noncoprimeSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
        (levelOccurrence l).current.old
    else 0

private theorem history_sum_comm {ι : Type*} {N n dep : ℕ} {t : ℝ}
    (A : Finset ℕ) (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (I : Finset ι) (f : (p : ℕ) → LevelIndex N n .U4 t p dep → ι → ℝ) :
    (∑ p ∈ A, ∑ l ∈ B p, ∑ i ∈ I, f p l i) =
      ∑ i ∈ I, ∑ p ∈ A, ∑ l ∈ B p, f p l i := by
  calc
    _ = ∑ p ∈ A, ∑ i ∈ I, ∑ l ∈ B p, f p l i :=
      sum_congr rfl (fun p _ => sum_comm)
    _ = _ := sum_comm

theorem selectedNoncoprimeMass_eq_cells (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedNoncoprimeMass N n dep t h B =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B p, levelMark l *
          ∑ s : Split, if admissibleSplit s then
            noncoprimeSlice N s.1.val s.2.val (log (cellQ N n c)) h
              (levelOccurrence l).current.old
          else 0 := by
  calc
    _ = ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B p, levelMark l *
          ∑ s : Split, if admissibleSplit s then
            noncoprimeSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
              (levelOccurrence l).current.old
          else 0 := by
      symm
      simp only [originalRootCellBand, sum_filter]
      rw [sum_comm]
      simp [selectedNoncoprimeMass]
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro p hp
      rw [originalRootCellBand_Q hp]

/-- Exact rearrangement on full tuples with the existing original
positive prefix coefficient. No occurrences are merged by product value. -/
theorem selectedNoncoprimeMass_eq_prefix_sum (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedNoncoprimeMass N n dep t h B =
      ∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
        ∑ v ∈ profileNoncoprimeTuples N s.1.val s.2.val (log (cellQ N n c)) h,
          prefixWeight N n dep t c B (tuplePrefix (tupleValues v)) *
            finPhysicalProfile (log (cellQ N n c)) (N : ℝ) (radialWidth h)
              ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ))
      else 0 := by
  rw [selectedNoncoprimeMass_eq_cells]
  apply sum_congr rfl
  intro c hc
  simp_rw [mul_sum]
  rw [history_sum_comm]
  apply sum_congr rfl
  intro s hs
  by_cases ha : admissibleSplit s
  · simp only [if_pos ha, noncoprimeSlice_eq_filtered]
    simp_rw [mul_sum]
    rw [history_sum_comm]
    apply sum_congr rfl
    intro v hv
    unfold prefixWeight
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [sum_mul]
    apply sum_congr rfl
    intro l hl
    unfold boundedProfileWeight
    split_ifs <;> simp
  · simp [ha]

theorem selectedNoncoprimeMass_le_ambient_sum (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedNoncoprimeMass N n dep t h B ≤ (shapeWords.card : ℝ) *
      ∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
        profileNoncoprimeMass N s.1.val s.2.val (log (cellQ N n c)) h
      else 0 := by
  rw [selectedNoncoprimeMass_eq_prefix_sum, mul_sum]
  apply sum_le_sum
  intro c hc
  rw [mul_sum]
  apply sum_le_sum
  intro s hs
  by_cases ha : admissibleSplit s
  · simp only [if_pos ha, profileNoncoprimeMass, mul_sum]
    apply sum_le_sum
    intro v hv
    apply mul_le_mul_of_nonneg_right
      (prefixWeight_le_shapeCard N n dep t c B (tuplePrefix (tupleValues v)))
    exact (physicalProfile_bounds (log (cellQ N n c)) (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor)
      (finToPhysical s.1.val s.2.val (fun i => ((v i).val : ℝ)))).1
  · simp [ha]

/-- A concrete source-level bound. The original fixed aggregateCard
pays all shapes, root cells and splits before any target or B is chosen. -/
theorem selectedNoncoprimeMass_le_count {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hp : 0 < h) (h8 : h ≤ 1 / 8)
    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2)
    (n dep : ℕ) (t : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedNoncoprimeMass N n dep t h B ≤
      (aggregateCard n : ℝ) * noncoprimeCount N := by
  have hcount : 0 ≤ noncoprimeCount N := by
    unfold noncoprimeCount
    exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum :
      (∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
        profileNoncoprimeMass N s.1.val s.2.val (log (cellQ N n c)) h
      else 0) ≤
        (Fintype.card (RootCode n) : ℝ) * (Fintype.card Split : ℝ) *
          noncoprimeCount N := by
    calc
      _ ≤ ∑ _c : RootCode n, ∑ _s : Split, noncoprimeCount N := by
        apply sum_le_sum
        intro c hc
        apply sum_le_sum
        intro s hs
        by_cases ha : admissibleSplit s
        · simp only [if_pos ha]
          exact profileNoncoprimeMass_le_count hN hp h8 hcut ha
        · simpa only [if_neg ha] using hcount
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring
  calc
    _ ≤ (shapeWords.card : ℝ) *
        (∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
          profileNoncoprimeMass N s.1.val s.2.val (log (cellQ N n c)) h
        else 0) := selectedNoncoprimeMass_le_ambient_sum N n dep t h B
    _ ≤ (shapeWords.card : ℝ) *
        ((Fintype.card (RootCode n) : ℝ) * (Fintype.card Split : ℝ) *
          noncoprimeCount N) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by
      simp only [aggregateCard, Nat.cast_mul]
      ring

/-- A single eventual threshold pays the original history sum for every
allowed physical width, depth, root parameter and selected subfamily. -/
theorem absolute_selected_noncoprime_payment (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (dep : ℕ) (t h : ℝ),
      0 < h → h ≤ 1 / 8 →
      ∀ (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          selectedNoncoprimeMass N n dep t h B ≤ ε := by
  let e := ε / ((aggregateCard n : ℝ) + 1)
  have hden : 0 < (aggregateCard n : ℝ) + 1 := by positivity
  have he' : 0 < e := div_pos he hden
  filter_upwards [absolute_noncoprime_payment he', eventually_cut_le_half_floor,
    eventually_gt_atTop (1 : ℕ)] with N hpaid hcut hN
  intro dep t h hp h8 B
  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast hN.le)) (Nat.cast_nonneg _)
  calc
    _ ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N *
        ((aggregateCard n : ℝ) * noncoprimeCount N) :=
      mul_le_mul_of_nonneg_left
        (selectedNoncoprimeMass_le_count (by omega) hp h8 hcut n dep t B) hnorm
    _ = (aggregateCard n : ℝ) *
        (P2FiniteMarkedGamma5RadialRoughMass.norm N * noncoprimeCount N) := by ring
    _ ≤ (aggregateCard n : ℝ) * e :=
      mul_le_mul_of_nonneg_left hpaid (Nat.cast_nonneg _)
    _ ≤ ((aggregateCard n : ℝ) + 1) * e :=
      mul_le_mul_of_nonneg_right (by linarith) he'.le
    _ = ε := by
      dsimp only [e]
      rw [mul_comm, div_mul_cancel₀ _ hden.ne']

/-- The same original B dep p is retained at every fixed remaining depth. -/
def allDepthSelectedNoncoprimeMass (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) : ℝ :=
  ∑ dep : Fin 431, selectedNoncoprimeMass N n dep.val t h (B dep)

theorem allDepthSelectedNoncoprimeMass_le_count {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hp : 0 < h) (h8 : h ≤ 1 / 8)
    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2)
    (n : ℕ) (t : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) :
    allDepthSelectedNoncoprimeMass N n t h B ≤
      (431 : ℝ) * (aggregateCard n : ℝ) * noncoprimeCount N := by
  unfold allDepthSelectedNoncoprimeMass
  calc
    _ ≤ ∑ _dep : Fin 431, (aggregateCard n : ℝ) * noncoprimeCount N :=
      sum_le_sum (fun dep _ =>
        selectedNoncoprimeMass_le_count hN hp h8 hcut n dep.val t (B dep))
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The complete finite remaining-depth error budget is paid before
N, h, t and every moving selected-history subfamily. -/
theorem absolute_all_depth_selected_noncoprime_payment
    (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (t h : ℝ), 0 < h → h ≤ 1 / 8 →
      ∀ (B : (dep : Fin 431) → (p : ℕ) →
        Finset (LevelIndex N n .U4 t p dep.val)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          allDepthSelectedNoncoprimeMass N n t h B ≤ ε := by
  have he' : 0 < ε / (431 : ℝ) := div_pos he (by norm_num)
  filter_upwards [absolute_selected_noncoprime_payment n he'] with N hpaid
  intro t h hp h8 B
  unfold allDepthSelectedNoncoprimeMass
  rw [mul_sum]
  calc
    _ ≤ ∑ _dep : Fin 431, ε / (431 : ℝ) :=
      sum_le_sum (fun dep _ => hpaid dep.val t h hp h8 (B dep))
    _ = ε := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualTargetExclusion
