import ImbalancedChen.P1HistoricalUpperFourthPhysicalGates

/-!
# P1: the historical fourth s=1 boundary is a double wall

On the actual third-parent cone, the fourth PLUS gap is
B = A + 2 G, with A the third cube gap and G=t2-t3 the strict order gap.
A small positive B therefore lies near both independent walls.  The weak
closed cone meets B=0 exactly at their intersection.  This module supplies
continuous and arithmetic localization, with no volume or density bound.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Set

/-- The actual inherited rank-three parent margin. -/
def p1_fourthThirdWallGap (old : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  old - t 0 - t 1 - 3 * t 2

/-- The order gap between the third and fourth selected primes. -/
def p1_fourthOrderWallGap (t : Fin 4 → ℝ) : ℝ := t 2 - t 3

/-- The numerator of s-1 for the fourth PLUS residual. -/
def p1_fourthPlusWallGap (old : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  old - (∑ i, t i) - t 3

/-- The extra terminal coordinate in B accounts for the second copy of G. -/
theorem p1_fourthPlusWallGap_eq (old : ℝ) (t : Fin 4 → ℝ) :
    p1_fourthPlusWallGap old t =
      p1_fourthThirdWallGap old t + 2 * p1_fourthOrderWallGap t := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [p1_fourthPlusWallGap, hsum, p1_fourthThirdWallGap, p1_fourthOrderWallGap]
  ring

/-- Two continuous wall coordinates, retained together for later budgets. -/
def p1_fourthDoubleWallCoordinates (old : ℝ) (t : Fin 4 → ℝ) : ℝ × ℝ :=
  (p1_fourthThirdWallGap old t, p1_fourthOrderWallGap t)

theorem p1_fourthDoubleWallCoordinates_continuous (old : ℝ) :
    Continuous (p1_fourthDoubleWallCoordinates old) := by
  unfold p1_fourthDoubleWallCoordinates p1_fourthThirdWallGap p1_fourthOrderWallGap
  fun_prop

/-- The walls are independent: their joint affine coordinates attain every
pair of real values.  No measure or asymptotic estimate is invoked. -/
theorem p1_fourthDoubleWallCoordinates_surjective (old : ℝ) :
    Function.Surjective (p1_fourthDoubleWallCoordinates old) := by
  rintro ⟨a, g⟩
  refine ⟨![old - a, 0, 0, -g], ?_⟩
  apply Prod.ext <;>
    simp [p1_fourthDoubleWallCoordinates, p1_fourthThirdWallGap, p1_fourthOrderWallGap] <;> ring

theorem p1_fourthPlusWallGap_continuous (old : ℝ) :
    Continuous (p1_fourthPlusWallGap old) := by
  unfold p1_fourthPlusWallGap
  fun_prop

/-- The genuine near-s=1 numerator strip localizes to two positive strips.
The order strip is strictly narrower than delta/2 because A is positive. -/
theorem p1_fourth_double_wall_localization (old delta : ℝ) (t : Fin 4 → ℝ)
    (hA : 0 < p1_fourthThirdWallGap old t)
    (hG : 0 < p1_fourthOrderWallGap t)
    (hB : 0 < p1_fourthPlusWallGap old t ∧ p1_fourthPlusWallGap old t ≤ delta) :
    0 < delta ∧
      (0 < p1_fourthThirdWallGap old t ∧ p1_fourthThirdWallGap old t ≤ delta) ∧
      (0 < p1_fourthOrderWallGap t ∧ p1_fourthOrderWallGap t ≤ delta / 2) ∧
      p1_fourthThirdWallGap old t < delta ∧ p1_fourthOrderWallGap t < delta / 2 := by
  have hid := p1_fourthPlusWallGap_eq old t
  refine ⟨lt_of_lt_of_le hB.1 hB.2, ⟨hA, ?_⟩, ⟨hG, ?_⟩, ?_, ?_⟩ <;>
    nlinarith only [hid, hB.2, hA, hG]

/-- The actual strip lies in the simultaneous two-wall rectangle, rather
than merely in the union of two wall strips. -/
theorem p1_fourth_nearPlusWall_subset_double_strip (old delta : ℝ) :
    {t : Fin 4 → ℝ | 0 < p1_fourthThirdWallGap old t ∧
      0 < p1_fourthOrderWallGap t ∧
      0 < p1_fourthPlusWallGap old t ∧ p1_fourthPlusWallGap old t ≤ delta} ⊆
    (p1_fourthDoubleWallCoordinates old) ⁻¹'
      (Set.Ioc 0 delta ×ˢ Set.Ioc 0 (delta / 2)) := by
  intro t ht
  have hh := p1_fourth_double_wall_localization old delta t ht.1 ht.2.1 ht.2.2
  exact ⟨hh.2.1, hh.2.2.1⟩

/-- On the closed cone there is no other s=1 numerator boundary. -/
theorem p1_fourth_closed_double_wall_iff (old : ℝ) (t : Fin 4 → ℝ)
    (hA : 0 ≤ p1_fourthThirdWallGap old t)
    (hG : 0 ≤ p1_fourthOrderWallGap t) :
    p1_fourthPlusWallGap old t = 0 ↔
      p1_fourthThirdWallGap old t = 0 ∧ t 2 = t 3 := by
  have hid := p1_fourthPlusWallGap_eq old t
  constructor
  · intro hB
    have ha : p1_fourthThirdWallGap old t = 0 := by nlinarith
    have hg : p1_fourthOrderWallGap t = 0 := by nlinarith
    exact ⟨ha, sub_eq_zero.mp hg⟩
  · rintro ⟨ha, horder⟩
    have hg : p1_fourthOrderWallGap t = 0 := by
      simp [p1_fourthOrderWallGap, horder]
    rw [hid, ha, hg]
    ring

/-- Exact corner locus as a set equality, without a positive-cutoff premise. -/
theorem p1_fourth_closed_corner_locus (old : ℝ) :
    {t : Fin 4 → ℝ | 0 ≤ p1_fourthThirdWallGap old t ∧
      0 ≤ p1_fourthOrderWallGap t ∧ p1_fourthPlusWallGap old t = 0} =
    {t : Fin 4 → ℝ | p1_fourthThirdWallGap old t = 0 ∧ t 2 = t 3} := by
  ext t
  constructor
  · rintro ⟨ha, hg, hb⟩
    exact (p1_fourth_closed_double_wall_iff old t ha hg).mp hb
  · rintro ⟨ha, horder⟩
    have hg : p1_fourthOrderWallGap t = 0 := by simp [p1_fourthOrderWallGap, horder]
    exact ⟨ha.ge, hg.ge, (p1_fourth_closed_double_wall_iff old t ha.ge hg.ge).mpr ⟨ha, horder⟩⟩

/-- Exact relation between the residual ratio and its numerator gap. -/
theorem p1_fourthPlusWallGap_eq_ratio (old : ℝ) (t : Fin 4 → ℝ) (ht3 : t 3 ≠ 0) :
    p1_fourthPlusWallGap old t = (((old - ∑ i, t i) / t 3) - 1) * t 3 := by
  unfold p1_fourthPlusWallGap
  field_simp [ht3] <;> ring

/-- At positive terminal cutoff, s=1 on the weak parent cone is exactly
the intersection of the third-parent wall and the order wall. -/
theorem p1_fourth_ratio_one_iff_double_wall (old : ℝ) (t : Fin 4 → ℝ)
    (ht3 : 0 < t 3) (hA : 0 ≤ p1_fourthThirdWallGap old t)
    (hG : 0 ≤ p1_fourthOrderWallGap t) :
    (old - ∑ i, t i) / t 3 = 1 ↔
      p1_fourthThirdWallGap old t = 0 ∧ t 2 = t 3 := by
  have hzero : (old - ∑ i, t i) / t 3 = 1 ↔ p1_fourthPlusWallGap old t = 0 := by
    rw [div_eq_iff ht3.ne']
    unfold p1_fourthPlusWallGap
    constructor <;> intro h <;> linarith
  exact hzero.trans (p1_fourth_closed_double_wall_iff old t hA hG)

/-- A relative near-s=1 strip is a physical numerator strip of width
at most epsilon*rho when the terminal log coordinate is at most rho. -/
theorem p1_fourth_near_ratio_double_wall (old epsilon rho : ℝ) (t : Fin 4 → ℝ)
    (ht3 : 0 < t 3) (htrho : t 3 ≤ rho)
    (hA : 0 < p1_fourthThirdWallGap old t)
    (hG : 0 < p1_fourthOrderWallGap t)
    (hs : 1 < (old - ∑ i, t i) / t 3 ∧ (old - ∑ i, t i) / t 3 ≤ 1 + epsilon) :
    0 < p1_fourthPlusWallGap old t ∧ p1_fourthPlusWallGap old t ≤ epsilon * rho ∧
      p1_fourthThirdWallGap old t ≤ epsilon * rho ∧
      p1_fourthOrderWallGap t ≤ epsilon * rho / 2 := by
  have heps : 0 < epsilon := by linarith [hs.1, hs.2]
  have hr : 0 < (old - ∑ i, t i) / t 3 - 1 := by linarith [hs.1]
  have hBpos : 0 < p1_fourthPlusWallGap old t := by
    rw [p1_fourthPlusWallGap_eq_ratio old t ht3.ne']
    exact mul_pos hr ht3
  have hB : p1_fourthPlusWallGap old t ≤ epsilon * rho := by
    rw [p1_fourthPlusWallGap_eq_ratio old t ht3.ne']
    calc
      _ ≤ epsilon * t 3 := mul_le_mul_of_nonneg_right (by linarith [hs.2]) ht3.le
      _ ≤ epsilon * rho := mul_le_mul_of_nonneg_left htrho heps.le
  have hh := p1_fourth_double_wall_localization old (epsilon * rho) t hA hG ⟨hBpos, hB⟩
  exact ⟨hBpos, hB, hh.2.1.2, hh.2.2.1.2⟩

/-- The original historical dictionary supplies positivity of both wall
coordinates for actual admitted tuples, without a new admission filter. -/
theorem p1_admittedFourth_double_wall_positive
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1))
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    0 < p1_fourthThirdWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p) ∧
      0 < p1_fourthOrderWallGap (actualPrimeTupleLog N p) := by
  have hd := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab hlevels N cap hN hcap p j ht).mp hp
  have hs : StrictAnti (actualPrimeTupleLog N p) :=
    (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hd.2.1 i).1.pos)).mpr hd.1
  refine ⟨?_, sub_pos.mpr (hs (by decide : (2 : Fin 4) < 3))⟩
  unfold p1_fourthThirdWallGap
  linarith [hd.2.2.2]

/-- Near-boundary actual PLUS density parameters force both independent
arithmetic-log wall strips.  The cutoff bound comes from the same owned mesh. -/
theorem p1_admittedFourth_near_actual_ratio_double_wall
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1)) (epsilon : ℝ)
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (hs : let q := actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
        (p 3 : ℝ) (D.old4 j : ℝ)
      1 < q.1 / q.2 ∧ q.1 / q.2 ≤ 1 + epsilon) :
    p1_fourthThirdWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p) ≤ epsilon * (D.b : ℝ) ∧
      0 < actualPrimeTupleLog N p 2 - actualPrimeTupleLog N p 3 ∧
      actualPrimeTupleLog N p 2 - actualPrimeTupleLog N p 3 ≤ epsilon * (D.b : ℝ) / 2 := by
  have hd := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab.le hlevels N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).1.pos
  have hparams := p1_admittedFourth_plusLegality_on_cell D hab.le hlevels N cap hN hcap p j hp ht
  have hwalls := p1_admittedFourth_double_wall_positive D hab.le hlevels N cap hN hcap p j hp ht
  have hbox := logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht
  have htrho : actualPrimeTupleLog N p 3 ≤ (D.b : ℝ) := (mem_logPrimeBox.mp hbox 3).2.le
  have hs' : 1 < ((D.old4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) /
        actualPrimeTupleLog N p 3 ∧
      ((D.old4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) /
        actualPrimeTupleLog N p 3 ≤ 1 + epsilon := by
    simpa only [p1_fourth_quotientParameters_eq N p hpos (D.old4 j : ℝ)] using hs
  have hh := p1_fourth_near_ratio_double_wall (D.old4 j : ℝ) epsilon (D.b : ℝ)
    (actualPrimeTupleLog N p) hparams.1 htrho hwalls.1 hwalls.2 hs'
  exact ⟨hh.2.2.1, hwalls.2, hh.2.2.2⟩

/-- A raised fourth level near s=1 also lies near the two original parent
walls.  The nonnegative level-raising gap is small at the same time. -/
theorem p1_fourth_near_raised_ratio_double_wall (old lambda epsilon rho : ℝ)
    (t : Fin 4 → ℝ) (hlevel : old ≤ lambda)
    (ht3 : 0 < t 3) (htrho : t 3 ≤ rho)
    (hA : 0 < p1_fourthThirdWallGap old t)
    (hG : 0 < p1_fourthOrderWallGap t)
    (hs : 1 < (lambda - ∑ i, t i) / t 3 ∧
      (lambda - ∑ i, t i) / t 3 ≤ 1 + epsilon) :
    p1_fourthThirdWallGap old t ≤ epsilon * rho ∧
      p1_fourthOrderWallGap t ≤ epsilon * rho / 2 ∧
      0 ≤ lambda - old ∧ lambda - old ≤ epsilon * rho := by
  have hAlambda : 0 < p1_fourthThirdWallGap lambda t := by
    unfold p1_fourthThirdWallGap at hA ⊢
    linarith
  have hh := p1_fourth_near_ratio_double_wall lambda epsilon rho t ht3 htrho hAlambda hG hs
  have hgap : lambda - old ≤ p1_fourthThirdWallGap lambda t := by
    unfold p1_fourthThirdWallGap at hA ⊢
    linarith
  have hmono : p1_fourthThirdWallGap old t ≤ p1_fourthThirdWallGap lambda t := by
    unfold p1_fourthThirdWallGap
    linarith
  exact ⟨hmono.trans hh.2.2.1, hh.2.2.2, sub_nonneg.mpr hlevel,
    hgap.trans hh.2.2.1⟩

end
end ImbalancedChen
