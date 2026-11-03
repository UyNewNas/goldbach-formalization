import ImbalancedChen.P2GammaU5PlateauGeometry

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Paper-internal algebra of the ORIGINAL U5 maximum, on its entire domain.
The owner is an exact disjoint bookkeeping partition, not a new sieve
policy, frozen level or smooth chart. No distribution theorem is used.
The plateau owns all its equality faces; the rising sum owns the v-knot;
on the remaining A(t)=C(t+u) face the falling sum owns the point.
-/
namespace ImbalancedChen.P3U5RootAtlas
noncomputable section
open scoped Classical BigOperators
open P2GammaU5PlateauGeometry
open Part5OriginalUpsilon5CausalDictionary

inductive Lane where
  | rise
  | plateau
  | fall
  | head
  deriving DecidableEq, Fintype

/-- All comparisons concern the old real level, before arithmetic errors. -/
def owner (u t : ℝ) : Lane :=
  if t+u ≤ VariableEnvelope.mu then .rise
  else if VariableEnvelope.A t ≤ plateauLevel ∧
      VariableEnvelope.C (t+u) ≤ plateauLevel then .plateau
  else if VariableEnvelope.A t ≤ VariableEnvelope.C (t+u) then .fall
  else .head

def laneLevel : Lane → ℝ → ℝ → ℝ
  | .rise, u, t => VariableEnvelope.A (t+u)
  | .plateau, _, _ => plateauLevel
  | .fall, u, t => VariableEnvelope.C (t+u)
  | .head, _, t => VariableEnvelope.A t

private theorem original_head_branch {u t : ℝ}
    (hu : a ≤ u) (hut : u ≤ t) (ht : t ≤ h) :
    VariableEnvelope.v t = VariableEnvelope.A t ∧
      VariableEnvelope.A t ≤ VariableEnvelope.A (t+u) ∧
      plateauLevel < VariableEnvelope.A (t+u) := by
  have htmu : t ≤ VariableEnvelope.mu := by
    dsimp [h,VariableEnvelope.mu] at *
    linarith
  refine ⟨VariableEnvelope.v_eq_A htmu,?_,?_⟩
  · dsimp [a,VariableEnvelope.A] at *
    linarith
  · rw [plateauLevel_exact]
    dsimp [a,VariableEnvelope.A] at *
    linarith

/-- Complete original maximum, including every tie and the v-knot. -/
theorem original_level_eq_owned {u t : ℝ}
    (hu : a ≤ u) (hut : u ≤ t) (ht : t ≤ h) :
    level u t = laneLevel (owner u t) u t := by
  obtain ⟨hv,hA,hP⟩ := original_head_branch hu hut ht
  by_cases hs : t+u ≤ VariableEnvelope.mu
  · simp only [owner,if_pos hs,laneLevel]
    unfold level
    rw [hv,VariableEnvelope.v_eq_A hs]
    change max (VariableEnvelope.A t)
      (max (VariableEnvelope.A (t+u)) plateauLevel) = _
    rw [max_eq_left hP.le,max_eq_right hA]
  · have hvsum := VariableEnvelope.v_eq_C (le_of_not_ge hs)
    by_cases hp : VariableEnvelope.A t ≤ plateauLevel ∧
        VariableEnvelope.C (t+u) ≤ plateauLevel
    · simp only [owner,if_neg hs,if_pos hp,laneLevel]
      unfold level
      rw [hv,hvsum]
      change max (VariableEnvelope.A t)
        (max (VariableEnvelope.C (t+u)) plateauLevel) = _
      rw [max_eq_right hp.2,max_eq_right hp.1]
    · by_cases hc : VariableEnvelope.A t ≤ VariableEnvelope.C (t+u)
      · have hpc : plateauLevel ≤ VariableEnvelope.C (t+u) := by
          by_contra hn
          exact hp ⟨hc.trans (le_of_not_ge hn),le_of_not_ge hn⟩
        simp only [owner,if_neg hs,if_neg hp,if_pos hc,laneLevel]
        unfold level
        rw [hv,hvsum]
        change max (VariableEnvelope.A t)
          (max (VariableEnvelope.C (t+u)) plateauLevel) = _
        rw [max_eq_left hpc,max_eq_right hc]
      · have hca : VariableEnvelope.C (t+u) ≤ VariableEnvelope.A t := le_of_not_ge hc
        have hpa : plateauLevel ≤ VariableEnvelope.A t := by
          by_contra hn
          exact hp ⟨le_of_not_ge hn,hca.trans (le_of_not_ge hn)⟩
        simp only [owner,if_neg hs,if_neg hp,if_neg hc,laneLevel]
        unfold level
        rw [hv,hvsum]
        change max (VariableEnvelope.A t)
          (max (VariableEnvelope.C (t+u)) plateauLevel) = _
        exact max_eq_left (max_le hca hpa)

/-- The ENTIRE plateau, not just the previously supplied witness box. -/
theorem original_level_eq_plateau_iff {u t : ℝ}
    (hu : a ≤ u) (hut : u ≤ t) (ht : t ≤ h) :
    level u t = plateauLevel ↔
      t ≤ (10621/80000 : ℝ) ∧ (17293/80000 : ℝ) ≤ t+u := by
  obtain ⟨hv,hA,hP⟩ := original_head_branch hu hut ht
  have hform : level u t = max (VariableEnvelope.A t)
      (max (min (VariableEnvelope.A (t+u)) (VariableEnvelope.C (t+u))) plateauLevel) := by
    unfold level
    rw [hv,VariableEnvelope.v_eq_min]
    rfl
  have hp : level u t = plateauLevel ↔
      VariableEnvelope.A t ≤ plateauLevel ∧ VariableEnvelope.C (t+u) ≤ plateauLevel := by
    rw [hform]
    constructor
    · intro heq
      have hfirst : VariableEnvelope.A t ≤ plateauLevel := by
        rw [← heq]
        exact le_max_left _ _
      have hmin : min (VariableEnvelope.A (t+u)) (VariableEnvelope.C (t+u)) ≤ plateauLevel := by
        rw [← heq]
        exact (le_max_left _ _).trans (le_max_right _ _)
      refine ⟨hfirst,?_⟩
      by_contra hn
      exact (not_lt_of_ge hmin) (lt_min hP (lt_of_not_ge hn))
    · rintro ⟨ha,hc⟩
      rw [max_eq_right ((min_le_right _ _).trans hc),max_eq_right ha]
  rw [hp,plateauLevel_exact]
  dsimp [VariableEnvelope.A,VariableEnvelope.C]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

/-- No data on the equality surfaces is dropped or paid by a null-set claim. -/
theorem owner_plateau_iff (u t : ℝ) :
    owner u t = Lane.plateau ↔
      t ≤ (10621/80000 : ℝ) ∧ (17293/80000 : ℝ) ≤ t+u := by
  have hp : (VariableEnvelope.A t ≤ plateauLevel ∧ VariableEnvelope.C (t+u) ≤ plateauLevel) ↔
      t ≤ (10621/80000 : ℝ) ∧ (17293/80000 : ℝ) ≤ t+u := by
    rw [plateauLevel_exact]
    dsimp [VariableEnvelope.A,VariableEnvelope.C]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  by_cases hs : t+u ≤ VariableEnvelope.mu
  · have hn : ¬ (t ≤ (10621/80000 : ℝ) ∧ (17293/80000 : ℝ) ≤ t+u) := by
      intro hh
      dsimp [VariableEnvelope.mu] at hs
      linarith [hh.2]
    simp [owner,hs,hn]
  · by_cases hh : VariableEnvelope.A t ≤ plateauLevel ∧ VariableEnvelope.C (t+u) ≤ plateauLevel
    · simp [owner,hs,hh,hp.mp hh]
    · have hn := mt hp.mpr hh
      simp only [owner,if_neg hs,if_neg hh]
      split_ifs <;> simp [hn]

/-- The rising branch owns the exact join t+u=25/128. -/
theorem owner_rise_iff (u t : ℝ) :
    owner u t = Lane.rise ↔ t+u ≤ VariableEnvelope.mu := by
  unfold owner
  split_ifs <;> simp_all

/-- This original affine wall is retained, including its tie orientation. -/
theorem fall_head_comparison (u t : ℝ) :
    VariableEnvelope.A t ≤ VariableEnvelope.C (t+u) ↔ 3*u+4*t ≤ (25/32 : ℝ) := by
  dsimp [VariableEnvelope.A,VariableEnvelope.C]
  constructor <;> intro hh <;> linarith

end
end ImbalancedChen.P3U5RootAtlas
