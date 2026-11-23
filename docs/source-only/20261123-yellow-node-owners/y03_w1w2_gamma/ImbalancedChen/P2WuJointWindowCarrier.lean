import ImbalancedChen.P2WuJointWindowProfile
import ImbalancedChen.P2WuOriginalWindowUpperWall

/-!
All `2*i` prefix walls are removed together in the original rank-label
construction at the W1 parameters. The prime/coprime mask, distinguished
triple, strengthened switched fibre and ordered tail are part of the carrier.
Testing the closed lower and strict upper endpoints of the SAME physical word
recovers exactly the original indexed family.
-/
namespace ImbalancedChen.P2WuJointWindowCarrier

noncomputable section
open Finset Wu2008DoubleSieve
open P2NativeOmega3ExpandedPrimeWords P2NativeOmega3RankTupleReceiver
open P2WuOriginalWindowUpperWall P2WuJointWindowProfile
open scoped Classical BigOperators

def lower (b : BoxIndex) (j : Fin b.1) : ℝ := b.2.2 j / b.2.1

def physical {r N : ℕ} (u : Fin r → Fin (N+1)) (l : Fin r) : ℝ := (u l).val

def unrestrictedWindows (N i : ℕ) (_j : Fin i) : Finset ℕ :=
  primeWindow N 0 ((N : ℝ) + 1)

def carrier (δ : ℝ) (r N i : ℕ) : Finset (Fin r → Fin (N+1)) :=
  family N δ 3 (16/5) (unrestrictedWindows N i) r

private theorem unrestricted_prime {N i : ℕ} (j : Fin i) (p : ℕ)
    (hp : p ∈ unrestrictedWindows N i j) : p.Prime :=
  (mem_primeWindow.mp hp).1

theorem carrier_product_cap {δ : ℝ} {r N i : ℕ} :
    ∀ u ∈ carrier δ r N i, Part3.labelledProduct u ≤ N :=
  family_product_cap unrestricted_prime

theorem prefix_fits {δ : ℝ} {r N i : ℕ} {u : Fin r → Fin (N+1)}
    (hu : u ∈ carrier δ r N i) : i ≤ r := by
  obtain ⟨a, ha, _⟩ := mem_image.mp hu
  have hlen := (rank_data ha).2
  simp only [primeWord, List.length_append, List.length_ofFn, List.length_cons,
    List.length_nil] at hlen
  omega

theorem indexed_subset_carrier {k r N : ℕ} {δ : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) :
    indexedFamily k δ r N b ⊆ carrier δ r N b.1 := by
  rw [indexedFamily, if_pos hb]
  intro u hu
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
  refine mem_image.mpr ⟨a, change_windows ha ?_, rfl⟩
  intro j
  have hp := old_window_geometry (rank_data ha).1 j
  obtain ⟨hr, he⟩ := read_prefix_slot
    (fun _ _ hp => (mem_convolutionWuWindows.mp hp).1) ha j
  have hcap : a.1 j ≤ N := by
    rw [← he]
    exact Nat.le_of_lt_succ (tuple N r a ⟨j.val, hr⟩).isLt
  have hreal : (a.1 j : ℝ) ≤ N := by exact_mod_cast hcap
  exact mem_primeWindow.mpr ⟨hp.1, hp.2.1, Nat.cast_nonneg _, by linarith only [hreal]⟩

/-- The reverse implication keeps the very same labelled witness and tail.
The complete-product map is unrestricted in multiplicity. -/
theorem indexed_iff_prefix {k r N : ℕ} {δ : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hr : b.1 ≤ r)
    {u : Fin r → Fin (N+1)} (hu : u ∈ carrier δ r N b.1) :
    u ∈ indexedFamily k δ r N b ↔
      ∀ j, lower b j ≤ physical u (Fin.castLE hr j) ∧
        physical u (Fin.castLE hr j) < b.2.2 j := by
  rw [indexedFamily, if_pos hb]
  constructor
  · intro hs
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
    intro j
    obtain ⟨_, he⟩ := read_prefix_slot
      (fun _ _ hp => (mem_convolutionWuWindows.mp hp).1) ha j
    have hread : (tuple N r a (Fin.castLE hr j)).val = a.1 j := he
    simp only [physical, hread]
    exact (old_window_geometry (rank_data ha).1 j).2.2
  · intro hall
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    refine mem_image.mpr ⟨a, change_windows ha ?_, rfl⟩
    intro j
    obtain ⟨_, he⟩ := read_prefix_slot unrestricted_prime ha j
    have hread : (tuple N r a (Fin.castLE hr j)).val = a.1 j := he
    have hbounds := hall j
    simp only [physical, hread] at hbounds
    have hmem := Fintype.mem_piFinset.mp (expanded_data (rank_data ha).1).1 j
    have hp := mem_primeWindow.mp hmem
    exact mem_convolutionWuWindows.mpr ⟨hp.1, hp.2.1, hbounds.1, hbounds.2⟩

def jointWeight (δ w : ℝ) (r N : ℕ) (b : BoxIndex) (u : Fin r → Fin (N+1)) : ℝ :=
  p5z_markedPhysicalWeight (carrier δ r N b.1) (fun v =>
    if hr : b.1 ≤ r then
      profile (lower b) b.2.2 w (Fin.castLE hr) (physical v)
    else 0) u

theorem jointWeight_bounds (δ w : ℝ) (r N : ℕ) (b : BoxIndex) (u : Fin r → Fin (N+1)) :
    0 ≤ jointWeight δ w r N b u ∧ jointWeight δ w r N b u ≤ 1 := by
  unfold jointWeight p5z_markedPhysicalWeight
  split_ifs
  · exact profile_bounds _ _ _ _ _
  all_goals norm_num

theorem jointWeight_one {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0 < w)
    (hL : ∀ j, 0 < lower b j) (hV : ∀ j, 0 < b.2.2 j)
    {u : Fin r → Fin (N+1)} (hu : u ∈ indexedFamily k δ r N b) :
    jointWeight δ w r N b u = 1 := by
  have hcar := indexed_subset_carrier hb hu
  have hfit := prefix_fits hcar
  have hin := (indexed_iff_prefix hb hfit hcar).mp hu
  simp only [jointWeight, p5z_markedPhysicalWeight, if_pos hcar, dif_pos hfit]
  exact profile_one hL hV hw (fun j => ⟨(hin j).1, (hin j).2.le⟩)

theorem native_outside_nonzero {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0 < w)
    (hL : ∀ j, 0 < lower b j) (hV : ∀ j, 0 < b.2.2 j)
    {u : Fin r → Fin (N+1)} (hs : u ∉ indexedFamily k δ r N b)
    (hn : jointWeight δ w r N b u ≠ 0) :
    Part3.labelledProduct u ≤ N ∧ ∃ hr : b.1 ≤ r, ∃ j : Fin b.1,
      windowCollar (lower b j) (b.2.2 j) w (physical u (Fin.castLE hr j)) := by
  have hcar : u ∈ carrier δ r N b.1 := by
    by_contra hc
    exact hn (by simp only [jointWeight, p5z_markedPhysicalWeight, if_neg hc])
  have hfit := prefix_fits hcar
  refine ⟨carrier_product_cap u hcar, hfit, ?_⟩
  simp only [jointWeight, p5z_markedPhysicalWeight, if_pos hcar, dif_pos hfit] at hn
  exact outside_nonzero_collar hL hV hw (fun h => hs ((indexed_iff_prefix hb hfit hcar).mpr h)) hn

/-- Equality on the full original labelled grid outside all prefix collars;
this also covers ranks too short to contain the prefix and depth zero. -/
theorem native_off_collar {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0 < w)
    (hL : ∀ j, 0 < lower b j) (hV : ∀ j, 0 < b.2.2 j)
    (u : Fin r → Fin (N+1))
    (hoff : ∀ (hr : b.1 ≤ r) (j : Fin b.1),
      ¬ windowCollar (lower b j) (b.2.2 j) w (physical u (Fin.castLE hr j))) :
    jointWeight δ w r N b u = indexedWeight k δ r N b u := by
  by_cases hs : u ∈ indexedFamily k δ r N b
  · rw [jointWeight_one hb hw hL hV hs]
    exact (if_pos hs).symm
  · have hz : indexedWeight k δ r N b u = 0 := if_neg hs
    rw [hz]
    by_contra hn
    obtain ⟨_, hr, j, hj⟩ := native_outside_nonzero hb hw hL hV hs hn
    exact hoff hr j hj

end
end ImbalancedChen.P2WuJointWindowCarrier
