import ImbalancedChen.FirstExitDepthSplice
import ImbalancedChen.ActualPrimeReciprocalMass

/-! An unsigned weight bound on the stopped states of the original first-exit
tree. The enumeration keeps every occurrence. Restricting the prime weight to a
fixed power interval makes the bound uniform in the target and stopping rank. -/

namespace ImbalancedChen.FirstExitFrontierWeightBound

noncomputable section

open Filter Topology
open scoped BigOperators

private theorem word_nonneg {α : Type*} (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (H : List α) :
    0 ≤ (H.map g).prod := by
  induction H with
  | nil => simp
  | cons p H ih => exact mul_nonneg (hg p) ih

private theorem euler_ge_one {α : Type*} (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (U : List α) :
    1 ≤ (U.map (fun p => 1 + g p)).prod := by
  induction U with
  | nil => rfl
  | cons p U ih =>
    change 1 ≤ (1 + g p) * _
    have hp : 1 ≤ 1 + g p := by linarith only [hg p]
    exact ih.trans (le_mul_of_one_le_left (zero_le_one.trans ih) hp)

/-- A stopped scan counts a retained state's prefix weight once for each
occurrence. The weight used to look up states can differ from the
nonnegative weight being summed. -/
theorem frontier_weight_le_product {α : Type*} (k : ℕ) (parent : Bool → List α → Bool)
    (h g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (pre : List α) (positive : Bool)
    (mass : ℝ) (carrier : List α) :
    ((firstExitDepthFrontier k parent h pre positive mass carrier).map
      (fun s => (s.selectedPrefix.map g).prod)).sum ≤
        (pre.map g).prod * (carrier.map (fun p => 1 + g p)).prod := by
  induction carrier generalizing pre positive mass with
  | nil =>
    by_cases hk : k ≤ pre.length
    · simp [firstExitDepthFrontier, hk]
    · simpa [firstExitDepthFrontier, hk] using word_nonneg g hg pre
  | cons p ps ih =>
    have hpre := word_nonneg g hg pre
    have htail := euler_ge_one g hg ps
    by_cases hk : k ≤ pre.length
    · have hall := euler_ge_one g hg (p :: ps)
      simpa [firstExitDepthFrontier, hk] using
        (le_mul_of_one_le_right hpre hall)
    · have hs := ih pre positive mass
      by_cases hp : parent (!positive) (p :: pre) = true
      · have ht := ih (p :: pre) (!positive) (mass * h p)
        simp only [List.map_cons, List.prod_cons] at ht
        simp only [firstExitDepthFrontier, if_neg hk, if_pos hp, List.map_append,
          List.sum_append, List.map_cons, List.prod_cons]
        exact (add_le_add hs ht).trans_eq (by ring)
      · simp only [firstExitDepthFrontier, if_neg hk, if_neg hp, List.append_nil,
          List.map_cons, List.prod_cons]
        apply hs.trans
        have hr := mul_nonneg (hg p) (zero_le_one.trans htail)
        apply mul_le_mul_of_nonneg_left _ hpre
        linarith only [hr]

private theorem euler_le_exp_sum {α : Type*} (g : α → ℝ) (hg : ∀ p, 0 ≤ g p)
    (carrier : List α) :
    (carrier.map (fun p => 1 + g p)).prod ≤ Real.exp (carrier.map g).sum := by
  induction carrier with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Real.exp_add]
    have hp : 1 + g p ≤ Real.exp (g p) := by simpa only [add_comm] using Real.add_one_le_exp (g p)
    exact mul_le_mul hp ih (zero_le_one.trans (euler_ge_one g hg ps)) (Real.exp_pos _).le

/-- The literal target-deleted weight on [N^d,N^a), zero outside. -/
def windowWeight (N : ℕ) (d a : ℝ) (p : ℕ) : ℝ :=
  if p ∈ roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ d) ((N : ℝ) ^ a)
  then 1 / ((p : ℝ) - 1) else 0

private theorem prime_weight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ 1 / ((p : ℝ) - 1) := by
  have hr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  exact div_nonneg zero_le_one (sub_nonneg.mpr hr)

theorem windowWeight_nonneg (N : ℕ) (d a : ℝ) (p : ℕ) : 0 ≤ windowWeight N d a p := by
  unfold windowWeight
  split_ifs with h
  · exact prime_weight_nonneg (mem_roughPrimeFinset.mp h).2.1
  · exact le_rfl

theorem windowWeight_eq_of_mem {N enum : ℕ} {d a : ℝ} {p : ℕ}
    (hp : p ∈ roughPrimeUniverse N enum 0 ((N : ℝ) ^ a)) (hlo : (N : ℝ) ^ d ≤ (p : ℝ)) :
    windowWeight N d a p = 1 / ((p : ℝ) - 1) := by
  obtain ⟨_, hprime, htarget, _, hhi⟩ := mem_roughPrimeUniverse.mp hp
  exact if_pos ((mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)).mpr
    ⟨hprime, htarget, hlo, hhi⟩)

private theorem window_sum_le {N enum : ℕ} (hN : 1 ≤ (N : ℝ)) {e d a : ℝ} (hed : e ≤ d) :
    ((roughPrimeUniverse N enum 0 ((N : ℝ) ^ a)).map (windowWeight N d a)).sum ≤
      actualPrimeReciprocalMass N e a := by
  classical
  let U := roughPrimeUniverse N enum 0 ((N : ℝ) ^ a)
  let W := roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ d) ((N : ℝ) ^ a)
  have hc := List.sum_toFinset (windowWeight N d a) (roughPrimeUniverse_nodup N enum 0 ((N : ℝ) ^ a))
  rw [← hc]
  change (∑ p ∈ U.toFinset, if p ∈ W then 1 / ((p : ℝ) - 1) else 0) ≤ _
  rw [← Finset.sum_filter]
  unfold actualPrimeReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hn, hprime, htarget, hlo, hhi⟩ :=
      mem_roughPrimeFinset.mp (show p ∈ W from (Finset.mem_filter.mp hp).2)
    exact mem_roughPrimeFinset.mpr ⟨hn, hprime, htarget,
      (Real.rpow_le_rpow_of_exponent_le hN hed).trans hlo, hhi⟩
  · intro p hp _
    exact prime_weight_nonneg (mem_roughPrimeFinset.mp hp).2.1

/-- A single constant and threshold precede every target, enumeration cap,
stopping rank, and parent policy. The lower endpoint of the window is
closed and the upper endpoint is strict. -/
theorem exists_frontier_window_weight_bound (d a : ℝ) (hd : 0 < d) (ha : 0 < a) :
    ∃ H : ℝ, 0 < H ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0,
      ∀ (enum k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ),
        ((firstExitDepthFrontier k parent h [] true 1
          (roughPrimeUniverse N enum 0 ((N : ℝ) ^ a))).map
            (fun s => (s.selectedPrefix.map (windowWeight N d a)).prod)).sum ≤ H := by
  let e := min d (a / 2)
  have he : 0 < e := lt_min hd (half_pos ha)
  have hea : e < a := (min_le_right d (a / 2)).trans_lt (half_lt_self ha)
  let B := Real.log (a / e) + 1
  have hev : ∀ᶠ N : ℕ in atTop, actualPrimeReciprocalMass N e a < B :=
    (tendsto_actualPrimeReciprocalMass he hea).eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨Real.exp B, Real.exp_pos _, max N0 2, le_max_right _ _, ?_⟩
  intro N hN enum k parent h
  have htwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  let g := windowWeight N d a
  let U := roughPrimeUniverse N enum 0 ((N : ℝ) ^ a)
  have hs : (U.map g).sum ≤ B := (window_sum_le hNr (min_le_left d (a / 2))).trans
    (hN0 N ((le_max_left _ _).trans hN)).le
  have hf := frontier_weight_le_product k parent h g (windowWeight_nonneg N d a) [] true 1 U
  simp only [List.map_nil, List.prod_nil, one_mul] at hf
  exact hf.trans ((euler_le_exp_sum g (windowWeight_nonneg N d a) U).trans (Real.exp_le_exp.mpr hs))

end

end ImbalancedChen.FirstExitFrontierWeightBound
