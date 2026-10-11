import ImbalancedChen.BufferedFirstCubeGeometry
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Constant selected-prefix caps licensed on whole rational boxes

The complete square gate and selected-subproduct square gate are the
literal finite sums in the manuscript. Their coefficients are nonnegative,
so upper box endpoints bound every gate. The tent lower interval bound
licenses the selected endpoint. A successful rational gap check constructs
one rational midpoint cap, fixed throughout the entire closed box.
This does not import the numerical box data or assert that an arbitrary
original certificate rectangle already passes the constant-cap check.
-/

namespace ImbalancedChen

open scoped BigOperators
open VariableEnvelope
open Filter Topology

def prefixSquareExpr {n : ℕ} {α : Type*} [CommSemiring α]
    (t : Fin n → α) (j : Fin n) : α :=
  (∑ k ∈ Finset.univ.filter (fun k => k < j), t k) + 2 * t j

def selectedSquareExpr {n : ℕ} {α : Type*} [CommSemiring α]
    (I : Finset (Fin n)) (t : Fin n → α) (j : Fin n) : α :=
  (∑ k ∈ I, t k) +
    (∑ k ∈ Finset.univ.filter (fun k => k < j ∧ k ∉ I), t k) + 2 * t j

def selectedCapLowerSet {n : ℕ} (I : Finset (Fin n)) (old : ℚ) (u : Fin n → ℚ) :
    Finset ℚ :=
  insert old (insert (1 / 2)
    (Finset.univ.image (prefixSquareExpr u) ∪
      (Finset.univ \ I).image (selectedSquareExpr I u)))

theorem selectedCapLowerSet_nonempty {n : ℕ} (I : Finset (Fin n))
    (old : ℚ) (u : Fin n → ℚ) : (selectedCapLowerSet I old u).Nonempty :=
  ⟨old, by simp [selectedCapLowerSet]⟩

def selectedCapLower {n : ℕ} (I : Finset (Fin n)) (old : ℚ) (u : Fin n → ℚ) : ℚ :=
  (selectedCapLowerSet I old u).max' (selectedCapLowerSet_nonempty I old u)

def selectedCapUpper {n : ℕ} (I : Finset (Fin n)) (nu : ℚ) (l u : Fin n → ℚ) : ℚ :=
  min nu (qVLo (∑ k ∈ I, l k) (∑ k ∈ I, u k))

def selectedBoxCap {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (l u : Fin n → ℚ) : ℚ :=
  (selectedCapLower I old u + selectedCapUpper I nu l u) / 2

def selectedBoxCapCheck {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (l u : Fin n → ℚ) : Bool :=
  decide (selectedCapLower I old u < selectedCapUpper I nu l u)

theorem selectedCapLower_old_le {n : ℕ} (I : Finset (Fin n)) (old : ℚ) (u : Fin n → ℚ) :
    old ≤ selectedCapLower I old u :=
  Finset.le_max' _ _ (by simp [selectedCapLowerSet])

theorem selectedCapLower_half_le {n : ℕ} (I : Finset (Fin n)) (old : ℚ) (u : Fin n → ℚ) :
    1 / 2 ≤ selectedCapLower I old u :=
  Finset.le_max' _ _ (by simp [selectedCapLowerSet])

theorem selectedCapLower_prefix_le {n : ℕ} (I : Finset (Fin n)) (old : ℚ)
    (u : Fin n → ℚ) (j : Fin n) :
    prefixSquareExpr u j ≤ selectedCapLower I old u := by
  apply Finset.le_max'
  simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_univ _, rfl⟩))

theorem selectedCapLower_selected_le {n : ℕ} (I : Finset (Fin n)) (old : ℚ)
    (u : Fin n → ℚ) (j : Fin n) (hj : j ∉ I) :
    selectedSquareExpr I u j ≤ selectedCapLower I old u := by
  apply Finset.le_max'
  simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩))

theorem selectedBoxCap_between {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (l u : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu l u = true) :
    selectedCapLower I old u < selectedBoxCap I old nu l u ∧
      selectedBoxCap I old nu l u < selectedCapUpper I nu l u := by
  have h := of_decide_eq_true hc
  dsimp [selectedBoxCap]
  constructor <;> linarith

theorem prefixSquareExpr_mono {n : ℕ} {t u : Fin n → ℝ}
    (h : ∀ i, t i ≤ u i) (j : Fin n) : prefixSquareExpr t j ≤ prefixSquareExpr u j := by
  exact add_le_add (Finset.sum_le_sum (fun k _ => h k)) (by nlinarith [h j])

theorem selectedSquareExpr_mono {n : ℕ} (I : Finset (Fin n)) {t u : Fin n → ℝ}
    (h : ∀ i, t i ≤ u i) (j : Fin n) :
    selectedSquareExpr I t j ≤ selectedSquareExpr I u j := by
  exact add_le_add
    (add_le_add (Finset.sum_le_sum (fun k _ => h k)) (Finset.sum_le_sum (fun k _ => h k)))
    (by nlinarith [h j])

theorem cast_prefixSquareExpr {n : ℕ} (t : Fin n → ℚ) (j : Fin n) :
    ((prefixSquareExpr t j : ℚ) : ℝ) = prefixSquareExpr (fun k => (t k : ℝ)) j := by
  simp [prefixSquareExpr]

theorem cast_selectedSquareExpr {n : ℕ} (I : Finset (Fin n)) (t : Fin n → ℚ) (j : Fin n) :
    ((selectedSquareExpr I t j : ℚ) : ℝ) = selectedSquareExpr I (fun k => (t k : ℝ)) j := by
  simp [selectedSquareExpr]

/-- All licensing inequalities hold on the closed box for the same
explicit rational cap. No sampling or corner-value assumption is used. -/
theorem selectedBoxCapCheck_sound {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (l u : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu l u = true)
    (t : Fin n → ℝ) (hl : ∀ i, (l i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (u i : ℝ)) :
    (old : ℝ) < selectedBoxCap I old nu l u ∧
      (selectedBoxCap I old nu l u : ℝ) < nu ∧
      (1 / 2 : ℝ) < selectedBoxCap I old nu l u ∧
      (∀ j, prefixSquareExpr t j < selectedBoxCap I old nu l u) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < selectedBoxCap I old nu l u) ∧
      (selectedBoxCap I old nu l u : ℝ) < v (∑ k ∈ I, t k) := by
  have hb := selectedBoxCap_between I old nu l u hc
  have hlow : (selectedCapLower I old u : ℝ) < selectedBoxCap I old nu l u := by
    exact_mod_cast hb.1
  have hhigh : (selectedBoxCap I old nu l u : ℝ) < selectedCapUpper I nu l u := by
    exact_mod_cast hb.2
  have hold : (old : ℝ) ≤ selectedCapLower I old u := by
    exact_mod_cast selectedCapLower_old_le I old u
  have hhalf : (1 / 2 : ℝ) ≤ selectedCapLower I old u := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr (selectedCapLower_half_le I old u)
    push_cast at hh
    exact hh
  have htop : (selectedCapUpper I nu l u : ℝ) =
      min (nu : ℝ) (qVLo (∑ k ∈ I, l k) (∑ k ∈ I, u k) : ℝ) := by
    simp [selectedCapUpper]
  rw [htop] at hhigh
  refine ⟨hold.trans_lt hlow, hhigh.trans_le (min_le_left _ _), hhalf.trans_lt hlow,
    ?_, ?_, ?_⟩
  · intro j
    have hj : ((prefixSquareExpr u j : ℚ) : ℝ) ≤ selectedCapLower I old u := by
      exact_mod_cast selectedCapLower_prefix_le I old u j
    rw [cast_prefixSquareExpr] at hj
    exact (prefixSquareExpr_mono hu j).trans_lt (hj.trans_lt hlow)
  · intro j hj
    have hg : ((selectedSquareExpr I u j : ℚ) : ℝ) ≤ selectedCapLower I old u := by
      exact_mod_cast selectedCapLower_selected_le I old u j hj
    rw [cast_selectedSquareExpr] at hg
    exact (selectedSquareExpr_mono I hu j).trans_lt (hg.trans_lt hlow)
  · have hls : ((∑ k ∈ I, l k : ℚ) : ℝ) ≤ ∑ k ∈ I, t k := by
      push_cast
      exact Finset.sum_le_sum (fun k _ => hl k)
    have hus : (∑ k ∈ I, t k) ≤ ((∑ k ∈ I, u k : ℚ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum (fun k _ => hu k)
    exact (hhigh.trans_le (min_le_right _ _)).trans_le (qVLo_le_v hls hus)

/-- Any rational level strictly inside all endpoint tests makes the
explicit midpoint check succeed. -/
theorem selectedBoxCapCheck_of_witness {n : ℕ} (I : Finset (Fin n))
    (old nu lambda : ℚ) (l u : Fin n → ℚ)
    (ho : old < lambda) (hn : lambda < nu) (hh : 1 / 2 < lambda)
    (hp : ∀ j, prefixSquareExpr u j < lambda)
    (hs : ∀ j ∉ I, selectedSquareExpr I u j < lambda)
    (hv : lambda < qVLo (∑ k ∈ I, l k) (∑ k ∈ I, u k)) :
    selectedBoxCapCheck I old nu l u = true := by
  have hlo : selectedCapLower I old u < lambda := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro a ha
    simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at ha
    rcases ha with rfl | rfl | ⟨j, _, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ho
    · exact hh
    · exact hp j
    · exact hs j (Finset.mem_sdiff.mp hj).2
  exact decide_eq_true (hlo.trans (lt_min hn hv))

theorem continuous_prefixSquareExpr {n : ℕ} (j : Fin n) :
    Continuous (fun t : Fin n → ℝ => prefixSquareExpr t j) := by
  unfold prefixSquareExpr
  fun_prop

theorem continuous_selectedSquareExpr {n : ℕ} (I : Finset (Fin n)) (j : Fin n) :
    Continuous (fun t : Fin n → ℝ => selectedSquareExpr I t j) := by
  unfold selectedSquareExpr
  fun_prop

/-- Strict pointwise license implies a common neighborhood of endpoint
pairs on which the *constant-cap* check succeeds. Thus further box
refinement is justified by an actual existence theorem, not by testing
the original rectangle only at corners. The radius precedes all rational
endpoint pairs; those pairs need not themselves be ordered here. -/
theorem exists_selectedBoxCapCheck_radius {n : ℕ} (I : Finset (Fin n))
    (old nu lambda : ℚ) (t : Fin n → ℝ)
    (ho : old < lambda) (hn : lambda < nu) (hh : 1 / 2 < lambda)
    (hp : ∀ j, prefixSquareExpr t j < (lambda : ℝ))
    (hs : ∀ j ∉ I, selectedSquareExpr I t j < (lambda : ℝ))
    (hv : (lambda : ℝ) < v (∑ k ∈ I, t k)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ l u : Fin n → ℚ,
      dist (fun i => (l i : ℝ)) t < delta →
      dist (fun i => (u i : ℝ)) t < delta →
      selectedBoxCapCheck I old nu l u = true := by
  have hep : ∀ᶠ u : Fin n → ℝ in 𝓝 t,
      ∀ j, prefixSquareExpr u j < (lambda : ℝ) := by
    apply eventually_all.mpr
    intro j
    exact (continuous_prefixSquareExpr j).continuousAt.eventually_lt
      continuousAt_const (hp j)
  have hes : ∀ᶠ u : Fin n → ℝ in 𝓝 t,
      ∀ j ∉ I, selectedSquareExpr I u j < (lambda : ℝ) := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j ∈ I
    · exact Filter.Eventually.of_forall (fun _ h => (h hj).elim)
    · exact ((continuous_selectedSquareExpr I j).continuousAt.eventually_lt
        continuousAt_const (hs j hj)).mono (fun _ h _ => h)
  rw [v_eq_min] at hv
  have hA : Continuous (fun s : Fin n → ℝ => A (∑ k ∈ I, s k)) := by
    unfold A
    fun_prop
  have hC : Continuous (fun s : Fin n → ℝ => C (∑ k ∈ I, s k)) := by
    unfold C
    fun_prop
  have heA : ∀ᶠ l : Fin n → ℝ in 𝓝 t, (lambda : ℝ) < A (∑ k ∈ I, l k) :=
    continuousAt_const.eventually_lt hA.continuousAt (lt_min_iff.mp hv).1
  have heC : ∀ᶠ u : Fin n → ℝ in 𝓝 t, (lambda : ℝ) < C (∑ k ∈ I, u k) :=
    continuousAt_const.eventually_lt hC.continuousAt (lt_min_iff.mp hv).2
  obtain ⟨dl, hdl, hleft⟩ := Metric.eventually_nhds_iff.mp heA
  obtain ⟨du, hdu, hright⟩ := Metric.eventually_nhds_iff.mp (hep.and (hes.and heC))
  refine ⟨min dl du, lt_min hdl hdu, ?_⟩
  intro l u hl hu
  have hlA := hleft (hl.trans_le (min_le_left _ _))
  obtain ⟨hpU, hsU, hUC⟩ := hright (hu.trans_le (min_le_right _ _))
  apply selectedBoxCapCheck_of_witness I old nu lambda l u ho hn hh
  · intro j
    have h := hpU j
    rw [← cast_prefixSquareExpr] at h
    exact_mod_cast h
  · intro j hj
    have h := hsU j hj
    rw [← cast_selectedSquareExpr] at h
    exact_mod_cast h
  · have hlow : (lambda : ℝ) <
        (qVLo (∑ k ∈ I, l k) (∑ k ∈ I, u k) : ℝ) := by
      rw [cast_qVLo]
      apply lt_min
      · simpa only [Rat.cast_sum] using hlA
      · simpa only [Rat.cast_sum] using hUC
    exact_mod_cast hlow

/-- The pointwise strict selected-prefix license before a common constant
cap has been chosen. The inherited cap is fixed on the old coarse cell. -/
def SelectedPrefixLicense {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (t : Fin n → ℝ) : Prop :=
  (old : ℝ) < min (nu : ℝ) (v (∑ k ∈ I, t k)) ∧
    (1 / 2 : ℝ) < min (nu : ℝ) (v (∑ k ∈ I, t k)) ∧
    (∀ j, prefixSquareExpr t j < min (nu : ℝ) (v (∑ k ∈ I, t k))) ∧
    (∀ j ∉ I, selectedSquareExpr I t j < min (nu : ℝ) (v (∑ k ∈ I, t k)))

/-- Rational density and the finite maximum construct the intermediate
level from the strict license itself; no selected level is an input. -/
theorem exists_selectedBoxCapCheck_radius_of_strict {n : ℕ}
    (I : Finset (Fin n)) (old nu : ℚ) (t : Fin n → ℝ)
    (h : SelectedPrefixLicense I old nu t) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ l u : Fin n → ℚ,
      dist (fun i => (l i : ℝ)) t < delta →
      dist (fun i => (u i : ℝ)) t < delta →
      selectedBoxCapCheck I old nu l u = true := by
  classical
  let S : Finset ℝ := insert (old : ℝ) (insert (1 / 2)
    (Finset.univ.image (prefixSquareExpr t) ∪
      (Finset.univ \ I).image (selectedSquareExpr I t)))
  have hS : S.Nonempty := ⟨old, by simp [S]⟩
  have hmax : S.max' hS < min (nu : ℝ) (v (∑ k ∈ I, t k)) := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at ha
    rcases ha with rfl | rfl | ⟨j, _, rfl⟩ | ⟨j, hj, rfl⟩
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1 j
    · exact h.2.2.2 j (Finset.mem_sdiff.mp hj).2
  obtain ⟨lambda, hlamlo, hlamhi⟩ := exists_rat_btwn hmax
  have hbelow (a : ℝ) (ha : a ∈ S) : a < (lambda : ℝ) :=
    (Finset.le_max' S a ha).trans_lt hlamlo
  apply exists_selectedBoxCapCheck_radius I old nu lambda t
  · exact_mod_cast hbelow old (by simp [S])
  · exact_mod_cast hlamhi.trans_le (min_le_left _ _)
  · have hh := hbelow (1 / 2) (by simp [S])
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hh
  · intro j
    apply hbelow
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_univ _, rfl⟩))
  · intro j hj
    apply hbelow
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩))
  · exact hlamhi.trans_le (min_le_right _ _)

/-- A finite natural subproduct obeys the corresponding exponent bound. -/
theorem naturalSubproduct_le_rpow_sum {n : ℕ} (N : ℝ) (hN : 0 < N)
    (p : Fin n → ℕ) (t : Fin n → ℝ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i)
    (J : Finset (Fin n)) :
    ((∏ i ∈ J, p i : ℕ) : ℝ) ≤ N ^ (∑ i ∈ J, t i) := by
  rw [Nat.cast_prod, Real.rpow_sum_of_pos hN]
  exact Finset.prod_le_prod (fun i _ => Nat.cast_nonneg (p i)) (fun i _ => hp i)

theorem prefixSquareExpr_actual_gate {n : ℕ} (N : ℝ) (hN : 1 < N)
    (p : Fin n → ℕ) (t : Fin n → ℝ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i)
    (j : Fin n) {lambda : ℝ} (hgate : prefixSquareExpr t j < lambda) :
    ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ lambda := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  calc
    _ ≤ N ^ (∑ i ∈ Finset.univ.filter (fun i => i < j), t i) * (N ^ t j) ^ 2 :=
      mul_le_mul (naturalSubproduct_le_rpow_sum N hNpos p t hp _)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hp j) 2) (by positivity) (by positivity)
    _ = N ^ prefixSquareExpr t j := by
      rw [prefixSquareExpr, Real.rpow_add hNpos,
        show 2 * t j = t j * (2 : ℕ) by ring, Real.rpow_mul_natCast hNpos.le]
    _ < N ^ lambda := Real.rpow_lt_rpow_of_exponent_lt hN hgate

theorem selectedSquareExpr_actual_gate {n : ℕ} (I : Finset (Fin n))
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (t : Fin n → ℝ)
    (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) (j : Fin n) {lambda : ℝ}
    (hgate : selectedSquareExpr I t j < lambda) :
    ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ lambda := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  calc
    _ ≤ N ^ (∑ i ∈ I, t i) *
        N ^ (∑ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), t i) * (N ^ t j) ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul (naturalSubproduct_le_rpow_sum N hNpos p t hp I)
          (naturalSubproduct_le_rpow_sum N hNpos p t hp _) (by positivity) (by positivity)
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp j) 2
      · positivity
      · positivity
    _ = N ^ selectedSquareExpr I t j := by
      rw [selectedSquareExpr, Real.rpow_add hNpos, Real.rpow_add hNpos,
        show 2 * t j = t j * (2 : ℕ) by ring, Real.rpow_mul_natCast hNpos.le]
    _ < N ^ lambda := Real.rpow_lt_rpow_of_exponent_lt hN hgate

/-- The constructed cap licenses the actual complete and selected integer
square products everywhere in the box, with their precise subproducts. -/
theorem selectedBoxCapCheck_actual_square_gates {n : ℕ} (I : Finset (Fin n))
    (old nu : ℚ) (l u : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu l u = true)
    (t : Fin n → ℝ) (hl : ∀ i, (l i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (u i : ℝ))
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ (selectedBoxCap I old nu l u : ℝ)) ∧
    (∀ j ∉ I, ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ (selectedBoxCap I old nu l u : ℝ)) := by
  have hg := selectedBoxCapCheck_sound I old nu l u hc t hl hu
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hg.2.2.2.1 j),
    fun j hj => selectedSquareExpr_actual_gate I N hN p t hp j (hg.2.2.2.2.1 j hj)⟩

end ImbalancedChen
