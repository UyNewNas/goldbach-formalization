import ImbalancedChen.P2OriginalAscendingEighthCapDictionary
import ImbalancedChen.RosserCompactParameterBounds
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Saving16 uses the original fourteen ascending cells, indices 0..14 except 7,
and R=C(t2+t3). This module constructs one finite causal third-cap mesh on
any compact retained part of that union. Its precision is chosen before N,
using the actual four strict history gaps. The third cap reads only the
first-three ancestor, not a future descendant or an observed AP error.

This is not a certificate that a particular old common policy has already
been installed: gluing these lower caps into all old branches, preservation
of earlier adopted gains, and the integral/compilation reserves remain open.
-/
namespace ImbalancedChen.P2OriginalFourteenCausalHistoryMesh

noncomputable section
open scoped Classical BigOperators
open P2OriginalAscendingEighthCapDictionary VariableEnvelope

abbrev Label := ℤ × ℤ

def pointLabel (tau : ℝ) (t : Point) : Label :=
  (⌊t 1 / tau⌋, ⌊t 2 / tau⌋)

def labelCap (tau : ℝ) (k : Label) : ℝ :=
  C (((k.1 : ℝ) + 1) * tau + ((k.2 : ℝ) + 1) * tau)

def finiteThirdCap (tau : ℝ) (t : Point) : ℝ := labelCap tau (pointLabel tau t)

/-- The common alphabet is finite and is selected independently of N. -/
def labels (tau : ℝ) : Finset Label :=
  (Finset.Icc 0 (⌊mu / tau⌋ : ℤ)).product (Finset.Icc 0 (⌊mu / tau⌋ : ℤ))

private theorem upper_endpoint_bounds (tau x : ℝ) (htau : 0 < tau) :
    x < (((⌊x / tau⌋ : ℤ) : ℝ) + 1) * tau ∧
      (((⌊x / tau⌋ : ℤ) : ℝ) + 1) * tau ≤ x + tau := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x / tau)) htau.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / tau)) htau
  rw [div_mul_cancel₀ x htau.ne'] at hlo hhi
  exact ⟨hhi, by nlinarith only [hlo]⟩

/-- Uniform exact error for the descending D23 branch. No third cap or
history inequality is supplied as a hypothesis. -/
theorem finiteThirdCap_bounds (tau : ℝ) (htau : 0 < tau) (t : Point) :
    R t - 3 * tau ≤ finiteThirdCap tau t ∧ finiteThirdCap tau t < R t := by
  have h1 := upper_endpoint_bounds tau (t 1) htau
  have h2 := upper_endpoint_bounds tau (t 2) htau
  dsimp [finiteThirdCap, labelCap, pointLabel, R, d, C]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Every actual saving16 point has a label in the same finite alphabet.
The argument uses the real physical order and positivity, not enumeration. -/
theorem pointLabel_mem {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (tau : ℝ) (htau : 0 < tau) :
    pointLabel tau t ∈ labels tau := by
  have h1 : t 1 ≤ mu := (h.order (by decide : (0 : Fin 8) < 1)).le.trans h.largest.le
  have h2 : t 2 ≤ mu := (h.order (by decide : (0 : Fin 8) < 2)).le.trans h.largest.le
  have hfloor (x : ℝ) (hx : 0 ≤ x) (hxu : x ≤ mu) :
      (0 : ℤ) ≤ ⌊x / tau⌋ ∧ ⌊x / tau⌋ ≤ ⌊mu / tau⌋ :=
    ⟨Int.floor_nonneg.mpr (div_nonneg hx htau.le),
      Int.floor_mono ((div_le_div_iff_of_pos_right htau).mpr hxu)⟩
  simpa only [pointLabel, labels, Finset.mem_product, Finset.mem_Icc] using
    And.intro (hfloor (t 1) (h.coordinate_pos 1).le h1)
      (hfloor (t 2) (h.coordinate_pos 2).le h2)

/-- Explicit common refinement: old labels are retained as the first
component; no old equality/inheritance region is removed by relabeling. -/
def refinedLabel {α : Type*} (old : Point → α) (tau : ℝ) (t : Point) : α × Label :=
  (old t, pointLabel tau t)

theorem refinedLabel_preserves_old {α : Type*} (old : Point → α) (tau : ℝ) (t : Point) :
    (refinedLabel old tau t).1 = old t := rfl

theorem refinedLabel_mem {α : Type*} [DecidableEq α]
    (old : Point → α) (oldLabels : Finset α) (tau : ℝ) (htau : 0 < tau)
    {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (hold : old t ∈ oldLabels) :
    refinedLabel old tau t ∈ oldLabels.product (labels tau) :=
  Finset.mem_product.mpr ⟨hold, pointLabel_mem h tau htau⟩

def historyCeiling (t : Point) : ℝ :=
  max (3 * t 0) (max (oddCube t 2) (max (oddCube t 4) (oddCube t 6)))

def historyGap (t : Point) : ℝ := R t - historyCeiling t

theorem historyGap_continuous : Continuous historyGap := by
  unfold historyGap historyCeiling R d C oddCube prefixSum
  fun_prop

theorem historyGap_pos {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : 0 < historyGap t := by
  apply sub_pos.mpr
  exact max_lt h.first_history (max_lt h.history3 (max_lt h.history5 h.history7))

theorem histories_below_mesh (tau delta : ℝ) (htau : 0 < tau)
    (hprecision : 3 * tau < delta) (t : Point) (hgap : delta ≤ historyGap t) :
    3 * t 0 < finiteThirdCap tau t ∧
      oddCube t 2 < finiteThirdCap tau t ∧
      oddCube t 4 < finiteThirdCap tau t ∧
      oddCube t 6 < finiteThirdCap tau t := by
  have hcap := (finiteThirdCap_bounds tau htau t).1
  have hh : historyCeiling t < finiteThirdCap tau t := by
    dsimp [historyGap] at hgap
    linarith only [hcap, hprecision, hgap]
  have hh' := (max_lt_iff.mp hh)
  have hh'' := max_lt_iff.mp hh'.2
  exact ⟨hh'.1, hh''.1, (max_lt_iff.mp hh''.2).1, (max_lt_iff.mp hh''.2).2⟩

/-- The precision precedes every point and every eventual N. All four old
histories survive one mesh on the whole retained fourteen-cell union.
Compact containment is a geometry input, not a bound for the saving. -/
theorem exists_common_history_precision
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (T : Set Point)
    (hT : IsCompact T) (hsub : ∀ t ∈ T, SelectedFamilyGuard patterns t) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ t ∈ T,
      pointLabel tau t ∈ labels tau ∧
      3 * t 0 < finiteThirdCap tau t ∧
      oddCube t 2 < finiteThirdCap tau t ∧
      oddCube t 4 < finiteThirdCap tau t ∧
      oddCube t 6 < finiteThirdCap tau t ∧
      finiteThirdCap tau t < R t := by
  have hpos : ∀ t ∈ T, 0 < historyGap t := by
    intro t ht
    obtain ⟨i, hi, hcell⟩ := hsub t ht
    exact historyGap_pos hcell
  obtain ⟨delta, hdelta, hfloor⟩ :=
    hT.exists_forall_le' historyGap_continuous.continuousOn hpos
  refine ⟨delta / 6, by positivity, ?_⟩
  intro t ht
  obtain ⟨i, hi, hcell⟩ := hsub t ht
  have htau : 0 < delta / 6 := by positivity
  have hhist := histories_below_mesh (delta / 6) delta htau (by linarith) t (hfloor t ht)
  exact ⟨pointLabel_mem hcell _ htau, hhist.1, hhist.2.1, hhist.2.2.1,
    hhist.2.2.2, (finiteThirdCap_bounds _ htau t).2⟩

/-- Arbitrary requested cap accuracy is compatible with the same history
retention. This does not itself pay any integral/compiler loss. -/
theorem exists_common_history_precision_with_error
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (T : Set Point)
    (hT : IsCompact T) (hsub : ∀ t ∈ T, SelectedFamilyGuard patterns t)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ 3 * tau < epsilon ∧ ∀ t ∈ T,
      pointLabel tau t ∈ labels tau ∧
      3 * t 0 < finiteThirdCap tau t ∧
      oddCube t 2 < finiteThirdCap tau t ∧
      oddCube t 4 < finiteThirdCap tau t ∧
      oddCube t 6 < finiteThirdCap tau t ∧
      0 < R t - finiteThirdCap tau t ∧ R t - finiteThirdCap tau t < epsilon := by
  have hpos : ∀ t ∈ T, 0 < historyGap t := by
    intro t ht
    obtain ⟨i, hi, hcell⟩ := hsub t ht
    exact historyGap_pos hcell
  obtain ⟨delta, hdelta, hfloor⟩ :=
    hT.exists_forall_le' historyGap_continuous.continuousOn hpos
  let tau := min delta epsilon / 6
  have htau : 0 < tau := div_pos (lt_min hdelta hepsilon) (by norm_num)
  have htd : 3 * tau < delta := by
    have := min_le_left delta epsilon
    dsimp [tau]
    linarith
  have hte : 3 * tau < epsilon := by
    have := min_le_right delta epsilon
    dsimp [tau]
    linarith
  refine ⟨tau, htau, hte, ?_⟩
  intro t ht
  obtain ⟨i, hi, hcell⟩ := hsub t ht
  have hh := histories_below_mesh tau delta htau htd t (hfloor t ht)
  have hb := finiteThirdCap_bounds tau htau t
  exact ⟨pointLabel_mem hcell tau htau, hh.1, hh.2.1, hh.2.2.1,
    hh.2.2.2, sub_pos.mpr hb.2, by linarith only [hb.1, hte]⟩
/-- Runtime evaluation reads the frozen first-three ancestor only. -/
def historyLabel (tau N : ℝ) (pre : List ℕ) : Label :=
  let u := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  (⌊u 1 / tau⌋, ⌊u 2 / tau⌋)

def causalThirdExponent (tau N : ℝ) (pre : List ℕ) : ℝ :=
  labelCap tau (historyLabel tau N pre)

theorem causalThirdExponent_same_ancestor (tau N : ℝ) (pre other : List ℕ)
    (h : rosserAncestor 3 pre = rosserAncestor 3 other) :
    causalThirdExponent tau N pre = causalThirdExponent tau N other := by
  simp only [causalThirdExponent, historyLabel, h]

/-- The causal evaluation is exactly the geometric mesh, not a new
future-dependent cap selected from the eighth cell label. -/
theorem causalThirdExponent_eighth (tau N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) :
    causalThirdExponent tau N pre =
      finiteThirdCap tau (primeHistoryLogCoordinates N 8 pre) := by
  have h1 := primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 8) (1 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 8) (2 : Fin 3)
  change primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1 =
    primeHistoryLogCoordinates N 8 pre 1 at h1
  change primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2 =
    primeHistoryLogCoordinates N 8 pre 2 at h2
  simp only [causalThirdExponent, historyLabel, finiteThirdCap, pointLabel, h1, h2]
/-- On every retained point, any later inherited sixth cap above this
chosen third cap has the actual lower history guard. Equality with R is
never imposed; the actual cap remains free throughout [lambda3,R]. -/
theorem common_precision_supplies_parent_history
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (T : Set Point)
    (hT : IsCompact T) (hsub : ∀ t ∈ T, SelectedFamilyGuard patterns t) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 →
      primeHistoryLogCoordinates N 8 pre ∈ T → ∀ current : ℝ,
      causalThirdExponent tau N pre ≤ current →
      current ≤ R (primeHistoryLogCoordinates N 8 pre) →
      CurrentParentGuard (primeHistoryLogCoordinates N 8 pre) current := by
  obtain ⟨tau, htau, hmesh⟩ := exists_common_history_precision patterns T hT hsub
  refine ⟨tau, htau, ?_⟩
  intro N pre hlen hpre current hlo hhi
  rw [causalThirdExponent_eighth tau N pre hlen] at hlo
  exact ⟨(hmesh _ hpre).2.2.2.2.1.trans_le hlo, hhi⟩

end
end ImbalancedChen.P2OriginalFourteenCausalHistoryMesh


