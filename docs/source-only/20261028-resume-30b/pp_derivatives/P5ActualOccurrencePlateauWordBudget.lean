import ImbalancedChen.P5OccurrenceWordFourFactorLeibniz
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The first concrete missing cutoff factor from the HB occurrence chart.
The scalar c is DEFINED from Mathlib's genuine smooth transition. Its
plateau, support, smoothness and all finite word bounds are consequences.
No derivative budget for c or for its tensor is a premise.

The constant is selected once for all m <= 6*kStar and word length
<= 12*kStar, before T, original rank, owner map, block scales or signs.
The complete-product eta and grouped psi factors remain explicit separate
obligations in the final corollary.
-/
namespace ImbalancedChen.P5Z.ActualOccurrencePlateauWordBudget
noncomputable section
open Classical Set
open scoped BigOperators
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift

/-- One fixed genuine smooth plateau, independent of every arithmetic
parameter. It is one on the complete closed atom-log interval [0,log 2]. -/
def c (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) *
    Real.smoothTransition (Real.log 2 + 1 - x)

theorem c_smooth : ContDiff ℝ ∞ c := by
  have hl : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (x + 1)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
  have hr : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (Real.log 2 + 1 - x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  exact hl.mul hr

theorem c_bounds (x : ℝ) : 0 ≤ c x ∧ c x ≤ 1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (by norm_num)

theorem c_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (Real.log 2)) : c x = 1 := by
  unfold c
  rw [Real.smoothTransition.one_of_one_le (by linarith [hx.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2])]
  norm_num

theorem c_eq_zero_of_left {x : ℝ} (hx : x ≤ -1) : c x = 0 := by
  unfold c
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  exact zero_mul _

theorem c_eq_zero_of_right {x : ℝ} (hx : Real.log 2 + 1 ≤ x) : c x = 0 := by
  unfold c
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : Real.log 2 + 1 - x ≤ 0)]
  exact mul_zero _

theorem c_nonzero_support {x : ℝ} (hx : c x ≠ 0) :
    -1 < x ∧ x < Real.log 2 + 1 := by
  constructor
  · by_contra h
    exact hx (c_eq_zero_of_left (le_of_not_gt h))
  · by_contra h
    exact hx (c_eq_zero_of_right (le_of_not_gt h))

/-- The actual occurrence plateau of the paper, including m=0. -/
def plateau (m : ℕ) (z : Fin m → ℝ) : ℝ := ∏ a : Fin m, c (z a)

theorem plateau_smooth (m : ℕ) : ContDiff ℝ ∞ (plateau m) := by
  unfold plateau
  apply contDiff_prod
  intro a ha
  exact c_smooth.comp (contDiff_apply ℝ ℝ a)

theorem plateau_compact (m : ℕ) : HasCompactSupport (plateau m) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun a : Fin m =>
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) (Real.log 2 + 1)))))
  intro z hz a ha
  have hfactor : c (z a) ≠ 0 := by
    intro heq
    exact hz (Finset.prod_eq_zero (Finset.mem_univ a) heq)
  have h := c_nonzero_support hfactor
  exact ⟨h.1.le, h.2.le⟩

/-- The endpoints are the actual right-closed (U,2U] atoms, not an altered
half-open convention. All factors equal one on every such integer tuple. -/
theorem plateau_rightClosed_atom {m : ℕ} (U : Fin m → ℝ) (n : Fin m → ℕ)
    (hU : ∀ a, 0 < U a) (hlo : ∀ a, U a < (n a : ℝ))
    (hhi : ∀ a, (n a : ℝ) ≤ 2 * U a) :
    plateau m (fun a => Real.log ((n a : ℝ) / U a)) = 1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro a ha
  apply c_eq_one
  have hn : 0 < (n a : ℝ) := (hU a).trans (hlo a)
  have hr : 0 < (n a : ℝ) / U a := div_pos hn (hU a)
  constructor
  · apply Real.log_nonneg
    apply (le_div_iff₀ (hU a)).mpr
    linarith [hlo a]
  · apply Real.log_le_log hr
    apply (div_le_iff₀ (hU a)).mpr
    exact hhi a

/-- Occurrence differentiation preserves genuine compact support. The
support fact is the existing Frechet-derivative support theorem. -/
theorem occOne_compact {m : ℕ} (a : Fin m) (f : OccSpace m → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    HasCompactSupport (occOne a f) := by
  have heq : occOne a f = fun z => fderiv ℝ f z (Pi.single a 1) := by
    funext z
    exact occOne_eq_fderiv a f z ((hf.differentiable (by simp)) z)
  have hs : tsupport (occOne a f) ⊆ tsupport f := by
    rw [heq]
    exact tsupport_fderiv_apply_subset ℝ (Pi.single a 1)
  exact hc.mono' ((subset_tsupport _).trans hs)

theorem occWord_compact {m : ℕ} (w : List (Fin m))
    (f : OccSpace m → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    HasCompactSupport (occWord w f) := by
  induction w with
  | nil => simpa [occWord] using hc
  | cons a w ih =>
      simpa [occWord] using
        occOne_compact a (occWord w f) (occWord_smooth w f hf) ih

/-- Compactness supplies a bound for a real smooth compact profile. -/
theorem exists_compact_profile_bound {m : ℕ} (f : OccSpace m → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ z, |f z| ≤ B := by
  obtain ⟨B, hB⟩ := hc.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport f
  · have hbz : |f z| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB z hz
    exact hbz.trans (le_max_left _ _)
  · have hzero : f z = 0 := by
      by_contra hn
      exact hz (subset_closure hn)
    rw [hzero, abs_zero]
    exact zero_le_one.trans (le_max_right _ _)

/-- Explicit finite bank of every ordered word up to the requested length.
Repeated letters are retained, so no false distinctness premise is used. -/
def wordBank (m : ℕ) : ℕ → List (List (Fin m))
  | 0 => [[]]
  | r + 1 => [] :: (List.finRange m).flatMap
      (fun a => (wordBank m r).map (fun w => a :: w))

theorem mem_wordBank {m : ℕ} (r : ℕ) (w : List (Fin m)) :
    w ∈ wordBank m r ↔ w.length ≤ r := by
  induction r generalizing w with
  | zero => cases w <;> simp [wordBank]
  | succ r ih =>
      cases w with
      | nil => simp [wordBank]
      | cons a w =>
          simp [wordBank, List.mem_flatMap, ih] <;> omega

theorem finite_profile_bounds {ι : Type*} {m : ℕ} (L : List ι)
    (f : ι → OccSpace m → ℝ)
    (h : ∀ i ∈ L, ∃ B : ℝ, 1 ≤ B ∧ ∀ z, |f i z| ≤ B) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ∈ L, ∀ z, |f i z| ≤ B := by
  revert h
  induction L with
  | nil => intro h; exact ⟨1, le_rfl, by simp⟩
  | cons i L ih =>
      intro h
      obtain ⟨Bi, hBi, hi⟩ := h i (by simp)
      obtain ⟨BL, hBL, hL⟩ := ih (fun j hj => h j (by simp [hj]))
      refine ⟨max Bi BL, hBi.trans (le_max_left _ _), ?_⟩
      intro j hj z
      rcases List.mem_cons.mp hj with rfl | hj
      · exact (hi z).trans (le_max_left _ _)
      · exact (hL j hj z).trans (le_max_right _ _)

theorem exists_plateau_word_budget (m r : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ w : List (Fin m), w.length ≤ r →
      ∀ z, |occWord w (plateau m) z| ≤ B := by
  have each : ∀ w ∈ wordBank m r, ∃ B : ℝ, 1 ≤ B ∧
      ∀ z, |occWord w (plateau m) z| ≤ B := by
    intro w hw
    exact exists_compact_profile_bound _
      (occWord_smooth w (plateau m) (plateau_smooth m)).continuous
      (occWord_compact w (plateau m) (plateau_smooth m) (plateau_compact m))
  obtain ⟨B, hB, hb⟩ := finite_profile_bounds (wordBank m r)
    (fun w => occWord w (plateau m)) each
  exact ⟨B, hB, fun w hw => hb w ((mem_wordBank r w).mpr hw)⟩

/-- The scalar is chosen BEFORE dimension, word, point and all arithmetic
parameters. The finite family includes the dimension-zero empty product. -/
theorem exists_uniform_plateau_word_budget (kStar : ℕ) :
    ∃ MC : ℝ, 1 ≤ MC ∧ ∀ (m : ℕ), m ≤ 6 * kStar →
      ∀ w : List (Fin m), w.length ≤ 12 * kStar →
        ∀ z, |occWord w (plateau m) z| ≤ MC := by
  choose B hB hb using
    (fun m : Fin (6 * kStar + 1) => exists_plateau_word_budget m.val (12 * kStar))
  refine ⟨∑ m : Fin (6 * kStar + 1), B m, ?_, ?_⟩
  · exact (hB 0).trans (Finset.single_le_sum
      (fun i hi => zero_le_one.trans (hB i)) (Finset.mem_univ 0))
  · intro m hm w hw z
    let i : Fin (6 * kStar + 1) := ⟨m, by omega⟩
    exact (hb i w hw z).trans (Finset.single_le_sum
      (fun j hj => zero_le_one.trans (hB j)) (Finset.mem_univ i))

/-- Eliminate the actual occurrence plateau's smoothness/budget premises
from the first-batch Family Leibniz estimate. Eta and grouped psi remain
separate local cutoff obligations, not final PP or D_T assumptions. -/
theorem family_chart_actual_plateau_bound {kStar : ℕ} (A : Family kStar) :
    ∃ CA BA : ℕ, ∃ MC : ℝ, 0 < CA ∧ 1 ≤ MC ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ)
        (w : List (Fin m)) (z : OccSpace m)
        (E P : OccSpace m → ℝ) (BE BP : ℝ),
        m ≤ 6 * kStar → w.length ≤ 12 * kStar →
        ContDiff ℝ ∞ E → ContDiff ℝ ∞ P → 0 ≤ BE → 0 ≤ BP →
        (∀ v : List (Fin m), v.length ≤ 12 * kStar → |occWord v E z| ≤ BE) →
        (∀ v : List (Fin m), v.length ≤ 12 * kStar → |occWord v P z| ≤ BP) →
        |occWord w (fun z => A.ambient T k
          (fun i => groupProduct owner U i z) * E z * P z * plateau m z) z| ≤
          (4 : ℝ) ^ w.length *
            (((CA : ℝ) * Real.log ((T : ℝ) + 2) ^ BA) * BE * BP * MC) := by
  obtain ⟨CA, BA, hCA, hfamily⟩ := family_four_chart_bound A
  obtain ⟨MC, hMC, hplateau⟩ := exists_uniform_plateau_word_budget kStar
  refine ⟨CA, BA, MC, hCA, hMC, ?_⟩
  intro T k m owner U w z E P BE BP hm hw hE hP hBE hBP bE bP
  exact hfamily T k m owner U w z E P (plateau m) BE BP MC hm hw
    hE hP (plateau_smooth m) hBE hBP (zero_le_one.trans hMC)
    bE bP (fun v hv => hplateau m hm v hv z)

end
end ImbalancedChen.P5Z.ActualOccurrencePlateauWordBudget
