import ImbalancedChen.P5OccurrenceLeibnizAllocation
import Mathlib

/-!
SOURCE ONLY. UNCOMPILED_ZERO_CREDIT. No kernel or compiler run.

The manuscript's HB chart has four smooth factors: the original ambient
profile, the complete-product cutoff, the grouped original-chart profile,
and the occurrence plateau. This file supplies the missing arbitrary-word
Leibniz argument, rather than assuming the resulting chart derivative bound.
All allocations are LISTS: their multiplicities, order, and repeated labels
are retained. The numerical constant is exactly 4 ^ word.length.
-/

namespace ImbalancedChen.P5Z.OccurrenceWordFourFactorLeibniz
noncomputable section
open Classical
open AllWordAmbientOccurrenceBound OccurrenceLeibnizAllocation
open GroupedOccurrenceLogShift AdmissibleAllRankIntegerGeometricFamily

abbrev OccSpace (m : ℕ) := Fin m → ℝ

/-- The coordinate curve has the actual constant coordinate tangent. -/
theorem coordinate_hasDerivAt {m : ℕ} (z : OccSpace m) (a : Fin m) :
    HasDerivAt (fun t : ℝ => z + Pi.single a t) (Pi.single a 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i = a
  · subst i
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (z a)
  · simpa [Pi.single_eq_of_ne hi] using
      (hasDerivAt_const (0 : ℝ) (z i))

/-- Identify the existing ordinary occurrence derivative with its Frechet
partial derivative. This prevents treating it as an abstract derivation. -/
theorem occOne_eq_fderiv {m : ℕ} (a : Fin m)
    (f : OccSpace m → ℝ) (z : OccSpace m)
    (hf : DifferentiableAt ℝ f z) :
    occOne a f z = fderiv ℝ f z (Pi.single a 1) := by
  have hc := coordinate_hasDerivAt z a
  simpa [occOne, Function.comp_def] using
    (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)).deriv

/-- Smoothness of all generated occurrence derivatives follows from genuine
smoothness of the profile; no differentiability fields are added to a chart. -/
theorem occOne_smooth {m : ℕ} (a : Fin m)
    (f : OccSpace m → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (occOne a f) := by
  have heq : occOne a f = fun z => fderiv ℝ f z (Pi.single a 1) := by
    funext z
    exact occOne_eq_fderiv a f z ((hf.differentiable (by simp)) z)
  rw [heq]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem occWord_smooth {m : ℕ} (w : List (Fin m))
    (f : OccSpace m → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (occWord w f) := by
  induction w with
  | nil => simpa [occWord] using hf
  | cons a w ih =>
      simpa [occWord] using occOne_smooth a (occWord w f) ih

theorem coordinate_differentiable {m : ℕ} (f : OccSpace m → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : OccSpace m) (a : Fin m) :
    DifferentiableAt ℝ (fun t : ℝ => f (z + Pi.single a t)) 0 := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => z + Pi.single a t) := by
    fun_prop
  exact ((hf.comp hc).differentiable (by simp)) 0

/-- A list sum is used because an allocation may occur with multiplicity. -/
def sumTerms {ι : Type*} {m : ℕ} (L : List ι)
    (F : ι → OccSpace m → ℝ) : OccSpace m → ℝ :=
  fun z => (L.map (fun i => F i z)).sum

@[simp] theorem sumTerms_nil {ι : Type*} {m : ℕ}
    (F : ι → OccSpace m → ℝ) : sumTerms [] F = 0 := rfl

@[simp] theorem sumTerms_cons {ι : Type*} {m : ℕ} (i : ι) (L : List ι)
    (F : ι → OccSpace m → ℝ) :
    sumTerms (i :: L) F = fun z => F i z + sumTerms L F z := rfl

@[simp] theorem sumTerms_append {ι : Type*} {m : ℕ} (L R : List ι)
    (F : ι → OccSpace m → ℝ) :
    sumTerms (L ++ R) F = fun z => sumTerms L F z + sumTerms R F z := by
  funext z
  simp [sumTerms, List.map_append, List.sum_append]

@[simp] theorem sumTerms_map {ι κ : Type*} {m : ℕ} (L : List ι)
    (g : ι → κ) (F : κ → OccSpace m → ℝ) :
    sumTerms (L.map g) F = sumTerms L (fun i => F (g i)) := by
  funext z
  simp [sumTerms, List.map_map]

theorem sumTerms_add {ι : Type*} {m : ℕ} (L : List ι)
    (F G : ι → OccSpace m → ℝ) (z : OccSpace m) :
    sumTerms L (fun i z => F i z + G i z) z =
      sumTerms L F z + sumTerms L G z := by
  induction L with
  | nil => simp [sumTerms]
  | cons i L ih =>
      change (F i z + G i z) + sumTerms L (fun i z => F i z + G i z) z =
        (F i z + sumTerms L F z) + (G i z + sumTerms L G z)
      rw [ih]
      ring

theorem sumTerms_congr {ι : Type*} {m : ℕ} (L : List ι)
    (F G : ι → OccSpace m → ℝ) (z : OccSpace m)
    (h : ∀ i ∈ L, F i z = G i z) : sumTerms L F z = sumTerms L G z := by
  revert h
  induction L with
  | nil => intro h; rfl
  | cons i L ih =>
      intro h
      change F i z + sumTerms L F z = G i z + sumTerms L G z
      rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem sumTerms_smooth {ι : Type*} {m : ℕ} (L : List ι)
    (F : ι → OccSpace m → ℝ)
    (hF : ∀ i ∈ L, ContDiff ℝ ∞ (F i)) : ContDiff ℝ ∞ (sumTerms L F) := by
  revert hF
  induction L with
  | nil => intro h; simpa [sumTerms] using (contDiff_const (c := (0 : ℝ)))
  | cons i L ih =>
      intro h
      exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- Differentiate the actual finite allocation sum. -/
theorem occOne_sumTerms {ι : Type*} {m : ℕ} (a : Fin m)
    (L : List ι) (F : ι → OccSpace m → ℝ) (z : OccSpace m)
    (hF : ∀ i ∈ L, ContDiff ℝ ∞ (F i)) :
    occOne a (sumTerms L F) z = sumTerms L (fun i => occOne a (F i)) z := by
  revert hF
  induction L with
  | nil => intro h; simp [sumTerms, occOne]
  | cons i L ih =>
      intro h
      have hL : ∀ j ∈ L, ContDiff ℝ ∞ (F j) :=
        fun j hj => h j (by simp [hj])
      calc
        occOne a (sumTerms (i :: L) F) z =
            occOne a (F i) z + occOne a (sumTerms L F) z :=
          occOne_add a (F i) (sumTerms L F) z
            (coordinate_differentiable (F i) (h i (by simp)) z a)
            (coordinate_differentiable (sumTerms L F) (sumTerms_smooth L F hL) z a)
        _ = sumTerms (i :: L) (fun i => occOne a (F i)) z := by
          rw [ih hL]
          rfl

structure FourWords (α : Type*) where
  ambient : List α
  eta : List α
  profile : List α
  plateau : List α

/-- Every letter goes to exactly one of four factors; an allocation is not
collapsed when the same original owner occurs more than once. -/
def fourAlloc {α : Type*} : List α → List (FourWords α)
  | [] => [⟨[], [], [], []⟩]
  | a :: w =>
      (fourAlloc w).map (fun p => ⟨a :: p.ambient, p.eta, p.profile, p.plateau⟩) ++
      (fourAlloc w).map (fun p => ⟨p.ambient, a :: p.eta, p.profile, p.plateau⟩) ++
      (fourAlloc w).map (fun p => ⟨p.ambient, p.eta, a :: p.profile, p.plateau⟩) ++
      (fourAlloc w).map (fun p => ⟨p.ambient, p.eta, p.profile, a :: p.plateau⟩)

theorem fourAlloc_length {α : Type*} (w : List α) :
    (fourAlloc w).length = 4 ^ w.length := by
  induction w with
  | nil => simp [fourAlloc]
  | cons a w ih =>
      simp only [fourAlloc, List.length_append, List.length_map, ih, List.length_cons,
        pow_succ]
      omega

theorem fourAlloc_letters {α : Type*} :
    ∀ w : List α, ∀ p ∈ fourAlloc w,
      p.ambient.length + p.eta.length + p.profile.length + p.plateau.length = w.length := by
  intro w
  induction w with
  | nil =>
      intro p hp
      simp only [fourAlloc, List.mem_singleton] at hp
      subst p
      rfl
  | cons a w ih =>
      intro p hp
      simp only [fourAlloc, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      all_goals
        have h := ih q hq
        simp only [List.length_cons]
        omega

def fourTerm {m : ℕ} (A E P C : OccSpace m → ℝ)
    (p : FourWords (Fin m)) (z : OccSpace m) : ℝ :=
  occWord p.ambient A z * occWord p.eta E z *
    occWord p.profile P z * occWord p.plateau C z

/-- The missing arbitrary-word four-factor Leibniz equality. It is derived
from the ordinary derivative product rule and finite-sum differentiation. -/
theorem occWord_four {m : ℕ} (A E P C : OccSpace m → ℝ)
    (hA : ContDiff ℝ ∞ A) (hE : ContDiff ℝ ∞ E)
    (hP : ContDiff ℝ ∞ P) (hC : ContDiff ℝ ∞ C) :
    ∀ w : List (Fin m), ∀ z : OccSpace m,
      occWord w (fun z => A z * E z * P z * C z) z =
        sumTerms (fourAlloc w) (fourTerm A E P C) z := by
  intro w
  induction w with
  | nil => intro z; simp [occWord, fourAlloc, sumTerms, fourTerm]
  | cons a w ih =>
      intro z
      have hfun : occWord w (fun z => A z * E z * P z * C z) =
          sumTerms (fourAlloc w) (fourTerm A E P C) := funext ih
      have hterms : ∀ p ∈ fourAlloc w, ContDiff ℝ ∞ (fourTerm A E P C p) := by
        intro p hp
        exact (((occWord_smooth p.ambient A hA).mul
          (occWord_smooth p.eta E hE)).mul
          (occWord_smooth p.profile P hP)).mul
          (occWord_smooth p.plateau C hC)
      change occOne a (occWord w (fun z => A z * E z * P z * C z)) z = _
      rw [hfun, occOne_sumTerms a (fourAlloc w) (fourTerm A E P C) z hterms]
      calc
        sumTerms (fourAlloc w) (fun p => occOne a (fourTerm A E P C p)) z =
          sumTerms (fourAlloc w) (fun p v =>
            fourTerm A E P C ⟨a :: p.ambient, p.eta, p.profile, p.plateau⟩ v +
            fourTerm A E P C ⟨p.ambient, a :: p.eta, p.profile, p.plateau⟩ v +
            fourTerm A E P C ⟨p.ambient, p.eta, a :: p.profile, p.plateau⟩ v +
            fourTerm A E P C ⟨p.ambient, p.eta, p.profile, a :: p.plateau⟩ v) z := by
              apply sumTerms_congr
              intro p hp
              exact occOne_four a (occWord p.ambient A) (occWord p.eta E)
                (occWord p.profile P) (occWord p.plateau C) z
                (coordinate_differentiable _ (occWord_smooth p.ambient A hA) z a)
                (coordinate_differentiable _ (occWord_smooth p.eta E hE) z a)
                (coordinate_differentiable _ (occWord_smooth p.profile P hP) z a)
                (coordinate_differentiable _ (occWord_smooth p.plateau C hC) z a)
        _ = sumTerms (fourAlloc (a :: w)) (fourTerm A E P C) z := by
          simp only [sumTerms_add, fourAlloc, sumTerms_append, sumTerms_map]

/-- A finite sum is bounded with multiplicity, without assuming distinct
allocation tuples (which would be false for repeated letters). -/
theorem abs_sumTerms_le {ι : Type*} {m : ℕ} (L : List ι)
    (F : ι → OccSpace m → ℝ) (z : OccSpace m) (B : ℝ)
    (hF : ∀ i ∈ L, |F i z| ≤ B) :
    |sumTerms L F z| ≤ (L.length : ℝ) * B := by
  revert hF
  induction L with
  | nil => intro h; simp [sumTerms]
  | cons i L ih =>
      intro h
      calc
        |sumTerms (i :: L) F z| ≤ |F i z| + |sumTerms L F z| := abs_add _ _
        _ ≤ B + (L.length : ℝ) * B :=
          add_le_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))
        _ = ((i :: L).length : ℝ) * B := by simp; ring

/-- Pointwise finite-order chart estimate with the sharp allocation constant.
The assumptions are bounds for the FOUR SEPARATE factors, not for their
product or for a prime-product discrepancy. -/
theorem occWord_four_bound {m : ℕ} (A E P C : OccSpace m → ℝ)
    (hA : ContDiff ℝ ∞ A) (hE : ContDiff ℝ ∞ E)
    (hP : ContDiff ℝ ∞ P) (hC : ContDiff ℝ ∞ C)
    (w : List (Fin m)) (z : OccSpace m) (BA BE BP BC : ℝ)
    (hBA : 0 ≤ BA) (hBE : 0 ≤ BE) (hBP : 0 ≤ BP) (hBC : 0 ≤ BC)
    (bA : ∀ v : List (Fin m), v.length ≤ w.length → |occWord v A z| ≤ BA)
    (bE : ∀ v : List (Fin m), v.length ≤ w.length → |occWord v E z| ≤ BE)
    (bP : ∀ v : List (Fin m), v.length ≤ w.length → |occWord v P z| ≤ BP)
    (bC : ∀ v : List (Fin m), v.length ≤ w.length → |occWord v C z| ≤ BC) :
    |occWord w (fun z => A z * E z * P z * C z) z| ≤
      (4 : ℝ) ^ w.length * (BA * BE * BP * BC) := by
  rw [occWord_four A E P C hA hE hP hC]
  have hterm : ∀ p ∈ fourAlloc w, |fourTerm A E P C p z| ≤ BA * BE * BP * BC := by
    intro p hp
    have hlen := fourAlloc_letters w p hp
    have ha := bA p.ambient (by omega)
    have he := bE p.eta (by omega)
    have hpr := bP p.profile (by omega)
    have hc := bC p.plateau (by omega)
    simp only [fourTerm, abs_mul]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul ha he (abs_nonneg _) hBA)
        hpr (abs_nonneg _) (mul_nonneg hBA hBE))
      hc (abs_nonneg _) (mul_nonneg (mul_nonneg hBA hBE) hBP)
  simpa only [fourAlloc_length, Nat.cast_pow, Nat.cast_ofNat] using
    abs_sumTerms_le (fourAlloc w) (fourTerm A E P C) z (BA * BE * BP * BC) hterm

/-- The actual grouped-product map is smooth in all occurrence coordinates. -/
theorem groupProduct_smooth {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (i : Fin k) :
    ContDiff ℝ ∞ (groupProduct owner U i) := by
  unfold groupProduct groupLog
  fun_prop

theorem family_grouped_smooth {kStar m : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun z => A.ambient T k (fun i => groupProduct owner U i z)) := by
  apply (A.smooth T k).comp
  apply contDiff_pi.mpr
  intro i
  exact groupProduct_smooth owner U i

/-- One pair of original Family constants C,B works for every rank,
occurrence chart and repeated-label word. The still-open cutoff obligation
is explicitly SEPARATE: prove BE/BP/BC for the concrete eta, psi and plateau
factors. The product's own derivative estimate is not a hypothesis. -/
theorem family_four_chart_bound {kStar : ℕ} (A : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ)
        (w : List (Fin m)) (z : OccSpace m)
        (E P Cut : OccSpace m → ℝ) (BE BP BC : ℝ),
        m ≤ 6 * kStar → w.length ≤ 12 * kStar →
        ContDiff ℝ ∞ E → ContDiff ℝ ∞ P → ContDiff ℝ ∞ Cut →
        0 ≤ BE → 0 ≤ BP → 0 ≤ BC →
        (∀ v : List (Fin m), v.length ≤ 12 * kStar → |occWord v E z| ≤ BE) →
        (∀ v : List (Fin m), v.length ≤ 12 * kStar → |occWord v P z| ≤ BP) →
        (∀ v : List (Fin m), v.length ≤ 12 * kStar → |occWord v Cut z| ≤ BC) →
        |occWord w (fun z =>
          A.ambient T k (fun i => groupProduct owner U i z) * E z * P z * Cut z) z| ≤
          (4 : ℝ) ^ w.length *
            (((C : ℝ) * Real.log ((T : ℝ) + 2) ^ B) * BE * BP * BC) := by
  obtain ⟨C, B, hC, hbound⟩ := family_all_word_ambient_bound A
  refine ⟨C, B, hC, ?_⟩
  intro T k m owner U w z E P Cut BE BP BC hm hw hE hP hCut hBE hBP hBC bE bP bCut
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) := by
    apply Real.log_nonneg
    have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  apply occWord_four_bound
    (fun z => A.ambient T k (fun i => groupProduct owner U i z)) E P Cut
    (family_grouped_smooth A T k owner U) hE hP hCut w z
    ((C : ℝ) * Real.log ((T : ℝ) + 2) ^ B) BE BP BC
    (mul_nonneg (Nat.cast_nonneg C) (pow_nonneg hlog B)) hBE hBP hBC
  · intro v hv
    exact hbound T k m owner U v z hm (hv.trans hw)
  · intro v hv
    exact bE v (hv.trans hw)
  · intro v hv
    exact bP v (hv.trans hw)
  · intro v hv
    exact bCut v (hv.trans hw)

end
end ImbalancedChen.P5Z.OccurrenceWordFourFactorLeibniz
