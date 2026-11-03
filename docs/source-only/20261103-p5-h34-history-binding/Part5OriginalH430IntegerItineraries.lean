import ImbalancedChen.P2EnhancedLowerFinitePhysicalGraph
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Integer words are computed from the SAME physical Program. New pair slots
are appended larger/smaller. No factorization of the final product is used.
All local domains, cell labels and incoming polarities remain the production
Member predicate. This file supplies an exact coordinate dictionary, not
an assertion that every Member is an occurrence in the original count.
-/
namespace ImbalancedChen.Part5OriginalH430IntegerItineraries

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry

abbrev IntegerPoint := Fin 2 → ℕ
abbrev IntegerCoordinates (depth : ℕ) := Fin depth → IntegerPoint

def physicalCoordinates (N : ℕ) {depth : ℕ}
    (q : IntegerCoordinates depth) : Coordinates depth :=
  fun j i => physicalPrime N (q j i)

def appendedWord : StepShape → IntegerPoint → List ℕ
  | .buchstabUpper, q => [q 0]
  | .buchstabLower, q => [q 0]
  | .w1Singleton _ _, q => [q 0]
  | .w2Singleton _ _, q => [q 0]
  | .w2Pair _ _, q => [q 1, q 0]
  | _, _ => []

def integerWord {mesh : ℕ} : (depth : ℕ) → List ℕ →
    Program mesh depth → IntegerCoordinates depth → List ℕ
  | 0, old, _, _ => old
  | d+1, old, code, q => integerWord d
      (old ++ appendedWord (code 0).1 (q 0)) (tail code) (tail q)

/-- Only active coordinates are tested. Fixed/retain/comparison shapes
append no prime. Repetition against the old prefix is not deleted here. -/
def PrimeLetters (N : ℕ) {mesh depth : ℕ} (code : Program mesh depth)
    (q : IntegerCoordinates depth) : Prop :=
  ∀ j, ∀ p ∈ appendedWord (code j).1 (q j), p.Prime ∧ p.Coprime N

theorem primeLetters_tail {N mesh depth : ℕ} {code : Program mesh (depth+1)}
    {q : IntegerCoordinates (depth+1)} (h : PrimeLetters N code q) :
    PrimeLetters N (tail code) (tail q) := fun j p hp => h j.succ p hp

theorem integerWord_letters {N mesh depth : ℕ} (old : List ℕ)
    (code : Program mesh depth) (q : IntegerCoordinates depth)
    (hold : ∀ p ∈ old, p.Prime ∧ p.Coprime N) (hq : PrimeLetters N code q) :
    ∀ p ∈ integerWord depth old code q, p.Prime ∧ p.Coprime N := by
  induction depth generalizing old with
  | zero => exact hold
  | succ d ih =>
      apply ih (old ++ appendedWord (code 0).1 (q 0)) (tail code) (tail q)
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hold p hp
        · exact hq 0 p hp
      · exact primeLetters_tail hq

theorem integerWord_prefix {mesh depth : ℕ} (old : List ℕ)
    (code : Program mesh depth) (q : IntegerCoordinates depth) :
    ∃ suffix, integerWord depth old code q = old ++ suffix := by
  induction depth generalizing old with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ d ih =>
      obtain ⟨xs, hx⟩ := ih (old ++ appendedWord (code 0).1 (q 0)) (tail code) (tail q)
      exact ⟨appendedWord (code 0).1 (q 0) ++ xs, by
        simpa only [integerWord, List.append_assoc] using hx⟩

theorem perform_word (N : ℕ) (p : PhysicalNode) (shape : StepShape)
    (q : IntegerPoint) :
    word (perform p shape (fun i => physicalPrime N (q i))) =
      word p ++ (appendedWord shape q).map (physicalPrime N) := by
  cases shape <;>
    simp [perform, appendedWord, word_appendOne, word_appendPair, compareAt]

/-- This is a theorem about the production realization, not a second
physical evaluator. Every earlier prefix uses its own actual state. -/
theorem realize_word {N mesh depth : ℕ} (n : TypedNode) (old : List ℕ)
    (code : Program mesh depth) (q : IntegerCoordinates depth)
    (hword : word n.physical = old.map (physicalPrime N)) :
    word (realize depth n code (physicalCoordinates N q)).physical =
      (integerWord depth old code q).map (physicalPrime N) := by
  induction depth generalizing n old with
  | zero => exact hword
  | succ d ih =>
      apply ih (advance n (code 0).1 (physicalCoordinates N q 0))
        (old ++ appendedWord (code 0).1 (q 0)) (tail code) (tail q)
      change word (perform n.physical (code 0).1
        (fun i => physicalPrime N (q 0 i))) = _
      rw [perform_word, hword, List.map_append]

theorem prod_pos {old : List ℕ} (h : ∀ p ∈ old, 0 < p) : 0 < old.prod := by
  induction old with
  | nil => simp
  | cons p ps ih =>
      exact Nat.mul_pos (h p (by simp)) (ih (fun r hr => h r (by simp [hr])))

/-- The exponent sum comes from the entire integer word; no squarefree
assumption and no loss of repeated factors is made. -/
theorem sum_physicalPrime (N : ℕ) {old : List ℕ}
    (h : ∀ p ∈ old, 0 < p) :
    (old.map (physicalPrime N)).sum = Real.log (old.prod : ℝ) / Real.log (N : ℝ) := by
  induction old with
  | nil => simp
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht : ∀ r ∈ ps, 0 < r := fun r hr => h r (by simp [hr])
      have hprod := prod_pos ht
      rw [List.map_cons, List.sum_cons, ih ht, List.prod_cons, Nat.cast_mul,
        Real.log_mul (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr hprod).ne', add_div]
      rfl

theorem residual_eq_physicalLevel {N : ℕ} (hN : 1 < N)
    {p : PhysicalNode} {lambda : ℝ} {old : List ℕ}
    (htotal : p.total = lambda)
    (hword : word p = old.map (physicalPrime N))
    (hold : ∀ q ∈ old, 0 < q) :
    residual p = physicalLevel N ((N : ℝ)^lambda) old := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNR
  have hp : (0 : ℝ) < old.prod := Nat.cast_pos.mpr (prod_pos hold)
  have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNR).ne'
  calc
    residual p = lambda - Real.log (old.prod : ℝ)/Real.log (N : ℝ) := by
      rw [residual, htotal, hword, sum_physicalPrime N hold]
    _ = physicalLevel N ((N : ℝ)^lambda) old := by
      unfold physicalLevel residualLevel parentProduct
      rw [Real.log_div (Real.rpow_pos_of_pos hN0 lambda).ne' hp.ne', Real.log_rpow hN0]
      field_simp [hl]
      <;> ring

/-- Parent support is derived from the exact log identity and positive
residual, rather than installed as a history-record field. -/
theorem parentWindow_of_realization {N : ℕ} (hN : 1 < N)
    {p : PhysicalNode} {lambda : ℝ} {old : List ℕ}
    (htotal : p.total = lambda) (hlambda : lambda ≤ 1)
    (hword : word p = old.map (physicalPrime N))
    (hold : ∀ q ∈ old, 0 < q) (hres : 0 < residual p) (hceil : 0 < p.ceiling) :
    parentWindow N ((N : ℝ)^lambda) old p.ceiling := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNR
  have hprod := prod_pos hold
  have hp : (0 : ℝ) < parentProduct old := Nat.cast_pos.mpr hprod
  have hQ : 0 < (N : ℝ)^lambda := Real.rpow_pos_of_pos hN0 lambda
  have hL := residual_eq_physicalLevel hN htotal hword hold
  have hlog : 0 < Real.log (((N : ℝ)^lambda)/(parentProduct old : ℝ)) := by
    have hpos : 0 < physicalLevel N ((N : ℝ)^lambda) old := hL ▸ hres
    have hm := mul_pos hpos (Real.log_pos hNR)
    dsimp [physicalLevel, residualLevel] at hm
    rwa [div_mul_cancel₀ _ (Real.log_pos hNR).ne'] at hm
  have hR : 1 < ((N : ℝ)^lambda)/(parentProduct old : ℝ) := by
    have he := Real.exp_lt_exp.mpr hlog
    simpa only [Real.exp_zero, Real.exp_log (div_pos hQ hp)] using he
  refine ⟨hN, hprod, ?_, ?_, hceil⟩
  · have ht := (lt_div_iff₀ hp).mp hR
    simpa only [one_mul] using ht
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNR.le hlambda

/-- Alpha propagation needs local domains but not the stronger physical
full-square assumption, which would wrongly exclude the classical root. -/
theorem realize_alpha_mono {lo hi : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (ha : 2 ≤ alpha n.physical) (hz : Member lo hi depth n code z) :
    alpha n.physical ≤ alpha (realize depth n code z).physical := by
  induction depth generalizing n with
  | zero => exact le_rfl
  | succ d ih =>
      have hs := perform_alpha hz.2.2.1 ha
      exact hs.trans (ih (ha.trans hs) hz.2.2.2)

theorem perform_ceiling_pos {p : PhysicalNode} {shape : StepShape} {z : Point}
    (hc : 0 < p.ceiling) (hz : LocalDomain p shape z) :
    0 < (perform p shape z).ceiling := by
  cases shape with
  | retain => exact hc
  | transport _ => exact hc
  | buchstabUpper => exact hz.2.1.1
  | buchstabLower => exact hz.2.2.1.1
  | w1Fixed _ _ => exact hc
  | w1Singleton _ _ => exact hz.2.1.1
  | w2Fixed _ _ => exact hc
  | w2Singleton _ _ => exact hz.2.1.1
  | w2Pair _ _ => exact hz.2.1.1

theorem realize_ceiling_pos {lo hi : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hc : 0 < n.physical.ceiling) (hz : Member lo hi depth n code z) :
    0 < (realize depth n code z).physical.ceiling := by
  induction depth generalizing n with
  | zero => exact hc
  | succ d ih => exact ih (perform_ceiling_pos hc hz.2.2.1) hz.2.2.2

/-- Fin(N+1) will not truncate an active natural prime of a Member. -/
theorem prime_le_target {N r : ℕ} (hN : 1 < N) (hr : 0 < r)
    (hcoord : physicalPrime N r ≤ 1) : r ≤ N := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (r:ℝ) ≤ Real.log (N:ℝ) := by
    have hh := (div_le_iff₀ (Real.log_pos hNR)).mp hcoord
    simpa only [one_mul] using hh
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (Nat.cast_pos.mpr hr), Real.exp_log (zero_lt_one.trans hNR)] at he
  exact_mod_cast he

theorem active_coordinate_le_one {N r : ℕ} {p : PhysicalNode}
    {shape : StepShape} {q : IntegerPoint}
    (htotal : p.total ≤ 1) (hsum : 0 ≤ (word p).sum)
    (hd : LocalDomain p shape (fun i => physicalPrime N (q i)))
    (hr : r ∈ appendedWord shape q) : physicalPrime N r ≤ 1 := by
  have hres : residual p ≤ 1 := by dsimp [residual]; linarith
  cases shape with
  | retain => simp [appendedWord] at hr
  | transport _ => simp [appendedWord] at hr
  | w1Fixed _ _ => simp [appendedWord] at hr
  | w2Fixed _ _ => simp [appendedWord] at hr
  | buchstabUpper =>
      have he : r = q 0 := by simpa [appendedWord] using hr
      subst r
      linarith [hd.2.1.2.2]
  | buchstabLower =>
      have he : r = q 0 := by simpa [appendedWord] using hr
      subst r
      linarith [hd.2.2.1.2.2]
  | w1Singleton _ _ =>
      have he : r = q 0 := by simpa [appendedWord] using hr
      subst r
      linarith [hd.2.1.2.2]
  | w2Singleton _ _ =>
      have he : r = q 0 := by simpa [appendedWord] using hr
      subst r
      linarith [hd.2.1.2.2]
  | w2Pair _ _ =>
      have he : r = q 1 ∨ r = q 0 := by simpa [appendedWord] using hr
      rcases he with rfl | rfl
      · linarith [hd.2.1.2.2.2.1]
      · linarith [hd.2.1.2.1, hd.2.1.2.2.2.1]

theorem path_active_cap {N mesh depth : ℕ} {lo hi : ℝ}
    {n : TypedNode} {old : List ℕ} {code : Program mesh depth}
    {q : IntegerCoordinates depth} (hN : 1 < N) (htotal : n.physical.total ≤ 1)
    (hword : word n.physical = old.map (physicalPrime N))
    (hold : ∀ r ∈ old, 0 < r) (hq : PrimeLetters N code q)
    (hz : Member lo hi depth n code (physicalCoordinates N q)) :
    ∀ j, ∀ r ∈ appendedWord (code j).1 (q j), r ≤ N := by
  induction depth generalizing n old with
  | zero => intro j; exact Fin.elim0 j
  | succ d ih =>
      have hs : 0 ≤ (word n.physical).sum := by
        rw [hword, sum_physicalPrime N hold]
        apply div_nonneg
        · apply Real.log_nonneg
          exact_mod_cast (show 1 ≤ old.prod from prod_pos hold)
        · exact (Real.log_pos (by exact_mod_cast hN)).le
      have hfirst : ∀ r ∈ appendedWord (code 0).1 (q 0), r ≤ N := by
        intro r hr
        apply prime_le_target hN (hq 0 r hr).1.pos
        exact active_coordinate_le_one htotal hs hz.2.2.1 hr
      have hold' : ∀ r ∈ old ++ appendedWord (code 0).1 (q 0), 0 < r := by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hold r hr
        · exact (hq 0 r hr).1.pos
      have hw' : word (advance n (code 0).1 (physicalCoordinates N q 0)).physical =
          (old ++ appendedWord (code 0).1 (q 0)).map (physicalPrime N) := by
        change word (perform n.physical (code 0).1
          (fun i => physicalPrime N (q 0 i))) = _
        rw [perform_word, hword, List.map_append]
      have ht' : (advance n (code 0).1 (physicalCoordinates N q 0)).physical.total ≤ 1 := by
        simpa only [advance, perform_total] using htotal
      have htail := ih ht' hw' hold' (primeLetters_tail hq) hz.2.2.2
      intro j
      exact Fin.cases hfirst (fun i => htail i) j

end
end ImbalancedChen.Part5OriginalH430IntegerItineraries
