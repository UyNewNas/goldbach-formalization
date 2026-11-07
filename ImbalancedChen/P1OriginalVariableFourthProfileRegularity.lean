import ImbalancedChen.P1OriginalVariableFourthContinuation
import ImbalancedChen.VariableEnvelopeRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Regularity of the literal variable fourth candidate and of a profile with a
fixed eligible row set on a cell. The pointwise producer profile may change its
eligible set across box walls; this module asserts continuity only where the
same eligible rows are present throughout the specified cell. No row licence,
improvement gap, distribution bound, or target assumption is supplied here.
-/

namespace ImbalancedChen.P1OriginalVariableFourthProfileRegularity

noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface

/-- The exact scalar `3/2` bound applies to the sum selected by a row. -/
theorem candidateExponent_abs_sub_le (loss : ℝ) (I : Finset (Fin 4))
    (t u : Point) :
    |candidateExponent loss I t - candidateExponent loss I u| ≤
      (3 / 2 : ℝ) * |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| := by
  calc
    |candidateExponent loss I t - candidateExponent loss I u| =
        |v (∑ i ∈ I, t i) - v (∑ i ∈ I, u i)| := by
          congr 1
          simp only [candidateExponent]
          ring
    _ ≤ (3 / 2 : ℝ) * |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| :=
      v_abs_sub_le _ _

/-- For a coordinatewise error `d`, a row with several selected labels has
constant `(3/2) * card I`. This avoids claiming `3/2` in sup norm. -/
theorem candidateExponent_abs_sub_le_of_coordinates (loss : ℝ)
    (I : Finset (Fin 4)) (t u : Point) (d : ℝ)
    (hcoord : ∀ i ∈ I, |t i - u i| ≤ d) :
    |candidateExponent loss I t - candidateExponent loss I u| ≤
      (3 / 2 : ℝ) * (I.card : ℝ) * d := by
  have hsum : |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| ≤ (I.card : ℝ) * d := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i ∈ I, (t i - u i)| ≤ ∑ i ∈ I, |t i - u i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I, d := Finset.sum_le_sum (fun i hi => hcoord i hi)
      _ = (I.card : ℝ) * d := by simp [nsmul_eq_mul]
  calc
    |candidateExponent loss I t - candidateExponent loss I u| ≤
        (3 / 2 : ℝ) * |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| :=
      candidateExponent_abs_sub_le loss I t u
    _ ≤ (3 / 2 : ℝ) * (I.card : ℝ) * d := by
      have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith

theorem continuous_candidateExponent (loss : ℝ) (I : Finset (Fin 4)) :
    Continuous (candidateExponent loss I) := by
  have hsum : Continuous (fun t : Point => ∑ i ∈ I, t i) := by
    apply continuous_finset_sum
    intro i _hi
    exact continuous_apply i
  simpa only [candidateExponent] using (continuous_v.comp hsum).sub continuous_const

/-- A finite maximum with its inherited seed. Its row set is fixed here. -/
def fixedMax {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (profile : ι → Point → ℝ) (t : Point) : ℝ :=
  (insert seed (rows.image (fun r => profile r t))).max'
    (by exact ⟨seed, Finset.mem_insert_self _ _⟩)

private theorem fixedMax_insert {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (profile : ι → Point → ℝ) (r : ι) (t : Point) :
    fixedMax seed (insert r rows) profile t =
      max (profile r t) (fixedMax seed rows profile t) := by
  classical
  simp [fixedMax, Finset.image_insert, Finset.insert_comm, Finset.max'_insert]

/-- Every finite maximum inherits the common absolute-difference bound of
its rows; the constant inherited seed has difference zero. -/
theorem fixedMax_abs_sub_le {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (profile : ι → Point → ℝ) (t u : Point) (d : ℝ) (hd : 0 ≤ d) :
    (∀ r ∈ rows, |profile r t - profile r u| ≤ d) →
      |fixedMax seed rows profile t - fixedMax seed rows profile u| ≤ d := by
  classical
  induction rows using Finset.induction_on with
  | empty =>
      intro _
      simpa [fixedMax] using hd
  | @insert r rows _hr ih =>
      intro hrow
      rw [fixedMax_insert, fixedMax_insert]
      apply (_root_.abs_max_sub_max_le_max _ _ _ _).trans
      apply max_le
      · exact hrow r (Finset.mem_insert_self _ _)
      · exact ih (fun s hs => hrow s (Finset.mem_insert_of_mem hs))

theorem continuous_fixedMax {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (profile : ι → Point → ℝ) :
    (∀ r ∈ rows, Continuous (profile r)) → Continuous (fixedMax seed rows profile) := by
  classical
  induction rows using Finset.induction_on with
  | empty =>
      intro _
      simpa [fixedMax] using (continuous_const : Continuous (fun _ : Point => seed))
  | @insert r rows _hr ih =>
      intro hrow
      have hr : Continuous (profile r) := hrow r (Finset.mem_insert_self _ _)
      have hs : Continuous (fixedMax seed rows profile) :=
        ih (fun s hs => hrow s (Finset.mem_insert_of_mem hs))
      have heq : fixedMax seed (insert r rows) profile =
          fun t => max (profile r t) (fixedMax seed rows profile t) := by
        funext t
        exact fixedMax_insert seed rows profile r t
      rw [heq]
      exact hr.sup hs

/-- On a cell where eligibility is constant, the literal `profile4` is the
fixed maximum of all eligible rows, including every overlap and the seed. -/
theorem profile4_eq_fixed_on_cell {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → Point → Prop) (profile : ι → Point → ℝ)
    (C : Set Point) (E : Finset ι)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ C, eligible r t ↔ r ∈ E)
    {t : Point} (ht : t ∈ C) :
    profile4 seed rows eligible profile t =
      fixedMax seed (rows.filter (fun r => r ∈ E)) profile t := by
  classical
  have hfilter : rows.filter (fun r => eligible r t) =
      rows.filter (fun r => r ∈ E) := by
    ext r
    by_cases hr : r ∈ rows
    · simpa only [Finset.mem_filter, hr, true_and] using hfixed r hr t ht
    · simp [Finset.mem_filter, hr]
  simp only [profile4, finiteMax, finiteValues, fixedMax, hfilter]

theorem continuousOn_profile4_fixed_cell {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → Point → Prop) (profile : ι → Point → ℝ)
    (C : Set Point) (E : Finset ι)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ C, eligible r t ↔ r ∈ E)
    (hrow : ∀ r ∈ rows, r ∈ E → Continuous (profile r)) :
    ContinuousOn (profile4 seed rows eligible profile) C := by
  have hc : Continuous (fixedMax seed (rows.filter (fun r => r ∈ E)) profile) :=
    continuous_fixedMax seed _ profile (fun r hr => by
      exact hrow r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2)
  exact hc.continuousOn.congr (fun t ht =>
    profile4_eq_fixed_on_cell seed rows eligible profile C E hfixed ht)

theorem continuous_bufferedCandidate (r : ProducerRow) (e : ℝ) :
    Continuous (r.bufferedCandidate e) := by
  have h : Continuous (candidateExponent (2 * e) r.selected) :=
    continuous_candidateExponent (2 * e) r.selected
  change Continuous (fun t : Point => r.bufferedCandidate e t)
  simpa only [ProducerRow.bufferedCandidate_eq, candidateExponent] using h

/-- The producer's own closed boxes decide eligibility on this cell; no
global wall-continuity of `producerProfile4` is inferred. -/
theorem continuousOn_producerProfile4_fixed_cell (e seed : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (C : Set Point) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ C,
      producerEligible licensed r t ↔ r ∈ E) :
    ContinuousOn (producerProfile4 e rows licensed seed) C := by
  exact continuousOn_profile4_fixed_cell seed rows (producerEligible licensed)
    (fun r => r.bufferedCandidate e) C E hfixed
      (fun r _hr _he => continuous_bufferedCandidate r e)

/-- The common `3/2` scalar modulus passes through the fixed eligible max.
The hypothesis measures each selected affine sum, rather than presuming a
smaller coordinatewise Lipschitz constant for rows with several labels. -/
theorem producerProfile4_abs_sub_le_on_fixed_cell (e seed : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (C : Set Point) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ C,
      producerEligible licensed r t ↔ r ∈ E)
    {t u : Point} (ht : t ∈ C) (hu : u ∈ C) (d : ℝ) (hd : 0 ≤ d)
    (hrows : ∀ r ∈ rows, r ∈ E →
      |(∑ i ∈ r.selected, t i) - ∑ i ∈ r.selected, u i| ≤ d) :
    |producerProfile4 e rows licensed seed t -
      producerProfile4 e rows licensed seed u| ≤ (3 / 2 : ℝ) * d := by
  change |profile4 seed rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) t -
    profile4 seed rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) u| ≤ (3 / 2 : ℝ) * d
  rw [profile4_eq_fixed_on_cell seed rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) C E hfixed ht,
    profile4_eq_fixed_on_cell seed rows (producerEligible licensed)
      (fun r => r.bufferedCandidate e) C E hfixed hu]
  apply fixedMax_abs_sub_le seed _ (fun r => r.bufferedCandidate e) t u
    ((3 / 2 : ℝ) * d) (mul_nonneg (by norm_num) hd)
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  have h := (candidateExponent_abs_sub_le (2 * e) r.selected t u).trans
    (mul_le_mul_of_nonneg_left (hrows r hr'.1 hr'.2) (by norm_num))
  simpa only [candidateExponent, ProducerRow.bufferedCandidate_eq] using h

def positiveCube (a b : ℝ) : Set Point :=
  univ.pi (fun _ : Fin 4 => Icc a b)

def reciprocalProduct (t : Point) : ℝ := ∏ i, 1 / t i

theorem continuousOn_reciprocalProduct (a b : ℝ) (ha : 0 < a) :
    ContinuousOn reciprocalProduct (positiveCube a b) := by
  unfold reciprocalProduct positiveCube
  apply continuousOn_finsetProd Finset.univ
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn
    (fun t ht => (ha.trans_le (ht i (mem_univ _)).1).ne')

theorem aestronglyMeasurable_producerProfile4_fixed_cube
    (e seed a b : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ positiveCube a b,
      producerEligible licensed r t ↔ r ∈ E) :
    AEStronglyMeasurable (producerProfile4 e rows licensed seed)
      (volume.restrict (positiveCube a b)) := by
  exact ((continuousOn_producerProfile4_fixed_cell e seed rows licensed
    (positiveCube a b) E hfixed).integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc))).aestronglyMeasurable

/-- Continuous fixed-row max times the literal reciprocal product is
integrable on any closed positive cube, with no target or supplier premise. -/
theorem integrableOn_producerProfile4_reciprocalProduct_fixed_cube
    (e seed a b : ℝ) (ha : 0 < a) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ positiveCube a b,
      producerEligible licensed r t ↔ r ∈ E) :
    IntegrableOn (fun t => producerProfile4 e rows licensed seed t *
      reciprocalProduct t) (positiveCube a b) := by
  have hc := continuousOn_producerProfile4_fixed_cell e seed rows licensed
    (positiveCube a b) E hfixed
  exact (hc.mul (continuousOn_reciprocalProduct a b ha)).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))

theorem aestronglyMeasurable_producerProfile4_reciprocalProduct_fixed_cube
    (e seed a b : ℝ) (ha : 0 < a) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ positiveCube a b,
      producerEligible licensed r t ↔ r ∈ E) :
    AEStronglyMeasurable (fun t => producerProfile4 e rows licensed seed t *
      reciprocalProduct t) (volume.restrict (positiveCube a b)) := by
  exact (integrableOn_producerProfile4_reciprocalProduct_fixed_cube
    e seed a b ha rows licensed E hfixed).aestronglyMeasurable

end
end ImbalancedChen.P1OriginalVariableFourthProfileRegularity
