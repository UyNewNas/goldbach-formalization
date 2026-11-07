import ImbalancedChen.P1OriginalVariableFourthContinuation
import ImbalancedChen.VariableEnvelopeRegularity
import ImbalancedChen.P1HistoricalFifthJointIntegralSign
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A bounded analytic supplier for the literal variable fifth cap. The old raw
fourth envelope retains all fifteen nonempty subset tents and the inherited
affine W = B(t3). Every selected fifth row uses M_I(t)-2e, and every overlap
participates in the maximum. No midpoint, generic-D old5, prime mean, or
desired asymptotic limit is substituted.

The substantive conclusions are a common coordinate modulus for the moving
old/new maximum and integrability of its genuine own-cube LOWER difference
on every closed positive cube. The strict own-cube gates cancel continuously
at residual parameter two, by the actual canonical lower-factor supplier.

OPEN: identify a concrete original firstStop/raw-Q3 producer's fourth
ancestor with this raw envelope on its licensed cells, install the selected
row table, and prove the arithmetic-to-integral passage and small-coordinate
tail. These are not hypotheses of an asserted discrete limit here. This
module does not modify any policy, retained divisor, or empty-history term.
-/

namespace ImbalancedChen.P1LiteralVariableFifthCompactSupplier

noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope P1OriginalVariableFourthContinuation

abbrev Point := Fin 5 → ℝ

def oldMasks : Finset (Finset (Fin 4)) := Finset.univ.erase ∅

theorem oldMasks_card : oldMasks.card = 15 := by decide

def oldSubsetSum (I : Finset (Fin 4)) (t : Point) : ℝ :=
  ∑ i ∈ I, t i.castSucc

/-- This is the fifteen-tent raw fourth envelope, with its inherited W.
Its identity with an actual licensed policy is deliberately not asserted. -/
def rawFourth (t : Point) : ℝ :=
  finiteMax oldMasks (fun _ => True) (fun I => v (oldSubsetSum I t)) (B (t 2))

def old5 (e : ℝ) (t : Point) : ℝ := rawFourth t - 2 * e

def M (I : Finset (Fin 5)) (t : Point) : ℝ :=
  min ((1 + ∑ i ∈ I, t i) / 2)
    (57 / 64 - (3 / 2 : ℝ) * ∑ i ∈ I, t i)

theorem M_eq_v (I : Finset (Fin 5)) (t : Point) :
    M I t = v (∑ i ∈ I, t i) := by
  rw [M, v_eq_min]
  rfl

/-- Fixed eligible rows on one causal cell. The inherited old profile also
moves with t. All selected masks, including overlapping masks, are kept. -/
def next5 (e : ℝ) (rows : Finset (Finset (Fin 5))) (t : Point) : ℝ :=
  finiteMax rows (fun _ => True) (fun I => M I t - 2 * e) (old5 e t)

theorem old5_le_next5 (e : ℝ) (rows : Finset (Finset (Fin 5))) (t : Point) :
    old5 e t ≤ next5 e rows t :=
  finiteMax_seed_le rows _ _ _

theorem selected_row_le_next5 (e : ℝ) (rows : Finset (Finset (Fin 5)))
    (t : Point) (I : Finset (Fin 5)) (hI : I ∈ rows) :
    M I t - 2 * e ≤ next5 e rows t :=
  finiteMax_row_le rows _ _ _ I hI trivial

/-- Unlike a constant-seed maximum bound, this pays the old-profile motion.
It will also apply when a licensed raw-Q3/fourth seed has been identified. -/
theorem finiteMax_moving_abs_sub_le {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (f g : ι → ℝ) (a b d : ℝ)
    (hseed : |a - b| ≤ d) (hrows : ∀ r ∈ rows, eligible r → |f r - g r| ≤ d) :
    |finiteMax rows eligible f a - finiteMax rows eligible g b| ≤ d := by
  have hfg : finiteMax rows eligible f a ≤ finiteMax rows eligible g b + d := by
    apply finiteMax_le
    · have h := finiteMax_seed_le rows eligible g b
      have hs := (abs_le.mp hseed).2
      linarith
    · intro r hr he
      have h := finiteMax_row_le rows eligible g b r hr he
      have hs := (abs_le.mp (hrows r hr he)).2
      linarith
  have hgf : finiteMax rows eligible g b ≤ finiteMax rows eligible f a + d := by
    apply finiteMax_le
    · have h := finiteMax_seed_le rows eligible f a
      have hs := (abs_le.mp hseed).1
      linarith
    · intro r hr he
      have h := finiteMax_row_le rows eligible f a r hr he
      have hs := (abs_le.mp (hrows r hr he)).1
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem sum_coordinate_error {n : ℕ} (I : Finset (Fin n))
    (t u : Fin n → ℝ) (d : ℝ) (h : ∀ i, |t i - u i| ≤ d) :
    |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| ≤ (I.card : ℝ) * d := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ I, (t i - u i)| ≤ ∑ i ∈ I, |t i - u i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, d := Finset.sum_le_sum (fun i _ => h i)
    _ = (I.card : ℝ) * d := by simp [nsmul_eq_mul]

theorem rawFourth_abs_sub_le (t u : Point) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ i, |t i - u i| ≤ d) :
    |rawFourth t - rawFourth u| ≤ 6 * d := by
  apply finiteMax_moving_abs_sub_le
  · have hs := abs_le.mp (h 2)
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith
  · intro I _ _
    have hs := sum_coordinate_error I (fun i => t i.castSucc)
      (fun i => u i.castSucc) d (fun i => h i.castSucc)
    have hc : (I.card : ℝ) ≤ 4 := by
      exact_mod_cast (Finset.card_le_univ I)
    have hsum : |oldSubsetSum I t - oldSubsetSum I u| ≤ 4 * d :=
      hs.trans (mul_le_mul_of_nonneg_right hc hd)
    have hv := v_abs_sub_le_of_le hsum
    nlinarith

/-- A fifth mask can select five coordinates, so the common constant is
15/2; inheriting the fourth profile does not increase that constant. -/
theorem next5_abs_sub_le (e : ℝ) (rows : Finset (Finset (Fin 5)))
    (t u : Point) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ i, |t i - u i| ≤ d) :
    |next5 e rows t - next5 e rows u| ≤ (15 / 2 : ℝ) * d := by
  apply finiteMax_moving_abs_sub_le
  · have hr := rawFourth_abs_sub_le t u d hd h
    have heq : old5 e t - old5 e u = rawFourth t - rawFourth u := by
      unfold old5
      ring
    rw [heq]
    nlinarith
  · intro I _ _
    have hs := sum_coordinate_error I t u d h
    have hc : (I.card : ℝ) ≤ 5 := by
      exact_mod_cast (Finset.card_le_univ I)
    have hv := v_abs_sub_le_of_le (hs.trans (mul_le_mul_of_nonneg_right hc hd))
    have heq : (M I t - 2 * e) - (M I u - 2 * e) =
        v (∑ i ∈ I, t i) - v (∑ i ∈ I, u i) := by
      rw [M_eq_v, M_eq_v]
      ring
    rw [heq]
    nlinarith

private theorem finiteMax_insert_all {ι : Type*} (rows : Finset ι)
    (f : ι → ℝ) (a : ℝ) (r : ι) :
    finiteMax (insert r rows) (fun _ => True) f a =
      max (f r) (finiteMax rows (fun _ => True) f a) := by
  simp [finiteMax, finiteValues, Finset.image_insert, Finset.insert_comm,
    Finset.max'_insert]

private theorem continuous_finiteMax_moving {ι : Type*} (rows : Finset ι)
    (f : ι → Point → ℝ) (a : Point → ℝ) (ha : Continuous a) :
    (∀ r ∈ rows, Continuous (f r)) →
      Continuous (fun t => finiteMax rows (fun _ => True) (fun r => f r t) (a t)) := by
  induction rows using Finset.induction_on with
  | empty =>
      intro _
      simpa [finiteMax, finiteValues] using ha
  | @insert r rows hr ih =>
      intro hf
      have hcont := (hf r (Finset.mem_insert_self _ _)).sup
        (ih (fun s hs => hf s (Finset.mem_insert_of_mem hs)))
      simpa only [finiteMax_insert_all] using hcont

theorem continuous_rawFourth : Continuous rawFourth := by
  apply continuous_finiteMax_moving
  · unfold B
    fun_prop
  · intro I _
    apply continuous_v.comp
    unfold oldSubsetSum
    fun_prop

theorem continuous_old5 (e : ℝ) : Continuous (old5 e) :=
  continuous_rawFourth.sub continuous_const

theorem continuous_next5 (e : ℝ) (rows : Finset (Finset (Fin 5))) :
    Continuous (next5 e rows) := by
  apply continuous_finiteMax_moving rows _ _ (continuous_old5 e)
  intro I _
  have hsum : Continuous (fun t : Point => ∑ i ∈ I, t i) := by fun_prop
  simpa only [M_eq_v] using (continuous_v.comp hsum).sub continuous_const

def positiveCube (a b : ℝ) : Set Point := univ.pi (fun _ => Icc a b)

/-- Both strict own-cube gates are evaluated at their own moving levels. -/
def kernel (e : ℝ) (rows : Finset (Finset (Fin 5))) (t : Point) : ℝ :=
  (primeOwnCubeGatedProfile (next5 e rows t) t -
    primeOwnCubeGatedProfile (old5 e t) t) * ∏ i, 1 / t i

theorem kernel_nonneg (e : ℝ) (rows : Finset (Finset (Fin 5)))
    (t : Point) (ht : ∀ i, 0 < t i) : 0 ≤ kernel e rows t := by
  apply mul_nonneg
  · exact sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t (ht (Fin.last 4))
      (old5_le_next5 e rows t))
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)

/-- A stored selected cap can be used conservatively only with the SAME
old raw-fourth profile. This permits a genuine pointwise row comparison
without identifying a generic D.old5 or assuming a final saving bound. -/
theorem selected_stored_kernel_le (e c : ℝ)
    (rows : Finset (Finset (Fin 5))) (I : Finset (Fin 5)) (hI : I ∈ rows)
    (t : Point) (ht : ∀ i, 0 < t i) (hcap : c ≤ M I t - 2 * e) :
    (primeOwnCubeGatedProfile c t - primeOwnCubeGatedProfile (old5 e t) t) *
        (∏ i, 1 / t i) ≤ kernel e rows t := by
  apply mul_le_mul_of_nonneg_right
  · exact sub_le_sub_right (p1PrimeOwnCubeGatedProfile_mono t (ht (Fin.last 4))
      (hcap.trans (selected_row_le_next5 e rows t I hI))) _
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)

/-- The canonical zero-extended lower factor removes the apparent
discontinuity at each moving own-cube surface, including their intersection. -/
theorem continuousOn_movingOwnCubeProfile (a b : ℝ) (ha : 0 < a)
    (level : Point → ℝ) (hlevel : Continuous level) :
    ContinuousOn (fun t => primeOwnCubeGatedProfile (level t) t) (positiveCube a b) := by
  have ht : ∀ t ∈ positiveCube a b, 0 < t (Fin.last 4) :=
    fun t ht => ha.trans_le (ht _ (mem_univ _)).1
  have hlast : ContinuousOn (fun t : Point => t (Fin.last 4)) (positiveCube a b) :=
    (continuous_apply _).continuousOn
  have hsum : Continuous (fun t : Point => ∑ i, t i) := by fun_prop
  have harg : ContinuousOn (fun t => (level t - ∑ i, t i) / t (Fin.last 4))
      (positiveCube a b) :=
    (hlevel.continuousOn.sub hsum.continuousOn).div hlast (fun t ht' => (ht t ht').ne')
  have hfactor := continuous_actualExtendedThirdLowerFactor.comp_continuousOn harg
  have hc : ContinuousOn (fun t => 4 * actualExtendedThirdLowerFactor
      ((level t - ∑ i, t i) / t (Fin.last 4)) / t (Fin.last 4))
      (positiveCube a b) :=
    (continuousOn_const.mul hfactor).div hlast (fun t ht' => (ht t ht').ne')
  apply hc.congr
  intro t ht'
  rw [p1PrimeOwnCubeGatedProfile_eq_profile _ t (ht t ht'),
    p1PrimeTupleMinusProfile_eq_lowerFactor _ t (ht t ht')]

theorem continuousOn_kernel (e a b : ℝ) (ha : 0 < a)
    (rows : Finset (Finset (Fin 5))) :
    ContinuousOn (kernel e rows) (positiveCube a b) := by
  have hprod : ContinuousOn (fun t : Point => ∏ i, 1 / t i) (positiveCube a b) := by
    apply continuousOn_finsetProd Finset.univ
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun t ht => (ha.trans_le (ht i (mem_univ _)).1).ne')
  exact ((continuousOn_movingOwnCubeProfile a b ha _ (continuous_next5 e rows)).sub
    (continuousOn_movingOwnCubeProfile a b ha _ (continuous_old5 e))).mul hprod

/-- A genuine compact integral supplier, requiring no assumed mean or
desired saving. Its noncompact tail and arithmetic limit remain OPEN. -/
theorem integrableOn_kernel (e a b : ℝ) (ha : 0 < a)
    (rows : Finset (Finset (Fin 5))) :
    IntegrableOn (kernel e rows) (positiveCube a b) :=
  (continuousOn_kernel e a b ha rows).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))

end
end ImbalancedChen.P1LiteralVariableFifthCompactSupplier
