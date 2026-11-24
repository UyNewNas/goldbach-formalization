import ImbalancedChen.P5OldFifthActualChildJensenIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing child argument is extended to a rectangle with its ORIGINAL
parent endpoints.  The firstF calculus, strict-own-cube pointwise Q bound,
one-dimensional affine moments and product-measure API are reused.  This
file proves the missing parent barycentric integration and normalized
Jensen steps; neither an integral lower bound nor Jensen is a hypothesis.
-/
namespace ImbalancedChen.P5OriginalParentBoxJensen
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier P1FifthUnitBoxLiteralGainLower
open P5OldFifthFrozenUpperSurrogate P5OldFifthFrozenGapConcavity
open P5OldFifthFiveCoordinateTree P5OldFifthFiveCoordinateBarycentric
open P5OldFifthChildGapIntegral P5OldFifthPointwiseQ
open P5OldFifthFirstFConcavity P5OldFifthChildQJensen

abbrev Point := Fin 5 → ℝ

def box (a b : Point) : Set Point := logPrimeBox a b
def boxVolume (a b : Point) : ℝ := ∏ i : Fin 5, b i - a i
def fraction (a b : Point) (i : Fin 5) (t : Point) : ℝ :=
  (t i - a i) / (b i - a i)
def low (a : Point) (i : Fin 5) (t : Point) : Point := Function.update t i (a i)
def high (b : Point) (i : Fin 5) (t : Point) : Point := Function.update t i (b i)
def vertex (a b : Point) (ε : VertexChoice) : Point :=
  fun i => if ε i then b i else a i
def weight (a b : Point) (ε : VertexChoice) (t : Point) : ℝ :=
  ∏ i : Fin 5, if ε i then fraction a b i t else 1 - fraction a b i t

theorem box_subset_closed (a b : Point) : box a b ⊆ Icc a b := by
  intro t ht
  have h := mem_logPrimeBox.mp ht
  exact ⟨fun i => (h i).1, fun i => (h i).2.le⟩

theorem fraction_mem (a b : Point) (hab : ∀ i, a i < b i)
    (i : Fin 5) {t : Point} (ht : t ∈ Icc a b) :
    fraction a b i t ∈ Icc (0 : ℝ) 1 := by
  have hs : 0 < b i - a i := sub_pos.mpr (hab i)
  exact ⟨div_nonneg (sub_nonneg.mpr (ht.1 i)) hs.le,
    (div_le_one hs).mpr (by linarith [ht.2 i])⟩

theorem low_mem (a b : Point) (hab : ∀ i, a i < b i)
    (i : Fin 5) {t : Point} (ht : t ∈ Icc a b) : low a i t ∈ Icc a b := by
  constructor <;> intro k <;> by_cases hk : k = i
  · subst k; simp [low]
  · simpa [low, hk, Ne.symm hk] using ht.1 k
  · subst k; simpa [low] using (hab i).le
  · simpa [low, hk, Ne.symm hk] using ht.2 k

theorem high_mem (a b : Point) (hab : ∀ i, a i < b i)
    (i : Fin 5) {t : Point} (ht : t ∈ Icc a b) : high b i t ∈ Icc a b := by
  constructor <;> intro k <;> by_cases hk : k = i
  · subst k; simpa [high] using (hab i).le
  · simpa [high, hk, Ne.symm hk] using ht.1 k
  · subst k; simp [high]
  · simpa [high, hk, Ne.symm hk] using ht.2 k

theorem mix_endpoints (a b : Point) (hab : ∀ i, a i < b i)
    (i : Fin 5) (t : Point) :
    mix (fraction a b i t) (low a i t) (high b i t) = t := by
  funext k
  by_cases hk : k = i
  · subst k
    simp only [mix, low, high, Function.update_same, fraction]
    field_simp [(sub_pos.mpr (hab i)).ne']
    <;> ring
  · simp [mix, low, high, hk, Ne.symm hk]
    ring

def tree (picks : ParentPicks) (raw : FifthWireRow) (a b : Point) :
    List (Fin 5) → Point → ℝ
  | [], t => frozenGap picks raw t
  | i :: rest, t =>
      (1 - fraction a b i t) * tree picks raw a b rest (low a i t) +
        fraction a b i t * tree picks raw a b rest (high b i t)

theorem tree_le_gap (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (hab : ∀ i, a i < b i) (coords : List (Fin 5))
    (t : Point) (ht : t ∈ Icc a b) :
    tree picks raw a b coords t ≤ frozenGap picks raw t := by
  induction coords generalizing t with
  | nil => rfl
  | cons i rest ih =>
      have hq := fraction_mem a b hab i ht
      have hl := ih (low a i t) (low_mem a b hab i ht)
      have hh := ih (high b i t) (high_mem a b hab i ht)
      have hc := frozenGap_concave_pair picks raw (fraction a b i t)
        hq.1 hq.2 (low a i t) (high b i t)
      rw [mix_endpoints a b hab i t] at hc
      exact (add_le_add
        (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hq.2))
        (mul_le_mul_of_nonneg_left hh hq.1)).trans hc

def endpoint (a b : Point) (i : Fin 5) (e : Bool) (t : Point) : Point :=
  if e then high b i t else low a i t

def factor (a b : Point) (i : Fin 5) (e : Bool) (t : Point) : ℝ :=
  if e then fraction a b i t else 1 - fraction a b i t

def corner (a b : Point) (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) : Point :=
  endpoint a b 4 e₄ (endpoint a b 3 e₃
    (endpoint a b 2 e₂ (endpoint a b 1 e₁ (endpoint a b 0 e₀ t))))

def wordWeight (a b : Point) (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) : ℝ :=
  factor a b 0 e₀ t * factor a b 1 e₁ t * factor a b 2 e₂ t *
    factor a b 3 e₃ t * factor a b 4 e₄ t

theorem tree_eq_nested (picks : ParentPicks) (raw : FifthWireRow)
    (a b t : Point) :
    tree picks raw a b allFiveCoordinates t =
      ∑ e₀ : Bool, ∑ e₁ : Bool, ∑ e₂ : Bool, ∑ e₃ : Bool, ∑ e₄ : Bool,
        wordWeight a b e₀ e₁ e₂ e₃ e₄ t *
          frozenGap picks raw (corner a b e₀ e₁ e₂ e₃ e₄ t) := by
  simp [tree, allFiveCoordinates, Fintype.sum_bool,
    wordWeight, corner, factor, endpoint, fraction, low, high, Function.update]
  ring

theorem corner_eq_vertex (a b : Point) (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) :
    corner a b e₀ e₁ e₂ e₃ e₄ t = vertex a b (![e₀, e₁, e₂, e₃, e₄]) := by
  funext i
  fin_cases i <;> simp [corner, endpoint, vertex, low, high, Function.update]

theorem wordWeight_eq_weight (a b : Point) (e₀ e₁ e₂ e₃ e₄ : Bool) (t : Point) :
    wordWeight a b e₀ e₁ e₂ e₃ e₄ t = weight a b (![e₀, e₁, e₂, e₃, e₄]) t := by
  simp [wordWeight, weight, factor, Fin.prod_univ_succ]
  ring

/-- Literal 32 leaves, in the already used original Word order. -/
theorem tree_eq_word_sum (picks : ParentPicks) (raw : FifthWireRow)
    (a b t : Point) :
    tree picks raw a b allFiveCoordinates t =
      ∑ w : Word, weight a b (wordChoice w) t *
        frozenGap picks raw (vertex a b (wordChoice w)) := by
  rw [tree_eq_nested]
  simp only [Fintype.sum_prod_type]
  simp [wordChoice, corner_eq_vertex, wordWeight_eq_weight]

theorem integrableOn_weight (a b : Point) (ε : VertexChoice) :
    IntegrableOn (weight a b ε) (box a b) := by
  unfold IntegrableOn weight box fraction logPrimeBox
  rw [volume_pi, Measure.restrict_pi_pi]
  apply Integrable.fintype_prod
  intro i
  have hc : Continuous (fun x : ℝ => if ε i then (x - a i) / (b i - a i)
      else 1 - (x - a i) / (b i - a i)) := by
    by_cases hi : ε i <;> simp [hi] <;> fun_prop
  exact hc.integrableOn_Icc.mono_set Ico_subset_Icc_self

/-- Each barycentric word has exactly one thirty-second of the ORIGINAL
parent volume; there is no child count or grid1600 scale in this identity. -/
theorem integral_weight (a b : Point) (hab : ∀ i, a i < b i) (ε : VertexChoice) :
    (∫ t in box a b, weight a b ε t) = boxVolume a b / 32 := by
  unfold weight box fraction logPrimeBox
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hm : ∀ i : Fin 5,
      (∫ x in Ico (a i) (b i), if ε i then (x - a i) / (b i - a i)
        else 1 - (x - a i) / (b i - a i)) = (b i - a i) / 2 := by
    intro i
    by_cases hi : ε i
    · simpa [hi] using integral_fraction_Ico (hab i)
    · simpa [hi] using integral_one_sub_fraction_Ico (hab i)
  simp_rw [hm]
  simp [boxVolume, Finset.prod_div_distrib, Fin.prod_univ_succ]

theorem integrableOn_gap (picks : ParentPicks) (raw : FifthWireRow) (a b : Point) :
    IntegrableOn (frozenGap picks raw) (box a b) :=
  (continuous_frozenGap picks raw).integrableOn_Icc.mono_set (box_subset_closed a b)

/-- Actual concavity plus actual affine moments prove the vertex-to-integral
step. The equality of archived d to these vertices is supplied separately. -/
theorem integral_gap_ge_vertex_mean (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (hab : ∀ i, a i < b i) :
    (boxVolume a b / 32) *
        (∑ w : Word, frozenGap picks raw (vertex a b (wordChoice w))) ≤
      ∫ t in box a b, frozenGap picks raw t := by
  have hi : ∀ w : Word, IntegrableOn (fun t => weight a b (wordChoice w) t *
      frozenGap picks raw (vertex a b (wordChoice w))) (box a b) :=
    fun w => (integrableOn_weight a b (wordChoice w)).mul_const _
  have htree : IntegrableOn (tree picks raw a b allFiveCoordinates) (box a b) := by
    simp only [tree_eq_word_sum]
    exact integrable_finset_sum _ (fun w _ => hi w)
  have hm := setIntegral_mono_on htree (integrableOn_gap picks raw a b)
    (measurableSet_logPrimeBox a b)
    (fun t ht => tree_le_gap picks raw a b hab _ t (box_subset_closed a b ht))
  have heq : (∫ t in box a b, tree picks raw a b allFiveCoordinates t) =
      (boxVolume a b / 32) *
        ∑ w : Word, frozenGap picks raw (vertex a b (wordChoice w)) := by
    rw [tree_eq_word_sum, integral_finset_sum _ (fun w _ => hi w)]
    simp_rw [integral_mul_const, integral_weight a b hab]
    rw [Finset.mul_sum]
  exact heq.symm.trans_le hm

theorem boxVolume_pos (a b : Point) (hab : ∀ i, a i < b i) :
    0 < boxVolume a b :=
  Finset.prod_pos (fun i _ => sub_pos.mpr (hab i))

theorem boxVolume_eq_measureReal (a b : Point) (hab : ∀ i, a i < b i) :
    volume.real (box a b) = boxVolume a b := by
  rw [Measure.real, box, logPrimeBox, volume_pi_pi]
  simp only [Real.volume_Ico, ENNReal.toReal_prod]
  unfold boxVolume
  apply Finset.prod_congr rfl
  intro i _
  exact ENNReal.toReal_ofReal (sub_pos.mpr (hab i)).le

def X (picks : ParentPicks) (raw : FifthWireRow) (b : Point) (t : Point) : ℝ :=
  max 0 (frozenGap picks raw t) / b 4

theorem continuous_X (picks : ParentPicks) (raw : FifthWireRow) (b : Point) :
    Continuous (X picks raw b) :=
  (continuous_const.max (continuous_frozenGap picks raw)).div_const _

theorem X_bounds (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (hab : ∀ i, a i < b i) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hs : 2 ≤ s)
    (hnew : ∀ t ∈ Icc a b, residual (rawCandidate 0 raw t) t ≤ s)
    {t : Point} (ht : t ∈ Icc a b) :
    X picks raw b t ∈ Icc (0 : ℝ) (s - 2) ∧
      max 0 (frozenGap picks raw t) / t 4 ∈ Icc (0 : ℝ) (s - 2) ∧
      X picks raw b t ≤ max 0 (frozenGap picks raw t) / t 4 := by
  have ht4 : 0 < t 4 := (ha 4).trans_le (ht.1 4)
  have hb4 : 0 < b 4 := (ha 4).trans (hab 4)
  have hg := P5OldFifthActualChildJensenIntegral.positive_gap_le_ratio_times_last
    picks raw t ht4 hs (hnew t ht)
  have h0 : 0 ≤ max 0 (frozenGap picks raw t) := le_max_left _ _
  have hr : max 0 (frozenGap picks raw t) / t 4 ≤ s - 2 :=
    (div_le_iff₀ ht4).mpr hg
  have hXr : X picks raw b t ≤ max 0 (frozenGap picks raw t) / t 4 :=
    div_le_div_of_nonneg_left h0 ht4 (ht.2 4)
  exact ⟨⟨div_nonneg h0 hb4.le, hXr.trans hr⟩,
    ⟨div_nonneg h0 ht4.le, hr⟩, hXr⟩

/-- Original uniform-parent Jensen. The only scalar identification is the
actual 32-vertex mean divided by the original last upper endpoint. -/
theorem Q_average_ge_vertex_input (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (hab : ∀ i, a i < b i) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hs2 : 2 < s) (hs4 : s ≤ 4)
    (hnew : ∀ t ∈ Icc a b, residual (rawCandidate 0 raw t) t ≤ s)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) (s - 2))
    (heq : e = ((∑ w : Word, frozenGap picks raw (vertex a b (wordChoice w))) / 32) / b 4) :
    Q s e ≤ ⨍ t in box a b, Q s (X picks raw b t) := by
  let C := box a b
  let V := boxVolume a b
  let T := b 4
  let Y := X picks raw b
  have hT : 0 < T := (ha 4).trans (hab 4)
  have hV : 0 < V := boxVolume_pos a b hab
  have hmass : volume.real C = V := boxVolume_eq_measureReal a b hab
  have hzero : volume C ≠ 0 := by
    intro hz
    have hh : volume.real C = 0 := by simp [hz, Measure.real]
    linarith
  have htop : volume C ≠ ∞ := by
    intro hz
    have hh : volume.real C = 0 := by simp [hz, Measure.real]
    linarith
  have hXrange : ∀ t ∈ Icc a b, Y t ∈ Icc (0 : ℝ) (s - 2) :=
    fun t ht => (X_bounds picks raw a b hab ha hs2.le hnew ht).1
  have hYint : IntegrableOn Y C :=
    (continuous_X picks raw b).integrableOn_Icc.mono_set (box_subset_closed a b)
  have hQint : IntegrableOn (fun t => Q s (Y t)) C :=
    (((Q_continuousOn s hs2).comp (continuous_X picks raw b).continuousOn
      hXrange).integrableOn_compact isCompact_Icc).mono_set (box_subset_closed a b)
  have hYae : ∀ᵐ t ∂volume.restrict C, Y t ∈ Icc (0 : ℝ) (s - 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox a b)] with t ht
    exact hXrange t (box_subset_closed a b ht)
  have hmeanRange : (⨍ t in C, Y t) ∈ Icc (0 : ℝ) (s - 2) :=
    (convex_Icc _ _).set_average_mem isClosed_Icc hzero htop hYae hYint
  have hJ := (Q_convexOn_no_calculus_input hs2.le hs4).map_set_average_le
    (Q_continuousOn s hs2) isClosed_Icc hzero htop hYae hYint hQint
  have hgapY : (∫ t in C, frozenGap picks raw t) / T ≤ ∫ t in C, Y t := by
    have hm := setIntegral_mono_on ((integrableOn_gap picks raw a b).div_const T)
      hYint (measurableSet_logPrimeBox a b) (fun t _ =>
        div_le_div_of_nonneg_right (le_max_right _ _) hT.le)
    simpa only [integral_div] using hm
  have hvertex := integral_gap_ge_vertex_mean picks raw a b hab
  have hlower : V * e ≤ ∫ t in C, Y t := by
    have hh := div_le_div_of_nonneg_right hvertex hT.le
    rw [heq]
    convert hh.trans hgapY using 1 <;> ring
  have hmean : e ≤ ⨍ t in C, Y t := by
    calc
      e = V⁻¹ * (V * e) := by field_simp [hV.ne']; ring
      _ ≤ V⁻¹ * (∫ t in C, Y t) :=
        mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hV.le)
      _ = _ := by rw [setAverage_eq, hmass]; simp [smul_eq_mul]
  exact ((Q_monotoneOn_no_calculus_input hs2.le hs4) he hmeanRange hmean).trans hJ

theorem continuousOn_movingProfile (a b : Point) (ha : ∀ i, 0 < a i)
    (level : Point → ℝ) (hlevel : Continuous level) :
    ContinuousOn (fun t => primeOwnCubeGatedProfile (level t) t) (Icc a b) := by
  have ht : ∀ t ∈ Icc a b, 0 < t (Fin.last 4) :=
    fun t ht => (ha _).trans_le (ht.1 _)
  have hlast : ContinuousOn (fun t : Point => t (Fin.last 4)) (Icc a b) :=
    (continuous_apply _).continuousOn
  have hsum : Continuous (fun t : Point => ∑ i, t i) := by fun_prop
  have harg := (hlevel.continuousOn.sub hsum.continuousOn).div hlast
    (fun t ht' => (ht t ht').ne')
  have hfactor := continuous_actualExtendedThirdLowerFactor.comp_continuousOn harg
  have hc : ContinuousOn (fun t => 4 * actualExtendedThirdLowerFactor
      ((level t - ∑ i, t i) / t (Fin.last 4)) / t (Fin.last 4)) (Icc a b) :=
    (continuousOn_const.mul hfactor).div hlast (fun t ht' => (ht t ht').ne')
  apply hc.congr
  intro t ht'
  rw [p1PrimeOwnCubeGatedProfile_eq_profile _ t (ht t ht'),
    p1PrimeTupleMinusProfile_eq_lowerFactor _ t (ht t ht')]

theorem integrableOn_frozenKernel (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (ha : ∀ i, 0 < a i) :
    IntegrableOn (frozenUpperPositiveKernel picks raw) (box a b) := by
  have hp : ContinuousOn (fun t : Point => ∏ i, 1 / t i) (Icc a b) := by
    apply continuousOn_finsetProd Finset.univ
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun t ht => ((ha i).trans_le (ht.1 i)).ne')
  have hn := continuousOn_movingProfile a b ha _ (continuous_rawCandidate 0 raw)
  have ho := continuousOn_movingProfile a b ha _ (continuous_frozenParentUpper picks)
  have hc : ContinuousOn (frozenUpperPositiveKernel picks raw) (Icc a b) :=
    continuousOn_const.sup ((hn.sub ho).mul hp)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (box_subset_closed a b)

def prefactor (b : Point) : ℝ := (4 / b 4) * ∏ i : Fin 5, 1 / b i

/-- Whole-parent Jensen with the full original reciprocal-prime amplitude.
The endpoint amplitude is multiplied by parent volume exactly once. -/
theorem integral_frozenKernel_ge_Jensen (picks : ParentPicks) (raw : FifthWireRow)
    (a b : Point) (hab : ∀ i, a i < b i) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hs2 : 2 < s) (hs4 : s ≤ 4)
    (hnew : ∀ t ∈ Icc a b, residual (rawCandidate 0 raw t) t ≤ s)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) (s - 2))
    (heq : e = ((∑ w : Word, frozenGap picks raw (vertex a b (wordChoice w))) / 32) / b 4) :
    boxVolume a b * prefactor b * Q s e ≤
      ∫ t in box a b, frozenUpperPositiveKernel picks raw t := by
  have hb : ∀ i, 0 < b i := fun i => (ha i).trans (hab i)
  have hA : 0 ≤ prefactor b :=
    mul_nonneg (div_nonneg (by norm_num) (hb 4).le)
      (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hb i).le))
  have hXrange : ∀ t ∈ Icc a b, X picks raw b t ∈ Icc (0 : ℝ) (s - 2) :=
    fun t ht => (X_bounds picks raw a b hab ha hs2.le hnew ht).1
  have hQint : IntegrableOn (fun t => Q s (X picks raw b t)) (box a b) :=
    (((Q_continuousOn s hs2).comp (continuous_X picks raw b).continuousOn
      hXrange).integrableOn_compact isCompact_Icc).mono_set (box_subset_closed a b)
  have hpoint : ∀ t ∈ box a b, prefactor b * Q s (X picks raw b t) ≤
      frozenUpperPositiveKernel picks raw t := by
    intro t ht
    have hc := box_subset_closed a b ht
    have htp : ∀ i, 0 < t i := fun i => (ha i).trans_le (hc.1 i)
    obtain ⟨hX, hr, hXr⟩ := X_bounds picks raw a b hab ha hs2.le hnew hc
    have hweight : prefactor b ≤ (4 / t 4) * ∏ i : Fin 5, 1 / t i := by
      apply mul_le_mul
        (div_le_div_of_nonneg_left (by norm_num) (htp 4) (hc.2 4))
      · apply Finset.prod_le_prod
        · intro i _; exact one_div_nonneg.mpr (hb i).le
        · intro i _; exact div_le_div_of_nonneg_left (by norm_num) (htp i) (hc.2 i)
      · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hb i).le)
      · exact div_nonneg (by norm_num) (htp 4).le
    have hlocal0 : 0 ≤ (4 / t 4) * ∏ i : Fin 5, 1 / t i := by positivity
    calc
      _ ≤ ((4 / t 4) * ∏ i : Fin 5, 1 / t i) * Q s (X picks raw b t) :=
        mul_le_mul_of_nonneg_right hweight (Q_nonneg hs2.le hs4 hX)
      _ ≤ ((4 / t 4) * ∏ i : Fin 5, 1 / t i) *
          Q s (max 0 (frozenGap picks raw t) / t 4) :=
        mul_le_mul_of_nonneg_left
          ((Q_monotoneOn_no_calculus_input hs2.le hs4) hX hr hXr) hlocal0
      _ ≤ _ := frozenUpperPositiveKernel_ge_Q_no_calculus_input
        picks raw t htp s hs2 hs4 (hnew t hc)
  have hint := setIntegral_mono_on (hQint.const_mul (prefactor b))
    (integrableOn_frozenKernel picks raw a b ha) (measurableSet_logPrimeBox a b) hpoint
  rw [integral_const_mul] at hint
  have hV := boxVolume_pos a b hab
  have hJ := mul_le_mul_of_nonneg_left
    (Q_average_ge_vertex_input picks raw a b hab ha hs2 hs4 hnew e he heq)
    (mul_nonneg hV.le hA)
  rw [setAverage_eq, boxVolume_eq_measureReal a b hab] at hJ
  simp only [smul_eq_mul] at hJ
  have hid : boxVolume a b * prefactor b *
      ((boxVolume a b)⁻¹ * (∫ t in box a b, Q s (X picks raw b t))) =
      prefactor b * (∫ t in box a b, Q s (X picks raw b t)) := by
    field_simp [hV.ne']
    <;> ring
  rw [hid] at hJ
  exact hJ.trans hint

end
end ImbalancedChen.P5OriginalParentBoxJensen
