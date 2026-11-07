import ImbalancedChen.Part5OriginalUpsilon5CausalDictionary
import Mathlib.Analysis.Normed.Group.FunctionSeries
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
Original enhanced U5: exact first/second lower-factor split. SOURCE ONLY.
The preceding dictionary's geometry is consumed, not reconstructed.

The manuscript defines abar(s)=s*f(s)/(2 exp(gamma)); this is the lower
linear-sieve factor. The Buchstab kernel belongs to other root occurrences.
The first region below includes s=4; the second is strictly s>4.
Correction regularity is an explicit analytic prerequisite, not a claim
that the adopted finite h248 table is continuous or has count semantics.
-/

namespace ImbalancedChen.Part5OriginalUpsilon5CausalDictionary

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem continuous_level :
    Continuous (fun x : Fin 2 → ℝ => level (x 0) (x 1)) := by
  unfold level
  exact (VariableEnvelope.continuous_v.comp (continuous_apply 1)).max
    ((VariableEnvelope.continuous_v.comp
      ((continuous_apply 1).add (continuous_apply 0))).max continuous_const)

theorem continuous_residual : Continuous residual := by
  exact (continuous_level.sub (continuous_apply 0)).sub (continuous_apply 1)

theorem continuous_argument : Continuous argument := continuous_residual.div_const a

/-- The actual max level, not its ordinary-level surrogate, defines the wall. -/
theorem argument_le_four_iff (x : Fin 2 → ℝ) :
    argument x ≤ 4 ↔
      max (VariableEnvelope.v (x 1))
        (max (VariableEnvelope.v (x 1 + x 0)) (VariableEnvelope.B a)) ≤
          x 0 + x 1 + 4 * a := by
  unfold argument
  rw [div_le_iff₀ (show 0 < a by norm_num [a])]
  unfold residual level
  constructor <;> linarith

def firstRegion : Set (Fin 2 → ℝ) := triangle ∩ {x | argument x ≤ 4}
def secondRegion : Set (Fin 2 → ℝ) := triangle ∩ {x | 4 < argument x}

theorem measurableSet_firstRegion : MeasurableSet firstRegion :=
  measurableSet_triangle.inter
    (isClosed_le continuous_argument continuous_const).measurableSet

theorem measurableSet_secondRegion : MeasurableSet secondRegion :=
  measurableSet_triangle.inter
    (isOpen_lt continuous_const continuous_argument).measurableSet

theorem firstRegion_literal_max :
    firstRegion = triangle ∩ {x |
      max (VariableEnvelope.v (x 1))
        (max (VariableEnvelope.v (x 1 + x 0)) (VariableEnvelope.B a)) ≤
          x 0 + x 1 + 4 * a} := by
  ext x
  simp only [firstRegion, mem_inter_iff, mem_setOf_eq, argument_le_four_iff]

theorem regions_union : firstRegion ∪ secondRegion = triangle := by
  ext x
  simp only [firstRegion, secondRegion, mem_union, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hx
    by_cases hs : argument x ≤ 4
    · exact Or.inl ⟨hx, hs⟩
    · exact Or.inr ⟨hx, lt_of_not_ge hs⟩

theorem regions_disjoint : Disjoint firstRegion secondRegion := by
  apply disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hx.2) hy.2

private theorem even_domain {s : ℝ} (hs : 2 ≤ s) (k : ℕ) :
    s ∈ suzukiParityDomainOne 2 (2 * (k + 1)) := by
  simp [suzukiParityDomainOne, KappaOneModel.parityDomain, hs]

private theorem even_layer_bound {s : ℝ} (hs : 2 ≤ s) (k : ℕ) :
    ‖suzukiLayer 1 2 (2 * (k + 1)) s‖ ≤
      suzukiLayer 1 2 (2 * (k + 1)) 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_even_nonneg hs k)]
  exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
    (even_domain le_rfl k) (even_domain hs k) hs

/-- Continuity comes from the actual convergent even source series. -/
theorem continuousOn_actualLowerFactor :
    ContinuousOn suzukiContinuousLowerFactor (Ici (2 : ℝ)) := by
  have hc (k : ℕ) : ContinuousOn (suzukiLayer 1 2 (2 * (k + 1)))
      (Ici (2 : ℝ)) := by
    apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num)
      (2 * (k + 1))).mono
    intro s hs
    exact even_domain hs k
  unfold suzukiContinuousLowerFactor suzukiContinuousLowerTail
    suzukiProposition118SourceTMinus
  exact continuousOn_const.sub (continuousOn_tsum hc
    (summable_suzukiProposition118SourceTMinus_of_sourceContract
      jr1965Section13HatSourceContract (by norm_num : (2 : ℝ) ≤ 2))
    (fun k s hs => even_layer_bound hs k))

/-- On the second branch the actual source factor is the JR lower factor. -/
theorem actualLowerFactor_eq_JR {s : ℝ} (hs : s ∈ Icc (4 : ℝ) 5) :
    suzukiContinuousLowerFactor s =
      SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s := by
  exact suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    jr1965Section13HatSourceContract hs.1 (hs.2.trans (by norm_num))

theorem canonicalKernel_eq_JR_on_secondRegion (corr : ℝ → ℝ)
    {x : Fin 2 → ℝ} (hx : x ∈ secondRegion) :
    canonicalKernel corr x =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / a) *
          SwitchingPrinciple.dimensionOneLowerLinearSieveFactor (argument x) +
        4 * corr (argument x) / residual x := by
  unfold canonicalKernel
  rw [actualLowerFactor_eq_JR ⟨hx.2.le, (argument_mem hx.1).2⟩]

theorem continuousOn_lowerAmplitude : ContinuousOn lowerAmplitude (Icc (2 : ℝ) 5) := by
  exact (continuousOn_id.mul (continuousOn_actualLowerFactor.mono
    (fun _ hs => hs.1))).div_const _

/-- A compact closure used only to prove integrability of the original domain. -/
def closedTriangle : Set (Fin 2 → ℝ) :=
  (Set.univ.pi (fun _ : Fin 2 => Icc a h)) ∩ {x | x 0 ≤ x 1}

theorem isCompact_closedTriangle : IsCompact closedTriangle :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_le (continuous_apply 0) (continuous_apply 1))

theorem triangle_subset_closedTriangle : triangle ⊆ closedTriangle := by
  intro x hx
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  refine ⟨?_, hut.le⟩
  intro i _
  fin_cases i
  · exact ⟨hu, hut.le.trans ht.le⟩
  · exact ⟨hu.trans hut.le, ht.le⟩

theorem closedTriangle_bounds {x : Fin 2 → ℝ} (hx : x ∈ closedTriangle) :
    0 < residual x ∧ argument x ∈ Icc (2 : ℝ) 5 := by
  have hu := (hx.1 0 (mem_univ _)).1
  have ht := (hx.1 1 (mem_univ _)).2
  obtain ⟨hl, hh⟩ := residual_bounds hu hx.2 ht
  have ha : 0 < a := by norm_num [a]
  refine ⟨lt_of_lt_of_le (by norm_num) hl, ?_, ?_⟩
  · apply (le_div_iff₀ ha).mpr
    dsimp [a]
    linarith
  · apply (div_le_iff₀ ha).mpr
    dsimp [a]
    linarith

/-- Analytic regularity prerequisite; it does not assert finite-table soundness. -/
theorem continuousOn_kernel_closedTriangle (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    ContinuousOn (kernel corr) closedTriangle := by
  have hmap : MapsTo argument closedTriangle (Icc (2 : ℝ) 5) :=
    fun _ hx => (closedTriangle_bounds hx).2
  have hl := continuousOn_lowerAmplitude.comp continuous_argument.continuousOn hmap
  have hc := hcorr.comp continuous_argument.continuousOn hmap
  exact (continuousOn_const.mul (hl.add hc)).div continuous_residual.continuousOn
    (fun _ hx => (closedTriangle_bounds hx).1.ne')

theorem continuousOn_weightedKernel_closedTriangle (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    ContinuousOn (fun x => kernel corr x * ∏ i, 1 / x i) closedTriangle := by
  apply (continuousOn_kernel_closedTriangle corr hcorr).mul
  apply continuousOn_finsetProd
  intro i _
  apply continuousOn_const.div (continuous_apply i).continuousOn
  intro x hx
  have hlo := (hx.1 i (mem_univ _)).1
  exact (lt_of_lt_of_le (by norm_num [a] : 0 < a) hlo).ne'

theorem integrableOn_weightedKernel (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    IntegrableOn (fun x => kernel corr x * ∏ i, 1 / x i) triangle := by
  exact ((continuousOn_weightedKernel_closedTriangle corr hcorr).integrableOn_compact
    isCompact_closedTriangle).mono_set triangle_subset_closedTriangle

theorem integrableOn_canonicalWeightedKernel (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    IntegrableOn (fun x => canonicalKernel corr x * ∏ i, 1 / x i) triangle := by
  apply (integrableOn_weightedKernel corr hcorr).congr_fun ?_ measurableSet_triangle
  intro x hx
  rw [kernel_eq_canonical hx]

/-- Exact partition of the full real integral, including the equality wall. -/
theorem integral_split (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    integral corr =
      (∫ x in firstRegion, kernel corr x * ∏ i, 1 / x i) +
        ∫ x in secondRegion, kernel corr x * ∏ i, 1 / x i := by
  have hi := integrableOn_weightedKernel corr hcorr
  unfold integral
  rw [← regions_union]
  exact setIntegral_union regions_disjoint measurableSet_secondRegion
    (hi.mono_set inter_subset_left) (hi.mono_set inter_subset_left)

/-- Only the first piece is converted to log(s-1). The entire second piece
keeps the actual canonical lower factor with the exact original normalization. -/
theorem integral_split_log_canonical (corr : ℝ → ℝ)
    (hcorr : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    integral corr =
      (∫ x in firstRegion,
        (4 * (Real.log (argument x - 1) + corr (argument x)) / residual x) *
          ∏ i, 1 / x i) +
      ∫ x in secondRegion, canonicalKernel corr x * ∏ i, 1 / x i := by
  rw [integral_split corr hcorr]
  congr 1
  · apply setIntegral_congr_fun measurableSet_firstRegion
    intro x hx
    rw [kernel_eq_log_of_argument_le_four hx.1 hx.2]
  · apply setIntegral_congr_fun measurableSet_secondRegion
    intro x hx
    rw [kernel_eq_canonical hx.1]

end

end ImbalancedChen.Part5OriginalUpsilon5CausalDictionary
