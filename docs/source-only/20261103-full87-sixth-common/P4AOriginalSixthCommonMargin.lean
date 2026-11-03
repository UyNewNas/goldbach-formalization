import ImbalancedChen.P4AOriginalSixthActionBank
import ImbalancedChen.P4AOriginalFull87TrimOmission

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

All geometrically licensed saved/eleven/later actions are simultaneously
trimmed by their ACTUAL lower-square margins. The geometric supercover does
not depend on e,q,omega,N,prime tuples, a winning row, or quantizer precision.
Every point is eventually in the safe strata: no null-wall argument and no
assumed positive uniform gap on an open original source is needed.

The weighted omission statement requires integrability explicitly. The
unconditional instance pays Euclidean volume only, not a prime mean or any
compiler/density reserve. The existing policy/state list is NOT filtered.
-/
namespace ImbalancedChen.P4AOriginalSixthCommonMargin
noncomputable section
open scoped Classical BigOperators Topology ENNReal
open Set Filter MeasureTheory
open P4AOriginalSixthActionBank P1QuantizedActionLicense
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P4AOriginalFull87SourceDictionary (Cell Point)
open P4AOriginalFull87StrictActionTrim (sourceSet)

/-- Conditional margins: an action which is geometrically inactive imposes
NO extra test. In particular neither a failed row nor an equality/inherit
branch is silently declared active. This set is measurable; no compactness
or closedness of this conditional stratum is asserted. -/
def safe (delta : ℝ) : Set Point6 :=
  {t | ∀ a : Entry, GeometricSource a.val t →
    ∀ g : P1QuantizedActionLicense.Gate 6,
      gate (selected a.val) t g + delta ≤ endpoint a.val t}

theorem safe_antitone {delta eta : ℝ} (h : delta ≤ eta) : safe eta ⊆ safe delta := by
  intro t ht a ha g
  have hg := ht a ha g
  linarith

theorem measurableSet_safe (delta : ℝ) : MeasurableSet (safe delta) := by
  have heq : safe delta = ⋂ a : Entry,
      ({t | GeometricSource a.val t}ᶜ ∪
        ⋂ g : P1QuantizedActionLicense.Gate 6,
          {t | gate (selected a.val) t g + delta ≤ endpoint a.val t}) := by
    ext t
    simp [safe, imp_iff_not_or]
  rw [heq]
  apply MeasurableSet.iInter
  intro a
  exact (geometricSource_measurable a.val).compl.union
    (MeasurableSet.iInter fun g =>
      (isClosed_le ((gate_continuous a.val g).add continuous_const)
        (endpoint_continuous a.val)).measurableSet)

/-- A finite pointwise minimum is derived implicitly by finite eventual
conjunction, including inactive entries. This is not a uniform gap premise. -/
theorem eventually_safe (t : Point6) :
    ∀ᶠ r : ℕ in atTop, t ∈ safe (width r) := by
  change ∀ᶠ r : ℕ in atTop, ∀ a : Entry, GeometricSource a.val t →
    ∀ g : P1QuantizedActionLicense.Gate 6,
      gate (selected a.val) t g + width r ≤ endpoint a.val t
  apply eventually_all.mpr
  intro a
  by_cases ha : GeometricSource a.val t
  · have hl := geometric_lower_license a.val t ha
    have hg : ∀ᶠ r : ℕ in atTop, ∀ g : P1QuantizedActionLicense.Gate 6,
        gate (selected a.val) t g + width r ≤ endpoint a.val t := by
      apply eventually_all.mpr
      intro g
      filter_upwards [width_tendsto.eventually (gt_mem_nhds
        (sub_pos.mpr (hl g)))] with r hr
      linarith
    exact hg.mono (fun _ h _ => h)
  · exact Eventually.of_forall (fun _ h => (ha h).elim)

/-- The same fine-resolution threshold licenses EVERY original action on
this entire stratum. Nothing selects n from the prime tuple or winner. -/
theorem safe_rounded (delta : ℝ) (hd : 0 < delta) (n : ℕ)
    (hn : 4 * width n < delta) (t : Point6) (ht : t ∈ safe delta)
    (a : Action) (ha : GeometricSource a t) :
    LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
    (∀ g : P1QuantizedActionLicense.Gate 6,
      gate (selected a) t g + delta / 2 < (rounded n (endpoint a t) : ℝ)) ∧
    (rounded n (endpoint a t) : ℝ) + width n ≤
      VariableEnvelope.v (∑ j ∈ selected a, t j) := by
  have hup := geometric_upper_license a t ha
  obtain ⟨hlo,hhi⟩ := rounded_licensed n (selected a) t (endpoint a t) delta hd
    (hup.trans (VariableEnvelope.v_le_cap _))
    (ht ⟨a,mem_allActions a⟩ ha) hn
  exact ⟨fun g => by have hg := hlo g; linarith, hlo, hhi.trans hup⟩

def project6 (t : Point) : Point6 := fun i => t i.castSucc.castSucc

theorem continuous_project6 : Continuous project6 := by
  unfold project6
  fun_prop

def safe8 (delta : ℝ) : Set Point := project6 ⁻¹' safe delta

theorem measurableSet_safe8 (delta : ℝ) : MeasurableSet (safe8 delta) :=
  (measurableSet_safe delta).preimage continuous_project6.measurable

theorem eventually_safe8 (t : Point) :
    ∀ᶠ r : ℕ in atTop, t ∈ safe8 (width r) := eventually_safe (project6 t)

/-- A rejected point has an ORIGINAL geometrically licensed action and
one of its OWN lower gates with an insufficient positive margin. This is
an exact finite witness, not the wall set of an unrelated comparison. -/
theorem not_safe_witness (delta : ℝ) (t : Point6) (ht : t ∉ safe delta) :
    ∃ a ∈ allActions, GeometricSource a t ∧
      ∃ g : P1QuantizedActionLicense.Gate 6,
        0 < endpoint a t - gate (selected a) t g ∧
        endpoint a t - gate (selected a) t g < delta := by
  have h : ∃ a : Entry, GeometricSource a.val t ∧
      ∃ g : P1QuantizedActionLicense.Gate 6,
        endpoint a.val t < gate (selected a.val) t g + delta := by
    simpa only [safe, mem_setOf_eq, not_forall, not_imp, not_le] using ht
  obtain ⟨a,ha,g,hg⟩ := h
  refine ⟨a.val,a.property,ha,g,sub_pos.mpr (geometric_lower_license a.val t ha g),?_⟩
  linarith

def sixthOmitted (c : Cell) (r : ℕ) (f : Point → ℝ) : ℝ :=
  ∫ t in sourceSet c, (safe8 (width r))ᶜ.indicator (fun t => ‖f t‖) t

theorem sixthOmitted_eq_sdiff (c : Cell) (r : ℕ) (f : Point → ℝ) :
    sixthOmitted c r f = ∫ t in sourceSet c \ safe8 (width r), ‖f t‖ := by
  unfold sixthOmitted
  rw [setIntegral_indicator (measurableSet_safe8 (width r)).compl]
  rfl

theorem sixthOmitted_nonneg (c : Cell) (r : ℕ) (f : Point → ℝ) :
    0 ≤ sixthOmitted c r f := by
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ (safe8 (width r))ᶜ
  · simpa only [indicator_of_mem ht] using norm_nonneg (f t)
  · simp only [indicator_of_notMem ht, le_refl]

theorem tendsto_sixthOmitted (c : Cell) (f : Point → ℝ)
    (hf : IntegrableOn f (sourceSet c)) :
    Tendsto (fun r => sixthOmitted c r f) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (sourceSet c))
    (F := fun r => (safe8 (width r))ᶜ.indicator (fun t => ‖f t‖))
    (f := fun _ => (0 : ℝ)) (fun t => ‖f t‖)
    (fun r => (hf.norm.indicator (measurableSet_safe8 (width r)).compl).aestronglyMeasurable)
    hf.norm
    (fun r => Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (norm_indicator_le_norm_self (s := (safe8 (width r))ᶜ)
          (fun t => ‖f t‖) t))
    (Eventually.of_forall fun t => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_safe8 t] with r hr
      simp [hr])
  simpa only [sixthOmitted, integral_zero] using hlim

def totalSixthOmitted (r : ℕ) (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, sixthOmitted c r (f c)

theorem tendsto_totalSixthOmitted (f : Cell → Point → ℝ)
    (hf : ∀ c, IntegrableOn (f c) (sourceSet c)) :
    Tendsto (fun r => totalSixthOmitted r f) atTop (𝓝 0) := by
  have h := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => tendsto_sixthOmitted c (f c) (hf c))
  simpa only [totalSixthOmitted, Finset.sum_const_zero] using h

theorem exists_common_weighted_margin (f : Cell → Point → ℝ)
    (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ r0 : ℕ, ∀ r ≥ r0, totalSixthOmitted r f < epsilon :=
  eventually_atTop.mp ((tendsto_totalSixthOmitted f hf).eventually (gt_mem_nhds he))

/-- This unconditional pre-N choice is VOLUME only. Subsequent arithmetic
applications must instantiate their true weight and its integrability. -/
theorem exists_common_volume_margin (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ r0 : ℕ, ∀ r ≥ r0,
      totalSixthOmitted r (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_common_weighted_margin (fun _ _ => (1 : ℝ)) _ epsilon he
  intro c
  exact integrableOn_const (P4AOriginalFull87TrimOmission.source_volume_lt_top c).ne

end
end ImbalancedChen.P4AOriginalSixthCommonMargin
