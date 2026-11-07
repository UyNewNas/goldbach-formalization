import ImbalancedChen.P5ZU11MeasurableEnvelope
import ImbalancedChen.CurrentNumericalTransfer
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FinCases

/-!
Canonical switched-integrability supplier for original U11.

The actual pinned `LiLiuPrereqBuchstab.continuous_buchstab` is globally
continuous (BuchstabFunction.lean, theorem at line 98). Its actual bounds
`buchstab_nonneg` and `buchstab_le_one` hold on Ici 1
(BuchstabBounds.lean, lines 75--84). No substitute function is introduced.

The switched kernel is continuous on a compact box with z >= 417/5000,
which contains the complete original domain for every pair mask. This
closes the switched-integrability premise in the preceding envelope API.
Analytic policy licensing, cardinal means and quadrature are still open.
Status: source_written / uncompiled.
-/

namespace ImbalancedChen.P5Z.U11Canonical

open Set MeasureTheory
open U11Integral
open scoped BigOperators

noncomputable section

/-- A compact containing box, including every boundary seam of the
original ordered support and retaining the full fourth-prime upper wall. -/
def compactBox : Set LogFour :=
  Icc (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))

theorem isCompact_compactBox : IsCompact compactBox := isCompact_Icc

theorem originalDomain_subset_compactBox (mask : Set (ℝ × ℝ)) :
    originalDomain mask ⊆ compactBox := by
  intro v hv
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  constructor
  · intro i
    fin_cases i <;> dsimp <;> linarith
  · intro i
    fin_cases i <;> dsimp <;> linarith

theorem originalDomain_volume_lt_top (mask : Set (ℝ × ℝ)) :
    volume (originalDomain mask) < ∞ :=
  lt_of_le_of_lt (measure_mono (originalDomain_subset_compactBox mask))
    isCompact_compactBox.measure_lt_top

theorem originalDomain_argument_mem (mask : Set (ℝ × ℝ))
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 ∈ Icc (77 / 38 : ℝ) 8 := by
  have hlo := originalDomain_buchstab_argument_gt mask v hv
  have hz := (originalDomain_denominators_pos mask v hv).2
  refine ⟨hlo.le, ?_⟩
  apply (div_le_iff₀ hz).2
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  linarith

/-- The denominator is separated from zero on the entire containing
compact box, so continuity includes all ordered-support boundary seams. -/
theorem continuousOn_canonical_switched_compactBox (K : ℝ) :
    ContinuousOn (switchedKernel K LiLiuPrereqBuchstab.buchstab) compactBox := by
  have h0 : ContinuousOn (fun v : LogFour => v 0) compactBox :=
    (continuous_apply 0).continuousOn
  have h1 : ContinuousOn (fun v : LogFour => v 1) compactBox :=
    (continuous_apply 1).continuousOn
  have h2 : ContinuousOn (fun v : LogFour => v 2) compactBox :=
    (continuous_apply 2).continuousOn
  have h3 : ContinuousOn (fun v : LogFour => v 3) compactBox :=
    (continuous_apply 3).continuousOn
  have hz : ∀ v ∈ compactBox, v 2 ≠ 0 := by
    intro v hv
    have ha : (417 / 5000 : ℝ) ≤ v 2 := hv.1 2
    have hp : 0 < v 2 := by linarith
    exact hp.ne'
  have harg : ContinuousOn
      (fun v : LogFour => (1 - (v 0 + v 1 + v 2 + v 3)) / v 2) compactBox :=
    (continuousOn_const.sub (((h0.add h1).add h2).add h3)).div h2 hz
  exact (continuousOn_const.mul
    (LiLiuPrereqBuchstab.continuous_buchstab.comp_continuousOn harg)).div h2 hz

/-- Unconditional Lebesgue integrability of the actual original switched
kernel, for any fixed real K and any pair mask. No mean premise occurs. -/
theorem integrableOn_original_canonical_switched (mask : Set (ℝ × ℝ)) (K : ℝ) :
    IntegrableOn (switchedKernel K LiLiuPrereqBuchstab.buchstab)
      (originalDomain mask) volume := by
  have hi : IntegrableOn (switchedKernel K LiLiuPrereqBuchstab.buchstab)
      compactBox volume :=
    (continuousOn_canonical_switched_compactBox K).integrableOn_compact isCompact_compactBox
  exact hi.mono_set (originalDomain_subset_compactBox mask)

theorem integrableOn_original_current_switched (mask : Set (ℝ × ℝ)) :
    IntegrableOn (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
      (originalDomain mask) volume :=
  integrableOn_original_canonical_switched mask currentK

/-- The prime harmonic volume density used with four logarithmic labels. -/
def harmonicDensity (v : LogFour) : ℝ := 1 / (v 0 * v 1 * v 2 * v 3)

theorem continuousOn_harmonicDensity_compactBox :
    ContinuousOn harmonicDensity compactBox := by
  have hc : ∀ i : Fin 4, ContinuousOn (fun v : LogFour => v i) compactBox :=
    fun i => (continuous_apply i).continuousOn
  have hn : ∀ v ∈ compactBox, ∀ i : Fin 4, v i ≠ 0 := by
    intro v hv i
    have ha : (417 / 5000 : ℝ) ≤ v i := hv.1 i
    have hp : 0 < v i := by linarith
    exact hp.ne'
  have hprod := (((hc 0).mul (hc 1)).mul (hc 2)).mul (hc 3)
  exact continuousOn_const.div hprod
    (fun v hv => mul_ne_zero (mul_ne_zero (mul_ne_zero (hn v hv 0) (hn v hv 1))
      (hn v hv 2)) (hn v hv 3))

/-- Integrability also holds after inserting the actual four-prime
harmonic density, so the switch kernel can be used in the full Lebesgue
four-dimensional integral rather than only as an unweighted function. -/
theorem integrableOn_original_weighted_switched (mask : Set (ℝ × ℝ)) (K : ℝ) :
    IntegrableOn (fun v => harmonicDensity v *
      switchedKernel K LiLiuPrereqBuchstab.buchstab v) (originalDomain mask) volume := by
  have hc := continuousOn_harmonicDensity_compactBox.mul
    (continuousOn_canonical_switched_compactBox K)
  exact (hc.integrableOn_compact isCompact_compactBox).mono_set
    (originalDomain_subset_compactBox mask)

theorem canonical_switched_nonneg (mask : Set (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K)
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    0 ≤ switchedKernel K LiLiuPrereqBuchstab.buchstab v := by
  have hz := (originalDomain_denominators_pos mask v hv).2
  have hs : 1 ≤ (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by
    have hh := (originalDomain_argument_mem mask v hv).1
    linarith
  exact div_nonneg (mul_nonneg hK (LiLiuPrereqBuchstab.buchstab_nonneg hs)) hz.le

/-- A uniform explicit majorant on the complete original domain. The
proof uses the actual global bound omega <= 1, rather than sampled values. -/
theorem abs_canonical_switched_le (mask : Set (ℝ × ℝ)) (K : ℝ)
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    |switchedKernel K LiLiuPrereqBuchstab.buchstab v| ≤ |K| / (417 / 5000 : ℝ) := by
  have hz := (originalDomain_denominators_pos mask v hv).2
  have hzA : (417 / 5000 : ℝ) ≤ v 2 := by
    obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
    linarith
  have ha : (0 : ℝ) < 417 / 5000 := by norm_num
  have hs : 1 ≤ (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by
    have hh := (originalDomain_argument_mem mask v hv).1
    linarith
  have hw0 := LiLiuPrereqBuchstab.buchstab_nonneg hs
  have hw1 := LiLiuPrereqBuchstab.buchstab_le_one hs
  rw [switchedKernel, abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hz]
  apply (div_le_div_iff₀ hz ha).2
  have hwa : LiLiuPrereqBuchstab.buchstab
      ((1 - (v 0 + v 1 + v 2 + v 3)) / v 2) * (417 / 5000 : ℝ) ≤ v 2 := by
    calc
      _ ≤ 1 * (417 / 5000 : ℝ) := mul_le_mul_of_nonneg_right hw1 ha.le
      _ ≤ v 2 := by simpa only [one_mul] using hzA
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwa (abs_nonneg K)

/-- The previous envelope API no longer requires a switched-integrability
supplier: the canonical function supplies it directly. -/
theorem integrableOn_original_canonical_envelope (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (K : ℝ) (hK : 0 ≤ K)
    (H : ℝ → ℝ) (L : ℕ → LogFour → ℝ)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (hH : Measurable H) (hL : ∀ j ∈ bank, Measurable (L j))
    (ho : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 0 ≤ ordinaryKernel H L j v) :
    IntegrableOn (envelope bank
      (guarded eligible (switchedKernel K LiLiuPrereqBuchstab.buchstab) (ordinaryKernel H L)))
      (originalDomain mask) volume := by
  exact integrableOn_original_envelope mask hm bank eligible K
    LiLiuPrereqBuchstab.buchstab H L volume he
    LiLiuPrereqBuchstab.continuous_buchstab.measurable hH hL
    (canonical_switched_nonneg mask K hK) ho
    (integrableOn_original_canonical_switched mask K)

/-- Actual current K, actual canonical Buchstab, and no switched
integrability premise in the final original-domain integral partition. -/
theorem integral_original_current_envelope_eq_sum (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (H : ℝ → ℝ) (L : ℕ → LogFour → ℝ)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (hH : Measurable H) (hL : ∀ j ∈ bank, Measurable (L j))
    (ho : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 0 ≤ ordinaryKernel H L j v) :
    (∫ v in originalDomain mask,
      envelope bank (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
        (ordinaryKernel H L)) v) =
      ∑ c ∈ tags bank,
        ∫ v in winner (originalDomain mask) bank
            (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
              (ordinaryKernel H L)) c,
          (if c = 0 then switchedKernel currentK LiLiuPrereqBuchstab.buchstab v
            else ordinaryKernel H L c.pred v) := by
  exact integral_original_envelope_eq_sum mask hm bank eligible currentK
    LiLiuPrereqBuchstab.buchstab H L volume he
    LiLiuPrereqBuchstab.continuous_buchstab.measurable hH hL
    (canonical_switched_nonneg mask currentK (by norm_num [currentK])) ho
    (integrableOn_original_current_switched mask)

end

end ImbalancedChen.P5Z.U11Canonical
