import ImbalancedChen.P5OldFifthPointwiseQ
import ImbalancedChen.P5OldFifthFirstFConcavity
import Mathlib.Analysis.Convex.Integral

/-! SOURCE ONLY / UNCOMPILED / READY=false / ZERO FORMAL CREDIT.
Convex Jensen for Q_b on one actual grid1600 child, sourced from the
previous gap integral and strict-gate pointwise bridge. The saved
parent picks, integer d and A/B geometry remain explicit guards.
The firstF calculus lemmas are pending in a separate source. -/

namespace ImbalancedChen.P5OldFifthChildQJensen
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree
open P5OldFifthFiveCoordinateBarycentric
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ
open P5OldFifthFirstFConcavity

theorem Q_convexOn (b : ℝ) (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hconc : ConcaveOn ℝ (Icc (2 : ℝ) 4) firstF) :
    ConvexOn ℝ (Icc 0 (b - 2)) (Q b) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have hbx : b - x ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hby : b - y ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hc := hconc.2 hbx hby hα hβ hsum
  have harg : b - (α * x + β * y) =
      α * (b - x) + β * (b - y) := by
    calc
      b - (α * x + β * y) = (α + β) * b -
          (α * x + β * y) := by rw [hsum]; ring
      _ = _ := by ring
  simp only [smul_eq_mul] at hc
  rw [← harg] at hc
  simp only [Q]
  linarith [hc]

theorem Q_monotoneOn (b : ℝ) (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hmono : MonotoneOn firstF (Icc (2 : ℝ) 4)) :
    MonotoneOn (Q b) (Icc 0 (b - 2)) := by
  intro x hx y hy hxy
  have hbx : b - x ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hby : b - y ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hf := hmono hby hbx (by linarith)
  unfold Q
  linarith

theorem Q_continuousOn (b : ℝ) (hb2 : 2 < b) :
    ContinuousOn (Q b) (Icc 0 (b - 2)) := by
  intro u hu
  have hden : b - u ≠ 0 := by linarith [hu.2]
  have hlog : b - u - 1 ≠ 0 := by linarith [hu.2]
  unfold Q firstF
  fun_prop

theorem childVolume_pos (raw : FifthWireRow) (c : ChildIndex) :
    0 < childVolume raw c := by
  unfold childVolume
  exact Finset.prod_pos (fun i _ => child_span_pos raw c i)

theorem childVolume_eq_measureReal (raw : FifthWireRow)
    (c : ChildIndex) :
    volume.real (childBox raw c) = childVolume raw c := by
  have hbox : childBox raw c =
      logPrimeBox (childLeft raw c) (childRight raw c) := by
    ext t
    simp [childBox, mem_logPrimeBox, childLeft, childRight]
  rw [Measure.real, hbox, logPrimeBox, volume_pi_pi]
  simp only [Real.volume_Ico, ENNReal.toReal_prod]
  unfold childVolume
  apply Finset.prod_congr rfl
  intro i _
  exact ENNReal.toReal_ofReal (child_span_pos raw c i).le

def childX (picks : ParentPicks) (raw : FifthWireRow)
    (c : ChildIndex) (t : Point) : ℝ :=
  max 0 (frozenGap picks raw t) / childRight raw c 4

theorem childX_continuous (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) :
    Continuous (childX picks raw c) := by
  unfold childX
  exact (continuous_const.max (continuous_frozenGap picks raw)).div_const _

theorem childX_integrableOn (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) :
    IntegrableOn (childX picks raw c) (childBox raw c) := by
  have hclosed : IntegrableOn (childX picks raw c)
      (Icc (childLeft raw c) (childRight raw c)) :=
    (childX_continuous picks raw c).integrableOn_Icc
  apply hclosed.mono_set
  intro t ht
  exact ⟨fun i => (ht i).1, fun i => (ht i).2.le⟩

/-- Jensen on the actual child with the exact saved integer d guard.
The input range on the closed child is the script's A/B ratio enclosure;
it is not an assumed integral bound. -/
theorem child_Q_average_ge_saved_e
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (b : ℝ) (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hT : 0 < childRight raw c 4)
    (hXrange : ∀ t ∈ Icc (childLeft raw c) (childRight raw c),
      childX picks raw c t ∈ Icc 0 (b - 2))
    (d : ℤ) (hd : (d : ℝ) = vertexD picks raw c)
    (he : (d : ℝ) / (1024 * 1600 * childRight raw c 4) ∈
      Icc 0 (b - 2)) :
    Q b ((d : ℝ) / (1024 * 1600 * childRight raw c 4)) ≤
      ⨍ t in childBox raw c, Q b (childX picks raw c t) := by
  let C := childBox raw c
  let V := childVolume raw c
  let T := childRight raw c 4
  let X := childX picks raw c
  let e := (d : ℝ) / (1024 * 1600 * T)
  have hconc : ConcaveOn ℝ (Icc (2 : ℝ) 4) firstF :=
    firstF_concaveOn
  have hmono : MonotoneOn firstF (Icc (2 : ℝ) 4) :=
    firstF_monotoneOn
  have hV : 0 < V := childVolume_pos raw c
  have hmass : volume.real C = V := childVolume_eq_measureReal raw c
  have hzero : volume C ≠ 0 := by
    intro hz
    have h : volume.real C = 0 := by simp [hz, Measure.real]
    linarith
  have htop : volume C ≠ ∞ := by
    intro hz
    have h : volume.real C = 0 := by simp [hz, Measure.real]
    linarith
  have hclosed : childBox raw c ⊆
      Icc (childLeft raw c) (childRight raw c) := by
    intro t ht
    exact ⟨fun i => (ht i).1, fun i => (ht i).2.le⟩
  have hXint : IntegrableOn X C := childX_integrableOn picks raw c
  have hQint : IntegrableOn (fun t => Q b (X t)) C := by
    have hc : ContinuousOn (fun t => Q b (X t))
        (Icc (childLeft raw c) (childRight raw c)) :=
      (Q_continuousOn b hb2).comp
        (childX_continuous picks raw c).continuousOn hXrange
    exact (hc.integrableOn_compact isCompact_Icc).mono_set hclosed
  have hXae : ∀ᵐ t ∂volume.restrict C, X t ∈ Icc 0 (b - 2) := by
    filter_upwards [ae_restrict_mem (childBox_measurable raw c)] with t ht
    exact hXrange t (hclosed ht)
  have hE_in : (⨍ t in C, X t) ∈ Icc 0 (b - 2) :=
    (convex_Icc _ _).set_average_mem isClosed_Icc hzero htop
      hXae hXint
  have hJensen :
      Q b (⨍ t in C, X t) ≤ ⨍ t in C, Q b (X t) :=
    (Q_convexOn b hb2 hb4 hconc).map_set_average_le
      (Q_continuousOn b hb2) isClosed_Icc hzero htop
      hXae hXint hQint
  have hgap := integrableOn_frozenGap picks raw c
  have hXge : (∫ t in C, frozenGap picks raw t) / T ≤
      ∫ t in C, X t := by
    have hp : ∀ t ∈ C,
        frozenGap picks raw t / T ≤ X t := by
      intro t _
      exact div_le_div_of_nonneg_right (le_max_right _ _) hT.le
    have hm := setIntegral_mono_on (hgap.div_const T) hXint
      (childBox_measurable raw c) hp
    simpa [X, childX, integral_div] using hm
  have hgapD := integral_frozenGap_ge_saved_integer_d
    picks raw c d hd
  have hXlower : V * e ≤ ∫ t in C, X t := by
    have hh := div_le_div_of_nonneg_right hgapD hT.le
    dsimp [e, V, T] at *
    convert hh.trans hXge using 1 <;> ring
  have hmean : e ≤ ⨍ t in C, X t := by
    calc
      e = V⁻¹ * (V * e) := by field_simp [hV.ne']; ring
      _ ≤ V⁻¹ * (∫ t in C, X t) :=
        mul_le_mul_of_nonneg_left hXlower (inv_nonneg.mpr hV.le)
      _ = ⨍ t in C, X t := by
        rw [setAverage_eq, hmass]
        simp [smul_eq_mul]
  have hQmono := Q_monotoneOn b hb2 hb4 hmono
  exact (hQmono he hE_in hmean).trans hJensen

end
end ImbalancedChen.P5OldFifthChildQJensen
