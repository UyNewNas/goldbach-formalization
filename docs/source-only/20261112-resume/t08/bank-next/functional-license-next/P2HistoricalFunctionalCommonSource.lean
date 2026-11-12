import ImbalancedChen.P2HistoricalW1NativeClipping
import ImbalancedChen.P2HistoricalW2NativeFunctional

/-! One fixed depth, delta, Q and threshold for both genuine native
functionals on the original Wu convolution source boxes. -/
namespace ImbalancedChen.P2HistoricalFunctionalCommonSource

noncomputable section
open MeasureTheory Wu2008DoubleSieve P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalLowerBankAncestry P2HistoricalW1NativeClipping P2HistoricalW2NativeFunctional
open scoped Interval

def firstGain (δ : ℝ) (a : SourceW1) : ℝ :=
  firstFunctionalGainPsi δ (clipped a.s a.s0) a.s0 + H δ a.s0 +
  (1/2)*(∫ u in (max 2 ((a.s0:ℝ)-(a.s0:ℝ)/(a.s:ℝ)))..((a.s0:ℝ)-1),
    h δ u*firstFeedbackWeightedKernel a.s0 u)

private theorem appeared {a : SourceW1} (ha : a∈w1Original++w1Retained) :
    ∃ g, a∈sourceW1Schedule g := by
  rcases List.mem_append.mp ha with h | h
  · exact ⟨0,h⟩
  · exact ⟨56,h⟩

private theorem included (g : ℕ) {a : SourceW1} (ha : a∈sourceW1Schedule g) :
    a∈w1Original++w1Retained := by
  unfold sourceW1Schedule at ha
  split at ha
  · exact List.mem_append.mpr (Or.inl ha)
  · exact List.mem_append.mpr (Or.inr ha)

private theorem unit_domain :
    (w1Original++w1Retained).all (fun a => decide (1≤a.s ∧ a.s≤10))=true := by decide

private theorem first_eventual (k : ℕ) {δ ε : ℝ} (hd : 0<δ) (hd' : δ≤1/10) (he : 0<ε)
    {a : SourceW1} (ha : a∈w1Original++w1Retained) :
    firstGain δ a-ε ∈ wuEventualImprovements true (k+1) δ a.s := by
  obtain ⟨g,hg⟩ := appeared ha
  obtain ⟨hs,hs'⟩ := of_decide_eq_true (List.all_eq_true.mp unit_domain a ha)
  have hsR : (1 : ℝ)≤(a.s:ℝ) := by exact_mod_cast hs
  have hsR' : (a.s:ℝ)≤10 := by exact_mod_cast hs'
  have hhalf : δ<1/2 := by linarith
  have hn : firstGain δ a ≤ wuImprovementLimit true δ a.s := all_W1_functions g hg hd hd'
  exact wuEventualImprovements_downward true (k+1) (by omega) hd hhalf hsR hsR'
    (sub_le_sub_right hn ε) (wuImprovementLimit_sub_mem true k hd hhalf hsR hsR' he)

private theorem first_common (k : ℕ) (δ ε : ℝ) (xs : List SourceW1)
    (he : ∀ a∈xs, firstGain δ a-ε ∈ wuEventualImprovements true k δ a.s) :
    ∃ T, ∀ a∈xs, firstGain δ a-ε ∈ wuAdmissibleImprovements true k δ a.s T := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons a xs ih =>
    obtain ⟨A,hA⟩ := he a List.mem_cons_self
    obtain ⟨B,hB⟩ := ih (fun b hb => he b (List.mem_cons_of_mem a hb))
    refine ⟨max A B,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact wuAdmissibleImprovements_mono_threshold true _ _ _ (le_max_left _ _) hA
    · exact wuAdmissibleImprovements_mono_threshold true _ _ _ (le_max_right _ _) (hB b hb)

/-- Each scheduled native first and second comparison is on this very
same source box. The first gain is at the legal clipped target; the
ordinary parent count here is at a.s. The second keeps its switched
cost and its single joint supremum. -/
theorem common_native_source (k : ℕ) {δ ε : ℝ} (hd : 0<δ) (hd' : δ≤1/10) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ g N, T≤N → Even N → ∀ i Δ (V : Fin i → ℝ),
      wuSourceBox (k+1) δ N i Δ V →
      (∀ a∈sourceW1Schedule g, wuBoxPhi N δ (convolutionWuWindows N Δ V) a.s ≤
        (wuUpperCoefficient a.s-(firstGain δ a-ε))*
          boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      (∀ b∈taggedW2 g, 5*wuBoxPhi N δ (convolutionWuWindows N Δ V) (native b.1).s ≤
        (SecondFunctionalCoupledFeedback.cost (native b.1) δ-
          SecondFunctionalCoupledFeedback.gain (native b.1) δ+ε)*
          boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) := by
  obtain ⟨A,hA⟩ := first_common (k+1) δ ε (w1Original++w1Retained)
    (fun _ ha => first_eventual k hd hd' he ha)
  obtain ⟨B,h4,hB⟩ := all_original_mothers (k+1) (by omega) hd hd' he
  have hT : 4≤max A B := h4.trans (le_max_right _ _)
  refine ⟨max A B,hT,?_⟩
  intro g N hN hEven i Δ V hb
  constructor
  · intro a ha
    exact hA a (included g ha) N ((le_max_left _ _).trans hN) (hT.trans hN) hEven i Δ V hb
  · intro b hrow
    exact hB g b hrow N ((le_max_right _ _).trans hN) hEven i Δ V hb

end
end ImbalancedChen.P2HistoricalFunctionalCommonSource
