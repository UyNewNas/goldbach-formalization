import ImbalancedChen.P2SeedOmegaUnitChartIdentification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Finite original unit COUNTS reach the manuscript's actual first/last
eliminated real masses. One common threshold supports the two separate
epsilon/2 errors and their epsilon combined error. Alpha stays the actual
omega3XPhi of EACH mark; the real N/(d log R) normalization stays literal.

Scope is the pinned positive convolution source family and its SAME
Q=N^(1/2-delta). This does not assert an arbitrary signed/marked-family
receiver, does not replace the given sigma by independent beta, and does
not assert the generalized current-Q positive-product/AP input.
-/

namespace ImbalancedChen.P2SeedOmegaActualUnitCountReceiver
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators
open Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open P2SeedOmegaLastUnitIntegrals
open P2SeedOmegaUnitChartIdentification

def sameQUnitMain20 {i : ℕ} (N : ℕ) (delta : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (N : ℝ)*∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ)/
      ((d : ℝ)*Real.log ((N : ℝ)^(1/2-delta)/d))*unit20Mass (omega3XPhi N d delta)

def sameQUnitMain21 {i : ℕ} (N : ℕ) (delta : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (N : ℝ)*∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ)/
      ((d : ℝ)*Real.log ((N : ℝ)^(1/2-delta)/d))*unit21Mass (omega3XPhi N d delta)

/-- This identification includes the nontrivial affine first/last chart
change for20. Both sides keep the same real descendant parameter. -/
theorem sameQUnitMain20_eq_boxed {i : ℕ} (N : ℕ) (delta : ℝ) (W : Fin i → Finset ℕ) :
    sameQUnitMain20 N delta W=
      HighUnit.boxedIntegral20 N delta W (fun _ => a2) (fun _ => a3) (fun _ => b) := by
  unfold sameQUnitMain20 HighUnit.boxedIntegral20
  simp_rw [unit20Mass_eq_pinned_J20]

theorem sameQUnitMain21_eq_boxed {i : ℕ} (N : ℕ) (delta : ℝ) (W : Fin i → Finset ℕ) :
    sameQUnitMain21 N delta W=
      HighUnit.boxedIntegral21 N delta W (fun _ => a3) (fun _ => b) := by
  unfold sameQUnitMain21 HighUnit.boxedIntegral21
  simp_rw [unit21Mass_eq_pinned_J21]

/-- Actual fixed positive source boxes choose one threshold BEFORE N,
the marked window family and its local cutoffs. Unit counts remain two
separate terms; their total error is explicitly paid once. -/
theorem actual_unit_counts_receiver (k : ℕ) {delta epsilon : ℝ}
    (hd : 0<delta) (hdhi : delta<1/2) (he : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N →
      ∀ (i : ℕ) (Delta : ℝ) (V : Fin i → ℝ),wuSourceBox k delta N i Delta V →
      let W := convolutionWuWindows N Delta V
      (HighUnitSource.unit20 N delta W (fun _ => a0) (fun _ => a1)
          (fun _ => a2) (fun _ => a3) (fun _ => b)≤sameQUnitMain20 N delta W+
        (epsilon/2)*((N : ℝ)/Real.log N)*boxConvolutionReciprocalMass W) ∧
      (HighUnitSource.unit21 N delta W (fun _ => a0) (fun _ => a1)
          (fun _ => a2) (fun _ => a3) (fun _ => b)≤sameQUnitMain21 N delta W+
        (epsilon/2)*((N : ℝ)/Real.log N)*boxConvolutionReciprocalMass W) ∧
      (HighUnitSource.unit20 N delta W (fun _ => a0) (fun _ => a1)
          (fun _ => a2) (fun _ => a3) (fun _ => b)+
        HighUnitSource.unit21 N delta W (fun _ => a0) (fun _ => a1)
          (fun _ => a2) (fun _ => a3) (fun _ => b)≤
        sameQUnitMain20 N delta W+sameQUnitMain21 N delta W+
        epsilon*((N : ℝ)/Real.log N)*boxConvolutionReciprocalMass W) := by
  obtain ⟨T,hT,hrec⟩ := HighUnitSource.source_pair_integral k hd hdhi he
  refine ⟨T,hT,?_⟩
  intro N hN i Delta V hbox
  have h := hrec N hN i Delta V hbox (fun _ => a0) (fun _ => a1)
    (fun _ => a2) (fun _ => a3) (fun _ => b)
    (fun _ _ => by norm_num [a2,a3,b])
  dsimp only at h ⊢
  rw [← sameQUnitMain20_eq_boxed,← sameQUnitMain21_eq_boxed] at h
  exact h

end
end ImbalancedChen.P2SeedOmegaActualUnitCountReceiver
