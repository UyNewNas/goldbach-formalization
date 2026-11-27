import ImbalancedChen.Part3ActualBetaNativeSource
import ImbalancedChen.Part3PhysicalCommonHardFrequencyWindow
import ImbalancedChen.Part3ActualModeJointBetaPositiveCount

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 9.
U9's actual HARD common completed-m window is lifted through the ORIGINAL
signed f/u/v coefficient mass. The raw eta is exactly1 and m=0 is retained.
No residue-dependent window or smooth replacement is introduced. The
actual mode lambda/omega norms are derived from their PUBLIC original
suppliers, not from a final coefficient-L2 or target norm premise.

The physical c sum is bounded by its honest finite 10C carrier. Original
f,T,H cardinalities remain explicit, including closed endpoints and every
ordered repeated source label. This is a truncation-mass bound only; no
chart recombination, spectral budget or full 7/32 closure is asserted.
-/

namespace ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualModeBetaPositiveCountSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators

def hardCompletedKernel (M N C R : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), if c.Coprime zy.1 then
    (scaledDyadicCutoff N c : ℂ) *
      ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0

def hardSourcePiece (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N C R : ℝ) (a : ℤ) : ℂ :=
  ∑ s ∈ U, weight lambda omega s * hardCompletedKernel M N C R a (output s)

def sourceAbsMass (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℝ :=
  ∑ s ∈ U, ‖weight lambda omega s‖

theorem completedKernel_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ R : ℝ, 0 < R → ∀ N : ℝ, ∀ a : ℤ, ∀ zy : Output,
        ‖completedKernel M N C a zy - hardCompletedKernel M N C R a zy‖ ≤
          A*C^2/R^(r-1) := by
  obtain ⟨A,hA,htail⟩ := frequency_common_hard_window_tail_cap r hr
  refine ⟨100*A,by positivity,fun C hC M hM R hR N a zy => ?_⟩
  unfold completedKernel hardCompletedKernel
  rw [← Finset.sum_sub_distrib]
  have hpoint (c : ℕ) (hc : c ∈ Ioc 0 (Nat.floor (10*C))) :
      ‖(if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0) -
        (if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0)‖ ≤
        10*A*C/R^(r-1) := by
    have hcpos := (Finset.mem_Ioc.mp hc).1
    have hcap : (c : ℝ) ≤ 10*C :=
      (show (c : ℝ) ≤ (Nat.floor (10*C) : ℝ) by
        exact_mod_cast (Finset.mem_Ioc.mp hc).2).trans (Nat.floor_le (by positivity))
    by_cases hunit : c.Coprime zy.1
    · simp only [if_pos hunit,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (scaledDyadicCutoff_nonneg N c)]
      have he := htail C hC M hM R hR c hcpos hcap a zy.2 (zy.1 : ℤ)
      calc
        _ ≤ (scaledDyadicCutoff N c)*(10*A*C/R^(r-1)) :=
          mul_le_mul_of_nonneg_left he (scaledDyadicCutoff_nonneg N c)
        _ ≤ 1*(10*A*C/R^(r-1)) :=
          mul_le_mul_of_nonneg_right (scaledDyadicCutoff_le_one N c) (by positivity)
        _ = _ := one_mul _
    · simp [hunit] <;> positivity
  have hcard : ((Ioc 0 (Nat.floor (10*C))).card : ℝ) ≤ 10*C := by
    simpa only [Nat.card_Ioc,Nat.sub_zero] using (Nat.floor_le (by positivity : 0 ≤ 10*C))
  calc
    _ ≤ ∑ c ∈ Ioc 0 (Nat.floor (10*C)),
        ‖(if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0) -
          (if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
            ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ Ioc 0 (Nat.floor (10*C)), 10*A*C/R^(r-1) := Finset.sum_le_sum hpoint
    _ = ((Ioc 0 (Nat.floor (10*C))).card : ℝ)*(10*A*C/R^(r-1)) := by simp
    _ ≤ (10*C)*(10*A*C/R^(r-1)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (100*A)*C^2/R^(r-1) := by ring

/-- The signed coefficient stays inside the source before norms. -/
theorem source_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ R : ℝ, 0 < R → ∀ N : ℝ, ∀ a : ℤ,
      ∀ (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        ‖(∑ s ∈ U, weight lambda omega s * completedKernel M N C a (output s)) -
          hardSourcePiece U lambda omega M N C R a‖ ≤
            (A*C^2/R^(r-1))*sourceAbsMass U lambda omega := by
  obtain ⟨A,hA,hkernel⟩ := completedKernel_common_hard_tail r hr
  refine ⟨A,hA,fun C hC M hM R hR N a U lambda omega => ?_⟩
  unfold hardSourcePiece sourceAbsMass
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ U, ‖weight lambda omega s * completedKernel M N C a (output s) -
        weight lambda omega s * hardCompletedKernel M N C R a (output s)‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ U, ‖weight lambda omega s‖*(A*C^2/R^(r-1)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (hkernel C hC M hM R hR N a (output s)) (norm_nonneg _)
    _ = (A*C^2/R^(r-1))*(∑ s ∈ U, ‖weight lambda omega s‖) := by
      rw [Finset.sum_mul]
      ring

def rawLabelBudget (T : Finset ℕ) (H : ℕ) (F : ℝ) : ℝ :=
  ((Icc (Int.ceil (-F)) (Int.floor F)).card : ℝ) *
    (((T.card : ℝ)*((poissonNonzeroFrequencyWindow H).card : ℝ))^2)

theorem sourceAbsMass_le_rawLabelBudget
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ t ∈ T, ‖lambda t‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow H, ‖omega h‖ ≤ 1) :
    sourceAbsMass (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) lambda omega ≤
      rawLabelBudget T H F := by
  have hweight (s : Source) (hs : s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) :
      ‖weight lambda omega s‖ ≤ 1 := by
    have hr := (Finset.mem_filter.mp hs).1
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hr).2
    have h1 := Finset.mem_product.mp hp.1
    have h2 := Finset.mem_product.mp hp.2
    have hu : ‖atomCoeff lambda omega s.2.1‖ ≤ 1 := by
      rw [atomCoeff,norm_mul]
      exact (mul_le_mul (hlambda _ h1.1) (homega _ h1.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hv : ‖atomCoeff lambda omega s.2.2‖ ≤ 1 := by
      rw [atomCoeff,norm_mul]
      exact (mul_le_mul (hlambda _ h2.1) (homega _ h2.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [weight,norm_mul,norm_star]
    exact (mul_le_mul hu hv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc
    _ ≤ ∑ _s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)), (1 : ℝ) := Finset.sum_le_sum hweight
    _ = ((carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))).card : ℝ) := by simp
    _ ≤ ((rawCarrier T H (Icc (Int.ceil (-F)) (Int.floor F))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = rawLabelBudget T H F := by
      simp only [rawCarrier,finiteInnerCarrier,Finset.card_product,Nat.cast_mul,rawLabelBudget,pow_two] <;> ring

/-- All actual lambda/omega norm inputs are CONCLUSIONS of public native
suppliers. The result applies to every original mode and the SAME hard K. -/
theorem actual_completedModePiece_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g*l)], 0 < D → 0 < g → 0 < l →
      ∀ (Z : ℝ) (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)),
      ∀ M : ℝ, 0 < M → ∀ N R : ℝ, 0 < R →
      let T := baseCarrier e (D/delta)
      let H := e.sharedSmoothFrequencyBound Z D
      let F := scaleF e D g
      let lam := actualModeLambda e D delta g l mode negative u k
      let om := actualModeOmega e D g l Z tag mode negative k
      let U := carrier (g*l) (signedResidue negative e.residue) T H (Icc (Int.ceil (-F)) (Int.floor F))
      ‖completedModePiece e D delta g l Z tag mode negative u k M N -
          hardSourcePiece U lam om M N (scaleC e D g l) R (signedResidue negative e.residue)‖ ≤
        (A*(scaleC e D g l)^2/R^(r-1))*rawLabelBudget T H F := by
  obtain ⟨A,hA,hsource⟩ := source_common_hard_tail r hr
  refine ⟨A,hA,?_⟩
  intro B sigma kappa c0 e he D delta g l inst hD hg hl Z tag mode negative u k M hM N R hR
  letI : NeZero (g*l) := inst
  dsimp only
  have hC : 0 < scaleC e D g l := by
    unfold scaleC
    have hU : 0 < e.U := zero_lt_one.trans_le he.1
    have hQ2 : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
    have hQ3 : 0 < e.Q3 := zero_lt_one.trans_le he.2.2.2.2.1
    positivity
  unfold completedModePiece
  rw [completedPiece_eq_source]
  apply (hsource (scaleC e D g l) hC M hM R hR N (signedResidue negative e.residue) _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sourceAbsMass_le_rawLabelBudget
  · exact fun t ht => actualModeLambda_norm_le he D delta g l mode negative u k ht
  · exact fun h hh => actualModeOmega_norm_le e D g l Z tag mode negative k h

end
end ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
