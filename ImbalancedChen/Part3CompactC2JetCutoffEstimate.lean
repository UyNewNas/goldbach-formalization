import ImbalancedChen.Part3CompactC2FiniteTensorApproximation
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
A proved six-jet multiplier estimate for actual compact smooth cutoffs.
This is used to localize the already constructed finite tensor approximants
without assuming support-preserving density or any Gamma graph assertion.
-/

noncomputable section
namespace ImbalancedChen.Part3.CompactC2JetCutoffEstimate20261026a

open Set
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a

def jetX : JetIndex := ⟨(1, 0), by norm_num⟩
def jetY : JetIndex := ⟨(0, 1), by norm_num⟩
def jetXY : JetIndex := ⟨(1, 1), by norm_num⟩

theorem directional_add (v : Plane) {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    directional v (F + G) = directional v F + directional v G := by
  funext p
  simp only [directional, fderiv_add (hF.differentiable (by simp) p)
    (hG.differentiable (by simp) p), ContinuousLinearMap.add_apply, Pi.add_apply]

theorem directional_sub (v : Plane) {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    directional v (F - G) = directional v F - directional v G := by
  funext p
  simp only [directional, fderiv_sub (hF.differentiable (by simp) p)
    (hG.differentiable (by simp) p), ContinuousLinearMap.sub_apply, Pi.sub_apply]

theorem directionalIter_sub (v : Plane) (n : ℕ) {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    directionalIter v n (F - G) = directionalIter v n F - directionalIter v n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change directional v (directionalIter v n (F - G)) = _
      rw [ih]
      exact directional_sub v (directionalIter_smooth v n hF) (directionalIter_smooth v n hG)

theorem mixedJet_sub {F G : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (ij : JetIndex) :
    mixedJet (F - G) ij = mixedJet F ij - mixedJet G ij := by
  unfold mixedJet
  rw [directionalIter_sub ey _ hF hG]
  exact directionalIter_sub ex _ (directionalIter_smooth ey _ hF) (directionalIter_smooth ey _ hG)

theorem directional_mul (v : Plane) {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    directional v (fun p => F p * G p) =
      fun p => directional v F p * G p + F p * directional v G p := by
  funext p
  simp only [directional, fderiv_fun_mul (hF.differentiable (by simp) p)
    (hG.differentiable (by simp) p), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem directional_twice_mul (v w : Plane) {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    directional v (directional w (fun p => F p * G p)) = fun p =>
      directional v (directional w F) p * G p +
      directional w F p * directional v G p +
      directional v F p * directional w G p +
      F p * directional v (directional w G) p := by
  rw [directional_mul w hF hG]
  have heq : (fun p => directional w F p * G p + F p * directional w G p) =
      (fun p => directional w F p * G p) + (fun p => F p * directional w G p) := rfl
  rw [heq, directional_add v ((directional_smooth w hF).mul hG)
    (hF.mul (directional_smooth w hG)),
    directional_mul v (directional_smooth w hF) hG,
    directional_mul v hF (directional_smooth w hG)]
  funext p
  simp only [Pi.add_apply]
  ring

private theorem norm_product_le {a b : ℂ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ δ) :
    ‖a * b‖ ≤ M * δ :=
  (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg _) hM)

private theorem norm_two_products_le {a b c d : ℂ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ δ)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ δ) : ‖a * b + c * d‖ ≤ 2 * M * δ := by
  calc
    _ ≤ ‖a * b‖ + ‖c * d‖ := norm_add_le _ _
    _ ≤ M * δ + M * δ := add_le_add (norm_product_le hM hδ ha hb)
      (norm_product_le hM hδ hc hd)
    _ = _ := by ring

private theorem norm_four_products_le {a b c d e f g h : ℂ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ δ)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ δ) (he : ‖e‖ ≤ M) (hf : ‖f‖ ≤ δ)
    (hg : ‖g‖ ≤ M) (hh : ‖h‖ ≤ δ) :
    ‖a * b + c * d + e * f + g * h‖ ≤ 4 * M * δ := by
  calc
    _ = ‖(a * b + c * d) + (e * f + g * h)‖ := by congr 1 <;> ring
    _ ≤ ‖a * b + c * d‖ + ‖e * f + g * h‖ := norm_add_le _ _
    _ ≤ 2 * M * δ + 2 * M * δ := add_le_add (norm_two_products_le hM hδ ha hb hc hd)
      (norm_two_products_le hM hδ he hf hg hh)
    _ = _ := by ring

/-- Actual two-derivative Leibniz rule gives a quantitative shared-jet
bound; the cutoff coefficient 4*M is paid BEFORE choosing the tolerance. -/
theorem mixedJet_mul_norm_le {C E : Plane → ℂ}
    (hC : ContDiff ℝ ∞ C) (hE : ContDiff ℝ ∞ E) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hCM : ∀ p ij, ‖mixedJet C ij p‖ ≤ M)
    (hEM : ∀ p ij, ‖mixedJet E ij p‖ ≤ δ) (p : Plane) (ij : JetIndex) :
    ‖mixedJet (fun q => C q * E q) ij p‖ ≤ 4 * M * δ := by
  have h0C : ‖C p‖ ≤ M := hCM p jet00
  have h0E : ‖E p‖ ≤ δ := hEM p jet00
  have hfirst (v : Plane) (hvC : ‖directional v C p‖ ≤ M)
      (hvE : ‖directional v E p‖ ≤ δ) :
      ‖directional v (fun q => C q * E q) p‖ ≤ 4 * M * δ := by
    rw [directional_mul v hC hE]
    exact (norm_two_products_le hM hδ hvC h0E h0C hvE).trans (by nlinarith [mul_nonneg hM hδ])
  have hsecond (v w : Plane) (hvwC : ‖directional v (directional w C) p‖ ≤ M)
      (hwC : ‖directional w C p‖ ≤ M) (hvC : ‖directional v C p‖ ≤ M)
      (hvwE : ‖directional v (directional w E) p‖ ≤ δ)
      (hwE : ‖directional w E p‖ ≤ δ) (hvE : ‖directional v E p‖ ≤ δ) :
      ‖directional v (directional w (fun q => C q * E q)) p‖ ≤ 4 * M * δ := by
    rw [directional_twice_mul v w hC hE]
    exact norm_four_products_le hM hδ hvwC h0E hwC hvE hvC hwE h0C hvwE
  rcases ij with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact (norm_product_le hM hδ h0C h0E).trans (by nlinarith [mul_nonneg hM hδ])
  · exact hfirst ey (hCM p jetY) (hEM p jetY)
  · exact hsecond ey ey (hCM p jetYY) (hCM p jetY) (hCM p jetY)
      (hEM p jetYY) (hEM p jetY) (hEM p jetY)
  · exact hfirst ex (hCM p jetX) (hEM p jetX)
  · exact hsecond ex ey (hCM p jetXY) (hCM p jetY) (hCM p jetX)
      (hEM p jetXY) (hEM p jetY) (hEM p jetX)
  · norm_num at hij
  · exact hsecond ex ex (hCM p jetXX) (hCM p jetX) (hCM p jetX)
      (hEM p jetXX) (hEM p jetX) (hEM p jetX)
  · norm_num at hij
  · norm_num at hij

/-- Compactness genuinely PRODUCES a finite global bound for every cutoff
jet, rather than receiving a cutoff multiplier bound as a premise. -/
theorem exists_global_jet_bound {C : Plane → ℂ} (hC : ContDiff ℝ ∞ C)
    (hc : HasCompactSupport C) : ∃ M : ℝ, 1 ≤ M ∧ ∀ p ij, ‖mixedJet C ij p‖ ≤ M := by
  have hjc : HasCompactSupport (jetVector C) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport C)
    intro p hp
    by_contra hout
    apply hp
    funext ij
    have hz : partialJet ij C p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hout (partialJet_tsupport_subset hC ij h))
    simpa only [jetVector, partialJet_eq_mixedJet hC] using hz
  obtain ⟨M0, hM0⟩ := (jetVector_continuous hC).bounded_above_of_compact_support hjc
  refine ⟨max 1 M0, le_max_left _ _, ?_⟩
  intro p ij
  exact (norm_le_pi_norm (jetVector C p) ij).trans ((hM0 p).trans (le_max_right _ _))

end ImbalancedChen.Part3.CompactC2JetCutoffEstimate20261026a