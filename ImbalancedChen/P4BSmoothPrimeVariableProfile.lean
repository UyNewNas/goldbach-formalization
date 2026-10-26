import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp
import ImbalancedChen.P4BSmoothProfileCommonCompactSupport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Genuine smooth pullback to positive continuous prime variables

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

Future normal imports refer to sibling source-only modules. The variable
here is a genuine positive real pair p=(r,q), and logarithms vary with p.
The discrete actual prime-tuple weight is its evaluation, not a separate
smoothness assertion about a finite set. The common compact normalized-log
profile module supplies support geometry; no compactness proof is repeated.
The Jacobian and the full fderiv chain rule are exact. No uniform derivative
constant or Part 3 licence is inferred from qualitative smoothness.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BSmoothProfileCommonCompactSupport

def positivePrimeOrthant : Set (Fin 2 → ℝ) := {p | ∀ i, 0 < p i}

def primeVariableLogPoint (N : ℕ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => Real.log (p i) / Real.log (N : ℝ)

def smoothPrimeVariableProfile (b : ℝ) (N : ℕ) (T width : ℝ)
    (p : Fin 2 → ℝ) : ℝ :=
  smoothPhysicalProfile b N T width (primeVariableLogPoint N p)

def primeTuplePoint (N : ℕ) (t : Fin 2 → Fin (N + 1)) : Fin 2 → ℝ :=
  fun i => ((t i).val : ℝ)

/-- Every genuine labelled prime tuple evaluates inside the positive
continuous domain, including repeated-prime tuples. -/
theorem primeTuplePoint_mem_positivePrimeOrthant {N : ℕ}
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    primeTuplePoint N t ∈ positivePrimeOrthant := by
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  intro i
  exact_mod_cast (hp i).pos

theorem smoothPhysicalPairOuterRamp_eq_primeVariableProfile (b : ℝ) (N : ℕ)
    (T width : ℝ) (t : Fin 2 → Fin (N + 1)) :
    smoothPhysicalPairOuterRamp b N T width t =
      smoothPrimeVariableProfile b N T width (primeTuplePoint N t) := by
  rfl

/-- The actual coordinate-log map is smooth on the positive orthant at
every finite or infinite order. The denominator is a fixed parameter. -/
theorem contDiffOn_primeVariableLogPoint (N : ℕ) {n : ℕ∞} :
    ContDiffOn ℝ n (primeVariableLogPoint N) positivePrimeOrthant := by
  apply contDiffOn_pi.mpr
  intro i
  have hcoord : ContDiffOn ℝ n (fun p : Fin 2 → ℝ => p i)
      positivePrimeOrthant := (contDiff_apply ℝ ℝ i).contDiffOn
  have hlog : ContDiffOn ℝ n (fun p : Fin 2 → ℝ => Real.log (p i))
      positivePrimeOrthant := Real.contDiffOn_log.comp hcoord (by
        intro p hp
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (hp i).ne')
  exact hlog.div_const (Real.log (N : ℝ))

/-- Actual C-infinity prime-variable pullback on its positive domain.
N>=2 is not needed merely for this regularity statement: totalized
division by the fixed log N remains a constant operation. -/
theorem contDiffOn_smoothPrimeVariableProfile (b : ℝ) (N : ℕ) (T width : ℝ)
    {n : ℕ∞} :
    ContDiffOn ℝ n (smoothPrimeVariableProfile b N T width) positivePrimeOrthant := by
  exact (contDiff_smoothPhysicalProfile b N T width).comp_contDiffOn
    (contDiffOn_primeVariableLogPoint N)

/-- Exact scalar logarithmic coordinate derivative. -/
theorem hasDerivAt_normalizedPrimeLog (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => Real.log x / Real.log (N : ℝ))
      (u⁻¹ / Real.log (N : ℝ)) u := by
  exact (Real.hasDerivAt_log hu.ne').div_const (Real.log (N : ℝ))

/-- The genuine diagonal log-coordinate Jacobian, retaining its exact
N and p dependence rather than inventing a uniform constant. -/
def primeVariableLogJacobian (N : ℕ) (p : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    (Real.log (N : ℝ))⁻¹ • ((p i)⁻¹ • ContinuousLinearMap.proj i))

theorem primeVariableLogJacobian_apply (N : ℕ) (p h : Fin 2 → ℝ) (i : Fin 2) :
    primeVariableLogJacobian N p h i = h i / (p i * Real.log (N : ℝ)) := by
  simp [primeVariableLogJacobian, div_eq_mul_inv, mul_inv_rev]
  <;> ring

theorem hasFDerivAt_primeVariableLogPoint (N : ℕ) {p : Fin 2 → ℝ}
    (hp : p ∈ positivePrimeOrthant) :
    HasFDerivAt (primeVariableLogPoint N) (primeVariableLogJacobian N p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hlog := (hasFDerivAt_apply (𝕜 := ℝ) i p).log (hp i).ne'
  simpa only [div_eq_mul_inv, mul_comm] using
    hlog.const_mul (Real.log (N : ℝ))⁻¹

/-- Exact continuous-prime-variable chain rule for the full genuine
profile. All N, width and variable dependence is visible in the Jacobian. -/
theorem fderiv_smoothPrimeVariableProfile (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) :
    fderiv ℝ (smoothPrimeVariableProfile b N T width) p =
      (fderiv ℝ (smoothPhysicalProfile b N T width) (primeVariableLogPoint N p)).comp
        (primeVariableLogJacobian N p) := by
  have hprofile : DifferentiableAt ℝ (smoothPhysicalProfile b N T width)
      (primeVariableLogPoint N p) :=
    ((contDiff_smoothPhysicalProfile (n := 1) b N T width).differentiable
      (by norm_num)).differentiableAt
  have hlog := hasFDerivAt_primeVariableLogPoint N hp
  change fderiv ℝ ((smoothPhysicalProfile b N T width) ∘ primeVariableLogPoint N) p = _
  rw [fderiv_comp hprofile hlog.differentiableAt, hlog.fderiv]

/-- The continuous upper physical margin is precisely the physical
logarithmic product gap, now for real positive prime variables. -/
theorem primeVariable_upper_margin_eq_log_gap (b T : ℝ) {N : ℕ}
    (hN : (1 : ℝ) < N) (p : Fin 2 → ℝ) :
    smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) 3 =
      Real.log (N : ℝ) - Real.log (p 0) - Real.log (p 1) := by
  change Real.log (N : ℝ) *
    (1 - Real.log (p 0) / Real.log (N : ℝ) -
      Real.log (p 1) / Real.log (N : ℝ)) = _
  field_simp [ne_of_gt (Real.log_pos hN)] <;> ring

/-- Nonzero actual continuous weight has the same strict physical
product cap as the discrete tuple weight. -/
theorem smoothPrimeVariableProfile_nonzero_product_lt_exp_mul_N
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hwidth : 0 < width)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (hnonzero : smoothPrimeVariableProfile b N T width p ≠ 0) :
    p 0 * p 1 < Real.exp width * (N : ℝ) := by
  have hgap := smoothPhysicalProfile_nonzero_margin_support hwidth hnonzero 3
  rw [primeVariable_upper_margin_eq_log_gap b T hN p] at hgap
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN
  apply (Real.log_lt_log_iff (mul_pos (hp 0) (hp 1))
    (mul_pos (Real.exp_pos width) hNpos)).mp
  rw [Real.log_mul (hp 0).ne' (hp 1).ne',
    Real.log_mul (Real.exp_pos width).ne' hNpos.ne', Real.log_exp]
  linarith only [hgap]

/-- The common normalized-coordinate support gives genuine rpow lower
support in positive prime variables. This reuses the common profile's
theta geometry and does not repeat or assume its compactness proof. -/
theorem smoothPrimeVariableProfile_nonzero_above_rpow
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (htheta : 0 < theta)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ P4BOuterRampRoughness.baseline b kappa - theta)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (hnonzero : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
      width p ≠ 0) :
    ∀ i : Fin 2, (N : ℝ) ^ theta < p i := by
  have hcoordinates := smoothPhysicalProfile_nonzero_coordinates_bounds
    hb htheta hN hwidth hgap hnonzero
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  intro i
  have hcoord := (hcoordinates i).1
  change theta < Real.log (p i) / Real.log (N : ℝ) at hcoord
  have hscaled := (lt_div_iff₀ (Real.log_pos hN1)).mp hcoord
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNpos theta) (hp i)).mp
  rw [Real.log_rpow hNpos theta]
  exact hscaled

end

end ImbalancedChen.P4B
