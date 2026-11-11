import ImbalancedChen.P3HBLogDerivativeGlobalSupport
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
P3.6 — true derivative-level restoration of the ORIGINAL three-way smooth
HB dyadic six-slot tensor. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 dyadic HB and §4 (F).
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Every finite one-coordinate logarithmic derivative commutes with the
three-way partition. The complete 3^6 ORIGINAL POSITIONAL child labels
restore the separated six-coordinate derivative tensor, before any norms.
A uniform absolute sum over all children is then paid by the same fixed
global C_K, independently of every original dyadic label.

NOT the actual mixed Frechet derivative of coupled W_T; NO integrated
mixed-L1, Fourier/Fubini, physical-rho discrepancy or full PP claim.
-/
namespace ImbalancedChen.P3HBSmoothLogTensorRestoration
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogFiniteDerivatives
open ImbalancedChen.P3HBLogDerivativeGlobalSupport

/-- Actual derivative-level restoration, not only the k=0 partition.
Pinned Mathlib iteratedDeriv_fun_sum is used on all three C∞ children. -/
theorem logChild_iteratedDeriv_sum
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (k : ℕ) (u : ℝ) :
    (∑ a : Fin 3, iteratedDeriv k (logChild chi a) u) =
      iteratedDeriv k
        (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) u := by
  have hregular : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      ContDiffAt ℝ k (logChild chi a) u := by
    intro a _
    exact (logChild_contDiff chi hchi a).contDiffAt.of_le le_top
  have hsum := (iteratedDeriv_fun_sum (I := (Finset.univ : Finset (Fin 3)))
    (f := fun a => logChild chi a) hregular)
  have heq :
      (fun v : ℝ => ∑ a : Fin 3, logChild chi a v) =
      (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) := by
    funext v
    exact logChild_sum chi v
  rw [heq] at hsum
  exact hsum.symm

/-- Six ORIGINAL positional coordinates, differentiated separately. -/
def logTensorMixed (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) : ℂ :=
  ∏ i : Fin 6, iteratedDeriv (orders i) (logChild chi (child i)) (u i)

/-- Actual dyadic labels retained literally before log chart removal. -/
def scaledTensorMixed (chi : ℝ → ℂ) (label orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) : ℂ :=
  ∏ i : Fin 6,
    iteratedDeriv (orders i)
      (fun v : ℝ => smoothCoord chi ((2 : ℝ) ^ (label i) * Real.exp v)
        (label i) (child i)) (u i)

/-- Exact elimination of dyadic labels, before taking absolute values. -/
theorem scaledTensorMixed_eq_logTensorMixed (chi : ℝ → ℂ)
    (label orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) :
    scaledTensorMixed chi label orders child u =
      logTensorMixed chi orders child u := by
  unfold scaledTensorMixed logTensorMixed
  apply Finset.prod_congr rfl
  intro i _
  exact smoothCoord_log_iteratedDeriv_exact chi (label i) (orders i)
    (child i) (u i)

/-- Restores all 729 original six-slot children, not a relabelled fibre
or substituted independent W_T. The differentiation is SEPARATED. -/
theorem logTensorMixed_children_sum (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (orders : Fin 6 → ℕ)
    (u : Fin 6 → ℝ) :
    (∑ child ∈ smoothChildren, logTensorMixed chi orders child u) =
      ∏ i : Fin 6, iteratedDeriv (orders i)
        (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) (u i) := by
  change (∑ child ∈ Finset.piFinset
      (fun _ : Fin 6 => (Finset.univ : Finset (Fin 3))),
      ∏ i : Fin 6,
        iteratedDeriv (orders i) (logChild chi (child i)) (u i)) = _
  rw [Finset.sum_prod_piFinset]
  simp_rw [logChild_iteratedDeriv_sum chi hchi]

/-- Same restoration in the LITERAL ORIGINAL dyadic child family. -/
theorem scaledTensorMixed_children_sum (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (label orders : Fin 6 → ℕ)
    (u : Fin 6 → ℝ) :
    (∑ child ∈ smoothChildren, scaledTensorMixed chi label orders child u) =
      ∏ i : Fin 6, iteratedDeriv (orders i)
        (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) (u i) := by
  simp_rw [scaledTensorMixed_eq_logTensorMixed]
  exact logTensorMixed_children_sum chi hchi orders u

/-- All derivatives of the separated tensor vanish if one coordinate
leaves the true original dyadic log window. -/
theorem logTensorMixed_zero_exterior_coordinate (chi : ℝ → ℂ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (i : Fin 6)
    (hi : u i ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    logTensorMixed chi orders child u = 0 := by
  unfold logTensorMixed
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact logChild_iteratedDeriv_zero_outside chi (child i) (orders i)
    hsmall hlarge (u i) hi

/-- Pays the absolute sum over ALL labelled children, unlike the previous
single-child bound. This is a pointwise cost, NOT Fourier L1/H. -/
theorem logTensorMixed_absolute_children_budget
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (orders : Fin 6 → ℕ) (u : Fin 6 → ℝ),
        (∀ i, orders i ≤ K) →
        (∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) ≤
          (smoothChildren.card : ℝ) * C ^ 6 := by
  obtain ⟨C, hC, hbound⟩ :=
    logChild_uniform_global_finite_order chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro orders u horders
  have hchild (child : Fin 6 → Fin 3) :
      ‖logTensorMixed chi orders child u‖ ≤ C ^ 6 := by
    calc
      ‖logTensorMixed chi orders child u‖ =
          ∏ i : Fin 6,
            ‖iteratedDeriv (orders i) (logChild chi (child i)) (u i)‖ := by
              simp [logTensorMixed, norm_prod]
      _ ≤ ∏ _i : Fin 6, C := by
          apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            exact hbound (orders i) (child i) (u i) (horders i)
      _ = C ^ 6 := by simp
  calc
    (∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖)
      ≤ ∑ child ∈ smoothChildren, C ^ 6 := by
          apply Finset.sum_le_sum
          intro child _
          exact hchild child
    _ = (smoothChildren.card : ℝ) * C ^ 6 := by simp

end ImbalancedChen.P3HBSmoothLogTensorRestoration
