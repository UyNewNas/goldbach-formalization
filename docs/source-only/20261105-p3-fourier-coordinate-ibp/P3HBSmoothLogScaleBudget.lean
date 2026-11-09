import ImbalancedChen.P3HBSmoothThreeWayRatioTwo
import Mathlib.Tactic

/-!
P3.6 — exact chart-scale removal and fixed absolute cost for the genuine
smooth three-way HB child, on the frozen manuscript's original dyadic scale.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (original dyadic psi and six HB slots), §4 (F).
Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

All identities keep the original complex-valued cutoff and the SAME
original six labelled HB slots. No new distribution theorem, extra premise of PP,
source compiler, physical modulus or rho is introduced.
The optional |chi|<=1 premise is an ordinary cutoff-amplitude condition,
NOT an assumption about PP or the target discrepancy. Its verification
for the selected cutoff is still a separate obligation.
-/
namespace ImbalancedChen.P3HBSmoothLogScaleBudget
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBDyadicTensorPartition

/-- The universal logarithmic-chart template. It contains NO dyadic
scale index and uses exactly the prior genuine three-way child gates. -/
def logChild (chi : ℝ → ℂ) (a : Fin 3) (u : ℝ) : ℂ :=
  (chi (Real.exp u) - chi (2 * Real.exp u)) *
    smoothGate chi (Real.exp u) a

/-- One actual dyadic child, charted at x=2^j*exp(u), is literally
one of three fixed templates. Thus the number of dyadic labels cannot
by itself increase any fixed-order log-coordinate derivative norm. -/
theorem smoothCoord_log_exact (chi : ℝ → ℂ)
    (j : ℕ) (a : Fin 3) (u : ℝ) :
    smoothCoord chi ((2 : ℝ) ^ j * Real.exp u) j a =
      logChild chi a u := by
  have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hdiv : ((2 : ℝ) ^ j * Real.exp u) / (2 : ℝ) ^ j =
      Real.exp u := by field_simp
  have hdouble : (2 * ((2 : ℝ) ^ j * Real.exp u)) /
      (2 : ℝ) ^ j = 2 * Real.exp u := by
    field_simp
  simp only [smoothCoord, dyadicPiece, logChild, hdiv, hdouble]

/-- Actual log-chart smoothness at ALL finite orders, uniformly in j
because the charted functions are extensionally identical. -/
theorem logChild_contDiff (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (a : Fin 3) :
    ContDiff ℝ ⊤ (logChild chi a) := by
  have he : ContDiff ℝ ⊤ (fun u : ℝ => Real.exp u) := by fun_prop
  have he2 : ContDiff ℝ ⊤ (fun u : ℝ => 2 * Real.exp u) := by fun_prop
  have hp : ContDiff ℝ ⊤
      (fun u : ℝ => chi (Real.exp u) - chi (2 * Real.exp u)) :=
    (hchi.comp he).sub (hchi.comp he2)
  exact hp.mul ((smoothGate_contDiff chi hchi a).comp he)

theorem smoothCoord_log_contDiff (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (j : ℕ) (a : Fin 3) :
    ContDiff ℝ ⊤ (fun u : ℝ =>
      smoothCoord chi ((2 : ℝ) ^ j * Real.exp u) j a) := by
  have heq : (fun u : ℝ =>
      smoothCoord chi ((2 : ℝ) ^ j * Real.exp u) j a) =
      logChild chi a := by
    funext u
    exact smoothCoord_log_exact chi j a u
  rw [heq]
  exact logChild_contDiff chi hchi a

/-- Exact first log-coordinate derivative invariance, with no
frequency-dependent constant and no appeal to a Fourier theorem. -/
theorem smoothCoord_log_deriv (chi : ℝ → ℂ)
    (j : ℕ) (a : Fin 3) (u : ℝ) :
    deriv (fun s : ℝ =>
      smoothCoord chi ((2 : ℝ) ^ j * Real.exp s) j a) u =
      deriv (logChild chi a) u := by
  have heq : (fun s : ℝ =>
      smoothCoord chi ((2 : ℝ) ^ j * Real.exp s) j a) =
      logChild chi a := by
    funext s
    exact smoothCoord_log_exact chi j a s
  rw [heq]

/-- The same three fixed templates recover the original true charted
cutoff BEFORE absolute values and any physical rho/Q discrepancy. -/
theorem logChild_sum (chi : ℝ → ℂ) (u : ℝ) :
    (∑ a : Fin 3, logChild chi a u) =
      chi (Real.exp u) - chi (2 * Real.exp u) := by
  simp [logChild, ← Finset.mul_sum, smoothGate_sum]

/-- The genuine fixed template is zero below the original rough dyadic
support. The equality holds at the endpoint 2*exp(u)=1. -/
theorem logChild_zero_small (chi : ℝ → ℂ) (a : Fin 3) (u : ℝ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hu : 2 * Real.exp u ≤ 1) : logChild chi a u = 0 := by
  have h : Real.exp u ≤ 1 := by linarith
  simp [logChild, hsmall _ h, hsmall _ hu]

/-- Likewise at and above exp(u)=2. There is no new cutoff at the
seams of the three overlapping smooth subintervals. -/
theorem logChild_zero_large (chi : ℝ → ℂ) (a : Fin 3) (u : ℝ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hu : 2 ≤ Real.exp u) : logChild chi a u = 0 := by
  have h : 2 ≤ 2 * Real.exp u := by linarith
  simp [logChild, hlarge _ hu, hlarge _ h]

/-- A concrete, target-independent bound on each smooth gate; avoids
assuming positivity/monotonicity of a complex-valued cutoff. -/
theorem smoothGate_norm_le_two (chi : ℝ → ℂ)
    (hchi : ∀ t : ℝ, ‖chi t‖ ≤ 1) (t : ℝ) (a : Fin 3) :
    ‖smoothGate chi t a‖ ≤ 2 := by
  fin_cases a
  · simpa [smoothGate] using
      (le_trans (hchi (4 * t - 2)) (by norm_num : (1 : ℝ) ≤ 2))
  · have hs := norm_sub_le (chi (4 * t - 3)) (chi (4 * t - 2))
    have h1 := hchi (4 * t - 3)
    have h2 := hchi (4 * t - 2)
    simpa [smoothGate] using (show
      ‖chi (4 * t - 3) - chi (4 * t - 2)‖ ≤ 2 by linarith)
  · have hs := norm_sub_le (1 : ℂ) (chi (4 * t - 3))
    have h2 := hchi (4 * t - 3)
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    simpa [smoothGate] using (show
      ‖(1 : ℂ) - chi (4 * t - 3)‖ ≤ 2 by linarith)

/-- The three-way refinement has a finite absolute loss per child,
uniform in the dyadic scale. This is a zero-order bound, not a
quantitative estimate for derivatives of every physical W_T. -/
theorem smoothCoord_norm_le_two (chi : ℝ → ℂ)
    (hchi : ∀ t : ℝ, ‖chi t‖ ≤ 1)
    (x : ℝ) (j : ℕ) (a : Fin 3) :
    ‖smoothCoord chi x j a‖ ≤ 2 * ‖dyadicPiece chi x j‖ := by
  rw [smoothCoord, norm_mul]
  have hb := smoothGate_norm_le_two chi hchi (x / (2 : ℝ) ^ j) a
  have hnon : 0 ≤ ‖dyadicPiece chi x j‖ := norm_nonneg _
  nlinarith

/-- A single actual six-position original HB smooth child pays only a
fixed universal zero-order factor 2^6=64 relative to its ORIGINAL
dyadic tensor. This does not use a bound on a physical modulus, rho, or
complete-product shift. It does NOT establish derivative Fourier budgets. -/
theorem smoothTensor_norm_le_sixtyfour (chi : ℝ → ℂ)
    (hchi : ∀ t : ℝ, ‖chi t‖ ≤ 1)
    (label : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (marked hb : List ℕ) :
    ‖smoothTensor chi label child marked hb‖ ≤
      64 * ‖hbDyadicCut chi label marked hb‖ := by
  have hf (i : Fin 6) :
      ‖smoothCoord chi (((hb.getD i.val 1 : ℕ) : ℝ))
          (label i) (child i)‖ ≤
        2 * ‖dyadicPiece chi (((hb.getD i.val 1 : ℕ) : ℝ))
          (label i)‖ :=
    smoothCoord_norm_le_two chi hchi _ _ _
  calc
    ‖smoothTensor chi label child marked hb‖ =
        ∏ i : Fin 6,
          ‖smoothCoord chi (((hb.getD i.val 1 : ℕ) : ℝ))
            (label i) (child i)‖ := by
          simp [smoothTensor, norm_prod]
    _ ≤ ∏ i : Fin 6,
          (2 * ‖dyadicPiece chi (((hb.getD i.val 1 : ℕ) : ℝ))
            (label i)‖) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact norm_nonneg _
          · intro i hi
            exact hf i
    _ = 64 * ‖hbDyadicCut chi label marked hb‖ := by
          simp [hbDyadicCut, norm_prod, Finset.prod_mul_distrib]

end ImbalancedChen.P3HBSmoothLogScaleBudget
