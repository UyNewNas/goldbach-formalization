import ImbalancedChen.Part3ActualMaassFourierODE
import ImbalancedChen.Part3ActualFourierBesselConjugation
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual zero Fourier coefficient: native physical initial-data uniqueness

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal n=0 coefficient of the original periodic C2 Maass PDE obeys
c''=-(1/4+tau^2)y^(-2)c on y>0. On any interval separated from zero,
its native first-order state field is uniformly Lipschitz, with constant
1+(1/4+tau^2)/A^2. Actual ODE uniqueness globalizes physical value and
height-derivative data throughout y>0. All real tau including zero are
covered; there is no nonzero-frequency scaling, L2 premise, K mode,
Hardy inequality, or held canonical-selection dependency.
-/

namespace ImbalancedChen.Part3.ActualZeroFourierInitialData20261026b

noncomputable section
open Set
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a

private def physicalPotential (tau y : ℝ) : ℝ := -(1/4+tau^2)/y^2

private def ZeroSolution (tau : ℝ) (c : ℝ → ℂ) : Prop :=
  ∀ y : ℝ, 0 < y → HasDerivAt c (deriv c y) y ∧
    HasDerivAt (deriv c) ((physicalPotential tau y : ℂ)*c y) y

/-- The original PDE supplies the actual native physical zero-mode ODE,
without a coefficient regularity or coefficient equation premise. -/
private theorem actual_zero_solution {u : ℝ × ℝ → ℂ} {tau : ℝ}
    (hu : ContDiffOn ℝ 2 u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x+1,y)=u(x,y))
    (hPDE : ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p) =
        ((1/4+tau^2 : ℝ) : ℂ)*u p) : ZeroSolution tau (coefficient u 0) := by
  intro y hy
  have hc := coefficient_contDiffOn_two hu (0 : ℤ)
  have hODE := actual_coefficient_maass_ode hu hp ((1/4+tau^2 : ℝ) : ℂ) hPDE (0 : ℤ) hy
  simp only [Int.cast_zero,mul_zero,Complex.ofReal_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul,sub_zero] at hODE
  have hEq : deriv (deriv (coefficient u 0)) y =
      (physicalPotential tau y : ℂ)*coefficient u 0 y := by
    have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    unfold physicalPotential
    push_cast
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero 2 hyC)).mpr
    linear_combination -hODE
  refine ⟨native_first hc hy,?_⟩
  simpa only [hEq] using native_second hc hy

private def state (c : ℝ → ℂ) (y : ℝ) : ℂ × ℂ := (c y,deriv c y)
private def field (tau y : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (z.2,(physicalPotential tau y : ℂ)*z.1)
private def boundConstant (tau A : ℝ) : ℝ≥0 :=
  ⟨1+(1/4+tau^2)/A^2,by positivity⟩

private theorem potential_bound {tau A y : ℝ} (hA : 0 < A) (hy : A < y) :
    |physicalPotential tau y| ≤ (boundConstant tau A : ℝ) := by
  have hLambda : 0 ≤ (1/4+tau^2 : ℝ) := by positivity
  have hpow : A^2 ≤ y^2 := by nlinarith
  calc
    _ = (1/4+tau^2)/y^2 := by
      simp only [physicalPotential,abs_div,abs_neg,
        abs_of_nonneg hLambda,abs_of_nonneg (sq_nonneg y)]
    _ ≤ (1/4+tau^2)/A^2 :=
      div_le_div_of_nonneg_left hLambda (sq_pos_of_pos hA) hpow
    _ ≤ _ := by dsimp [boundConstant]; linarith

private theorem field_lipschitz {tau A y : ℝ} (hA : 0 < A) (hy : A < y) :
    LipschitzWith (boundConstant tau A) (field tau y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have hK : 1 ≤ (boundConstant tau A : ℝ) := by
    dsimp [boundConstant]
    have hnonneg : 0 ≤ (1/4+tau^2)/A^2 := by positivity
    linarith
  have hfst : dist x.2 z.2 ≤ (boundConstant tau A : ℝ)*dist x z := by
    have hpart : dist x.2 z.2 ≤ dist x z := by rw [Prod.dist_eq]; exact le_max_right _ _
    nlinarith [dist_nonneg x z]
  have hsnd : dist ((physicalPotential tau y : ℂ)*x.1)
      ((physicalPotential tau y : ℂ)*z.1) ≤ (boundConstant tau A : ℝ)*dist x z := by
    rw [dist_eq_norm,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul (potential_bound hA hy) ?_ (norm_nonneg _) (by positivity)
    rw [← dist_eq_norm,Prod.dist_eq]
    exact le_max_left _ _
  change max (dist x.2 z.2)
    (dist ((physicalPotential tau y : ℂ)*x.1) ((physicalPotential tau y : ℂ)*z.1)) ≤ _
  exact max_le hfst hsnd

private theorem zero_initial_unique {tau y0 : ℝ} {c d : ℝ → ℂ}
    (hc : ZeroSolution tau c) (hd : ZeroSolution tau d) (hy0 : 0 < y0)
    (hval : c y0=d y0) (hderiv : deriv c y0=deriv d y0) :
    EqOn c d (Ioi (0 : ℝ)) := by
  intro y hy
  let A := min y0 y/2
  let B := max y0 y+1
  have hmin : 0 < min y0 y := lt_min hy0 hy
  have hA : 0 < A := half_pos hmin
  have hy0A : A < y0 := by dsimp [A]; linarith [min_le_left y0 y]
  have hyA : A < y := by dsimp [A]; linarith [min_le_right y0 y]
  have hy0B : y0 < B := by dsimp [B]; linarith [le_max_left y0 y]
  have hyB : y < B := by dsimp [B]; linarith [le_max_right y0 y]
  have hEq : EqOn (state c) (state d) (Ioo A B) := by
    apply ODE_solution_unique_of_mem_Ioo (v := field tau) (s := fun _ => univ)
      (K := boundConstant tau A) (t₀ := y0)
    · intro t ht
      exact (field_lipschitz hA ht.1).lipschitzOnWith
    · exact ⟨hy0A,hy0B⟩
    · intro t ht
      have ht0 := hA.trans ht.1
      exact ⟨(hc t ht0).1.prodMk (hc t ht0).2,mem_univ _⟩
    · intro t ht
      have ht0 := hA.trans ht.1
      exact ⟨(hd t ht0).1.prodMk (hd t ht0).2,mem_univ _⟩
    · exact Prod.ext hval hderiv
  exact congrArg Prod.fst (hEq ⟨hyA,hyB⟩)

/-- Physical zero-frequency initial-data uniqueness for actual periodic
C2 Maass functions. This is the missing zero leaf needed alongside
signed nonzero Fourier coefficient initial-data uniqueness. -/
theorem actual_zero_coefficient_initial_data_unique
    {u v : ℝ × ℝ → ℂ} {tau y0 : ℝ}
    (hu : ContDiffOn ℝ 2 u upperDomain) (hv : ContDiffOn ℝ 2 v upperDomain)
    (hpu : ∀ x y : ℝ, 0 < y → u (x+1,y)=u(x,y))
    (hpv : ∀ x y : ℝ, 0 < y → v (x+1,y)=v(x,y))
    (hPDEu : ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p) =
        ((1/4+tau^2 : ℝ) : ℂ)*u p)
    (hPDEv : ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2*(partialX (partialX v) p+partialY (partialY v) p) =
        ((1/4+tau^2 : ℝ) : ℂ)*v p)
    (hy0 : 0 < y0)
    (hvalue : coefficient u 0 y0=coefficient v 0 y0)
    (hderiv : deriv (coefficient u 0) y0=deriv (coefficient v 0) y0) :
    EqOn (coefficient u 0) (coefficient v 0) (Ioi (0 : ℝ)) :=
  zero_initial_unique (actual_zero_solution hu hpu hPDEu) (actual_zero_solution hv hpv hPDEv)
    hy0 hvalue hderiv

end
end ImbalancedChen.Part3.ActualZeroFourierInitialData20261026b
