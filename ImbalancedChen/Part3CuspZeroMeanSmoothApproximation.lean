import ImbalancedChen.Part3CuspFourierL2Plancherel
import ImbalancedChen.Part3ActualCuspFourierSection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Concrete smooth test functions for actual period-one cusp sections. The
N-th approximant is the finite Fourier polynomial with indices [-N,N]
and with zero removed. Its real lift is C-infinity and exactly periodic;
its normalized Haar mean vanishes for every N. For every mean-zero L2
section the polynomials converge in the actual normalized-Haar L2 norm.
The derivative is the literal finite sum of the differentiated characters.

This is a smooth approximation result, not a Maass/Eisenstein expansion or
a supplied density/Plancherel hypothesis. The all-integer Hilbert basis
used in the convergence proof is Mathlib's actual AddCircle basis.
-/

noncomputable section

namespace ImbalancedChen.Part3.CuspZeroMeanSmoothApproximationSourceOnly

open Set MeasureTheory Filter
open scoped ENNReal Topology MatrixGroups UpperHalfPlane

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1:ℝ)))

/-- The measure is the Haar probability measure, not unnormalized Haar. -/
theorem normalized_haar_mass :
    AddCircle.haarAddCircle (T := (1:ℝ)) Set.univ=1 := by simp

def window (N : ℕ) : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)

/-- A literal finite trigonometric polynomial with no constant character. -/
def polynomial (f : CircleL2) (s : Finset ℤ) : C(UnitAddCircle,ℂ) :=
  ∑ n ∈ s.erase 0, AddCircle.fourierCoeff f n • AddCircle.fourier n

def polynomialL2 (f : CircleL2) (s : Finset ℤ) : CircleL2 :=
  ∑ n ∈ s.erase 0, AddCircle.fourierCoeff f n • AddCircle.fourierLp 2 n

theorem polynomial_apply (f : CircleL2) (s : Finset ℤ) (x : UnitAddCircle) :
    polynomial f s x=∑ n ∈ s.erase 0, AddCircle.fourierCoeff f n • AddCircle.fourier n x := by
  simp [polynomial]

/-- The concrete polynomial and the finite Hilbert-space sum are the same
L2 element, through the actual continuous-function inclusion. -/
theorem toLp_polynomial (f : CircleL2) (s : Finset ℤ) :
    ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (polynomial f s)=
      polynomialL2 f s := by
  simp only [polynomial,polynomialL2,map_sum,map_smul,AddCircle.fourierLp]

def realLift (f : CircleL2) (s : Finset ℤ) (x : ℝ) : ℂ :=
  polynomial f s (x:UnitAddCircle)

/-- The derivative is a concrete finite sum and retains its signed modes. -/
def realDerivative (f : CircleL2) (s : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ n ∈ s.erase 0, AddCircle.fourierCoeff f n •
    ((2*(Real.pi:ℂ)*Complex.I*(n:ℂ))*AddCircle.fourier n (x:UnitAddCircle))

theorem realLift_periodic (f : CircleL2) (s : Finset ℤ) :
    Function.Periodic (realLift f s) 1 := by
  intro x
  change polynomial f s ((x+1:ℝ):UnitAddCircle)=polynomial f s (x:UnitAddCircle)
  rw [AddCircle.coe_add_period]

private theorem characterLift_contDiff (n : ℤ) :
    ContDiff ℝ ⊤ (fun x : ℝ => AddCircle.fourier n (x:UnitAddCircle)) := by
  simp only [AddCircle.fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Every approximating test function is genuinely smooth after lifting
from the quotient circle to the real horizontal coordinate. -/
theorem realLift_contDiff (f : CircleL2) (s : Finset ℤ) :
    ContDiff ℝ ⊤ (realLift f s) := by
  have hfun : realLift f s=
      fun x : ℝ => ∑ n ∈ s.erase 0,
        AddCircle.fourierCoeff f n • AddCircle.fourier n (x:UnitAddCircle) := by
    funext x
    exact polynomial_apply f s _
  rw [hfun]
  exact ContDiff.sum fun n _ => (characterLift_contDiff n).const_smul _

theorem realLift_hasDerivAt (f : CircleL2) (s : Finset ℤ) (x : ℝ) :
    HasDerivAt (realLift f s) (realDerivative f s x) x := by
  have hfun : realLift f s=
      fun y : ℝ => ∑ n ∈ s.erase 0,
        AddCircle.fourierCoeff f n • AddCircle.fourier n (y:UnitAddCircle) := by
    funext y
    exact polynomial_apply f s _
  rw [hfun]
  simpa only [realDerivative,Complex.ofReal_one,div_one] using
    (HasDerivAt.fun_sum (u := s.erase 0) fun n _ =>
      (AddCircle.hasDerivAt_fourier (1:ℝ) n x).const_smul (AddCircle.fourierCoeff f n))

theorem realLift_deriv (f : CircleL2) (s : Finset ℤ) :
    deriv (realLift f s)=realDerivative f s := by
  funext x
  exact (realLift_hasDerivAt f s x).deriv

private theorem integral_nonzero_character (n : ℤ) (hn : n≠0) :
    (∫ x : UnitAddCircle, AddCircle.fourier n x ∂AddCircle.haarAddCircle)=0 := by
  have h := congrFun (AddCircle.fourierCoeff_fourier (T := (1:ℝ)) n) 0
  simpa [AddCircle.fourierCoeff,AddCircle.fourier_zero,hn,Ne.symm hn] using h

private theorem character_integrable (n : ℤ) :
    Integrable (AddCircle.fourier (T := (1:ℝ)) n) AddCircle.haarAddCircle := by
  simpa only [integrableOn_univ] using
    ((AddCircle.fourier (T := (1:ℝ)) n).continuous.continuousOn.integrableOn_compact
      isCompact_univ : IntegrableOn (AddCircle.fourier (T := (1:ℝ)) n)
        Set.univ AddCircle.haarAddCircle)

/-- Erasing the zero mode makes the actual integral of every test function
zero, irrespective of whether the original section has zero mean. -/
theorem polynomial_integral_zero (f : CircleL2) (s : Finset ℤ) :
    (∫ x : UnitAddCircle, polynomial f s x ∂AddCircle.haarAddCircle)=0 := by
  simp_rw [polynomial_apply]
  rw [integral_finsetSum (s.erase 0)
    (fun n _ => (character_integrable n).const_smul (AddCircle.fourierCoeff f n))]
  apply Finset.sum_eq_zero
  intro n hn
  rw [integral_smul,integral_nonzero_character n (Finset.ne_of_mem_erase hn),smul_zero]

theorem polynomial_zero_coefficient (f : CircleL2) (s : Finset ℤ) :
    AddCircle.fourierCoeff (polynomial f s) 0=0 := by
  simpa [AddCircle.fourierCoeff,AddCircle.fourier_zero] using polynomial_integral_zero f s

/-- Actual finite approximants converge in L2 over normalized Haar. Erasing
zero changes no finite sum when the section has zero constant coefficient. -/
theorem polynomialL2_tendsto (f : CircleL2)
    (hzero : AddCircle.fourierCoeff f 0=0) :
    Tendsto (polynomialL2 f) atTop (𝓝 f) := by
  have herase (s : Finset ℤ) : polynomialL2 f s=
      ∑ n ∈ s, AddCircle.fourierCoeff f n • AddCircle.fourierLp 2 n := by
    exact Finset.sum_erase s (by rw [hzero,zero_smul])
  simpa only [herase] using (AddCircle.hasSum_fourier_series_L2 f)

/-- Symmetric frequency cutoffs give a sequence, not only a directed net. -/
theorem window_polynomialL2_tendsto (f : CircleL2)
    (hzero : AddCircle.fourierCoeff f 0=0) :
    Tendsto (fun N => polynomialL2 f (window N)) atTop (𝓝 f) := by
  exact (polynomialL2_tendsto f hzero).comp (Finset.tendsto_Icc_neg (R := ℤ))

theorem window_L2_error_tendsto_zero (f : CircleL2)
    (hzero : AddCircle.fourierCoeff f 0=0) :
    Tendsto (fun N => ‖polynomialL2 f (window N)-f‖) atTop (𝓝 (0:ℝ)) := by
  simpa only [sub_self,norm_zero] using
    ((window_polynomialL2_tendsto f hzero).sub tendsto_const_nhds).norm

/-- Given a genuine mean-zero L2 section and a requested tolerance, one
literal finite Fourier polynomial supplies all smooth-test properties and
the requested error. No smooth-density input or coefficient bound is used. -/
theorem exists_smooth_zero_mean_approximation (f : CircleL2)
    (hzero : AddCircle.fourierCoeff f 0=0) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,
      ContDiff ℝ ⊤ (realLift f (window N)) ∧
      Function.Periodic (realLift f (window N)) 1 ∧
      (∫ x : UnitAddCircle, polynomial f (window N) x ∂AddCircle.haarAddCircle)=0 ∧
      ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
          (polynomial f (window N))-f‖<ε := by
  have hevent : ∀ᶠ N : ℕ in atTop, ‖polynomialL2 f (window N)-f‖<ε :=
    (window_L2_error_tendsto_zero f hzero).eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := hevent.exists
  exact ⟨N,realLift_contDiff f _,realLift_periodic f _,polynomial_integral_zero f _,
    by simpa only [toLp_polynomial] using hN⟩

/-- The zero-mean assumption may be the actual Haar integral of a section,
rather than a supplied statement about its L2 representative. -/
theorem memLp_zero_mean_approximation (g : UnitAddCircle → ℂ)
    (hg : MemLp g 2 AddCircle.haarAddCircle)
    (hmean : (∫ x : UnitAddCircle, g x ∂AddCircle.haarAddCircle)=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,
      ContDiff ℝ ⊤ (realLift (hg.toLp g) (window N)) ∧
      Function.Periodic (realLift (hg.toLp g) (window N)) 1 ∧
      (∫ x : UnitAddCircle, polynomial (hg.toLp g) (window N) x
        ∂AddCircle.haarAddCircle)=0 ∧
      ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
        (polynomial (hg.toLp g) (window N))-hg.toLp g‖<ε := by
  have hzero : AddCircle.fourierCoeff (hg.toLp g) 0=0 := by
    have hc := congrFun (AddCircle.fourierCoeff_congr_ae hg.coeFn_toLp) 0
    rw [hc]
    simpa [AddCircle.fourierCoeff,AddCircle.fourier_zero] using hmean
  exact exists_smooth_zero_mean_approximation (hg.toLp g) hzero ε hε

/-- Bundle the actual old Gamma0 cusp chart, at a fixed positive height. -/
def actualOldSection (level : ℕ) (hlevel : 0<level) (F : ℍ → ℂ)
    (hF : Continuous F)
    (hΓ : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ CongruenceSubgroup.Gamma0 level → ∀ z : ℍ,F (γ • z)=F z)
    (y : ℝ) (hy : 0<y) : C(UnitAddCircle,ℂ) :=
  ⟨ActualCuspFourierSectionSourceOnly.oldSection level hlevel F hΓ y hy,
    ActualCuspFourierSectionSourceOnly.oldSection_continuous level hlevel F hF hΓ y hy⟩

/-- A continuous automorphic function's actual old cusp section therefore
has concrete smooth zero-mean tests whenever its actual Haar mean vanishes.
Compactness supplies its L2 representative through ContinuousMap.toLp. -/
theorem actual_old_cusp_smooth_approximation
    (level : ℕ) (hlevel : 0<level) (F : ℍ → ℂ) (hF : Continuous F)
    (hΓ : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ CongruenceSubgroup.Gamma0 level → ∀ z : ℍ,F (γ • z)=F z)
    (y : ℝ) (hy : 0<y)
    (hmean : (∫ x : UnitAddCircle,actualOldSection level hlevel F hF hΓ y hy x
      ∂AddCircle.haarAddCircle)=0)
    (ε : ℝ) (hε : 0<ε) :
    let f : CircleL2 := ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
      (actualOldSection level hlevel F hF hΓ y hy)
    ∃ N : ℕ,
      ContDiff ℝ ⊤ (realLift f (window N)) ∧
      Function.Periodic (realLift f (window N)) 1 ∧
      (∫ x : UnitAddCircle,polynomial f (window N) x ∂AddCircle.haarAddCircle)=0 ∧
      ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
        (polynomial f (window N))-f‖<ε := by
  let f : CircleL2 := ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
    (actualOldSection level hlevel F hF hΓ y hy)
  have hzero : AddCircle.fourierCoeff f 0=0 := by
    rw [show f=ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
      (actualOldSection level hlevel F hF hΓ y hy) from rfl,
      AddCircle.fourierCoeff_toLp]
    simpa [AddCircle.fourierCoeff,AddCircle.fourier_zero] using hmean
  exact exists_smooth_zero_mean_approximation f hzero ε hε

end ImbalancedChen.Part3.CuspZeroMeanSmoothApproximationSourceOnly
