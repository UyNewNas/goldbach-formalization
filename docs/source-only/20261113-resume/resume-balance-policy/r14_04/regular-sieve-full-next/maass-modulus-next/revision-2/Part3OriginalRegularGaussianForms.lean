import ImbalancedChen.Part3OriginalRegularGaussianMoment
import ImbalancedChen.Part3OriginalHolomorphicShortOscillation
import Batteries.Tactic.OpenPrivate

/-! Both arbitrary rows of the actual Gaussian orbital coefficient,
inside each oscillatory square-root sum before taking any norm. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianForms20261113
open Finset Real MeasureTheory Complex
open OriginalRegularPreKuznetsovAverage20261113 (gaussianOrbit G)
open OriginalRegularPreKuznetsovOscillation20261113
open OriginalRegularGaussianMoment20261113 (sineWeight cosineWeight)
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale cosineForm cosine_signs)
open OriginalHolomorphicShortOscillation20261113 (sineForm sine_signs rootRow rowProduct)
open OriginalAllParameterKloosterman20261113 (allCost all_parameter_bound dyadEnergy twistedForm_conj)
open OriginalTwistedKloosterman20261113 (twistedForm)
open private sinI cosI from ImbalancedChen.Part3OriginalRegularPreKuznetsovOscillation

def normalization : ℝ := Real.pi*Real.sqrt Real.pi/4
theorem normalization_pos : 0<normalization := by unfold normalization; positivity

def sinKernel (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :=
  ((scale c*ξ*G K ξ*Real.tanh ξ:ℝ):ℂ)*sineForm M c (Real.cosh ξ) (rootRow a) (rootRow b)

def cosKernel (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :=
  (((1-ξ*Real.tanh ξ-2*(K*ξ)^2)*G K ξ/Real.cosh ξ:ℝ):ℂ)*cosineForm M c (Real.cosh ξ) a b

def numerator (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) :=
  form M c a b (fun m n => gaussianOrbit K (argument c m n))

private theorem form_rows (M c : ℕ) (a b : ℕ→ℂ) (f : ℕ→ℕ→ℝ→ℂ)
    (hi : ∀ i j,Integrable (f (M+i) (M+j))) :
    Integrable (fun ξ : ℝ => form M c a b (fun m n => f m n ξ)) ∧
    form M c a b (fun m n => ∫ ξ : ℝ,f m n ξ)=
      ∫ ξ : ℝ,form M c a b (fun m n => f m n ξ) := by
  have row (i j : ℕ) := (hi i j).const_mul
    (a (M+i)*b (M+j)*OriginalSmoothPoissonTail.kloosterman c (M+i:ℕ) (M+j:ℕ))
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => row i j)),?_⟩
  dsimp only [form]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => row i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => row i j)]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul]

private theorem argument_positive {M c : ℕ} [NeZero c] (hM : 0<M) (i j : ℕ) :
    0<argument c (M+i) (M+j) := by
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  unfold argument scale
  push_cast
  positivity

private theorem sin_row (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :
    form M c a b (fun m n => ((argument c m n*sinDensity K (argument c m n) ξ:ℝ):ℂ))=
      sinKernel M c K a b ξ := by
  dsimp only [sinKernel,sineForm,form,sinDensity,sinFactor,rootRow]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  dsimp only [argument]
  rw [mul_comm (scale c*Real.sqrt ↑(M+i)*Real.sqrt ↑(M+j)) (Real.cosh ξ)]
  push_cast
  ring

private theorem cos_row (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :
    form M c a b (fun m n => (cosDensity K (argument c m n) ξ:ℂ))=cosKernel M c K a b ξ := by
  dsimp only [cosKernel,cosineForm,form,cosDensity,cosFactor]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [mul_comm (argument c (M+i) (M+j)) (Real.cosh ξ)]
  push_cast;ring

private theorem matrix_factor (M c : ℕ) (a b : ℕ→ℂ) (f : ℕ→ℕ→ℂ) (d : ℂ) :
    form M c a b (fun m n => d*f m n)=d*form M c a b f := by
  simp only [form,Finset.mul_sum]
  exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))

/-- Literal equality and absolute integrability of both representations of
the same arbitrary-sequence numerator. -/
theorem numerator_forms {M c : ℕ} [NeZero c] (hM : 0<M) {K : ℝ} (hK : 0<K) (a b : ℕ→ℂ) :
    Integrable (sinKernel M c K a b) ∧ Integrable (cosKernel M c K a b) ∧
    numerator M c K a b=((normalization*K^3:ℝ):ℂ)*(∫ ξ : ℝ,sinKernel M c K a b ξ) ∧
    numerator M c K a b=((normalization*K^3:ℝ):ℂ)*(∫ ξ : ℝ,cosKernel M c K a b ξ) := by
  let s := fun m n ξ => ((argument c m n*sinDensity K (argument c m n) ξ:ℝ):ℂ)
  let v := fun m n ξ => (cosDensity K (argument c m n) ξ:ℂ)
  have S := form_rows M c a b s (fun i j =>Complex.ofRealCLM.integrable_comp
    ((sinI hK (argument c (M+i) (M+j))).const_mul (argument c (M+i) (M+j))))
  have V := form_rows M c a b v (fun i j =>Complex.ofRealCLM.integrable_comp (cosI hK (argument c (M+i) (M+j))))
  simp only [s,sin_row] at S
  simp only [v,cos_row] at V
  refine ⟨S.1,V.1,?_,?_⟩
  · rw [←S.2,←matrix_factor]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [sine_orbit hK (argument_positive hM i j)]
    simp only [integral_complex_ofReal,integral_const_mul,normalization,Complex.ofReal_mul]
    push_cast <;> ring
  · rw [←V.2,←matrix_factor]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [cosine_orbit hK (argument_positive hM i j)]
    dsimp only [normalization]
    rw [integral_complex_ofReal]
    push_cast;ring

theorem all_forms {M c : ℕ} [NeZero c] (hM : 0<M) {q : ℝ} (hq : 0≤q) (a b : ℕ→ℂ) :
    ‖cosineForm M c q a b‖≤4*Real.exp (4*Real.pi)*allCost M c q*rowProduct M a b ∧
    ‖sineForm M c q a b‖≤4*Real.exp (4*Real.pi)*allCost M c q*rowProduct M a b := by
  have p (u v : ℕ→ℂ) : ‖twistedForm M c 0 q u v‖≤4*Real.exp (4*Real.pi)*allCost M c q*rowProduct M u v := by
    have h := all_parameter_bound M c hM (lam:=0) (le_refl 0) hq u v
    convert h using 1 <;> dsimp only [rowProduct] <;> ring
  have n := p (fun m => star (a m)) (fun m => star (b m))
  have n' : ‖twistedForm M c 0 (-q) a b‖≤4*Real.exp (4*Real.pi)*allCost M c q*rowProduct M a b := by
    simpa [twistedForm_conj M c 0 q a b,rowProduct,dyadEnergy] using n
  constructor
  · have h := norm_add_le (twistedForm M c 0 q a b) (twistedForm M c 0 (-q) a b)
    rw [←cosine_signs,norm_mul,Complex.norm_two] at h
    linarith only [h,p a b,n']
  · have h := norm_sub_le (twistedForm M c 0 q a b) (twistedForm M c 0 (-q) a b)
    rw [←sine_signs,norm_mul,norm_mul,Complex.norm_two,Complex.norm_I,mul_one] at h
    linarith only [h,p a b,n']

end ImbalancedChen.Part3.OriginalRegularGaussianForms20261113
end
