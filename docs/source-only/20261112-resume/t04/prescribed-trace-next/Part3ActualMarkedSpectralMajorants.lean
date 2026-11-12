import ImbalancedChen.Part3ActualPrescribedDiagonalTrace
import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov

/-! Cauchy--Schwarz for the same native Fourier amplitudes used by
both original finite markings. The denominator is counted exactly once. -/
namespace ImbalancedChen.Part3.ActualMarkedSpectralMajorants20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedDiagonalTrace20261112 ActualSingleModeSpectralEnergy20261112
open ActualCuspBasisWhittakerCoefficients20261102 ActualFullCuspEigenbasis20261026b
open ActualContinuousPoincarePairing20261110 OriginalContinuousClassRemoval20261110
open ActualContinuousClassFourier20261110
open ActualCuspDenominatorClasses20261110 ActualOppositeBesselTransform20261112
open OriginalOppositeMarkedKuznetsov20261112

private def cost (S : Finset ℕ) (w : ℕ → ℂ) : ℝ := ∑ p∈S,‖w p‖^2

private theorem marked_sq (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ) (f : ℤ → ℂ) :
    ‖markedRow S w ind f‖^2≤cost S w*∑ p∈S,‖f (ind p)‖^2 := by
  have h : ‖markedRow S w ind f‖≤∑ p∈S,‖w p‖*‖f (ind p)‖ := by
    simpa only [markedRow,norm_mul] using norm_sum_le S (fun p => w p*f (ind p))
  apply le_trans ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr h)
  exact Finset.sum_mul_sq_le_sq_mul_sq S (fun p => ‖w p‖) (fun p => ‖f (ind p)‖)

theorem discrete_row (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (nonzero : ∀ p∈S,ind p≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun i : actualCuspBasisIndex N (NeZero.pos N) =>
      basisWeight N (spectralTest ell Y) i*‖markedRow S w ind (basisR N (NeZero.pos N) i g)‖^2) := by
  let W := basisWeight N (spectralTest ell Y)
  have s := (summable_sum (s := S) (fun p hp => discrete_diagonal N g (ind p) (nonzero p hp) ell hY)).mul_left (cost S w)
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (sq_nonneg _)) (fun i => ?_) s
  have H := mul_le_mul_of_nonneg_left (marked_sq S w ind (basisR N (NeZero.pos N) i g)) (norm_nonneg _ : 0≤W i)
  simpa only [Finset.mul_sum,mul_comm,mul_assoc,mul_left_comm] using H

def continuousRowBudget (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (Φ : ℝ → ℂ) (t : ℝ) : ℝ := cost S w*∑ p∈S,weightedContinuousMass N one (ind p) Φ t

theorem continuous_row_budget (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (nonzero : ∀ p∈S,ind p≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (continuousRowBudget N one S w ind (spectralTest ell Y)) :=
  (integrable_finsetSum S (fun p hp => continuous_diagonal N one (ind p) (nonzero p hp) ell hY)).const_mul _

private def contFactor (Φ : ℝ → ℂ) (t : ℝ) : ℝ := ‖oppositeWeight Φ t‖/(4*Real.pi*Real.cosh (Real.pi*t))

private theorem factor_nonneg (Φ : ℝ → ℂ) (t : ℝ) : 0≤contFactor Φ t :=
  div_nonneg (norm_nonneg _) (by positivity)

private theorem factor_sum (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (Φ : ℝ → ℂ) (t : ℝ) :
    contFactor Φ t*(∑ a : Parameters N,‖nativeR a one m t‖^2)=weightedContinuousMass N one m Φ t := by
  rw [weightedContinuousMass,continuousMass,contFactor]
  field_simp [Real.pi_ne_zero,(Real.cosh_pos (Real.pi*t)).ne'] <;> ring

private theorem cont_row (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (Φ : ℝ → ℂ) (t : ℝ) :
    contFactor Φ t*(∑ a : Parameters N,‖markedRow S w ind (fun m => nativeR a one m t)‖^2)≤
      continuousRowBudget N one S w ind Φ t := by
  have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Parameters N))) (fun a _ =>
    marked_sq S w ind (fun m => nativeR a one m t))
  apply (mul_le_mul_of_nonneg_left H (factor_nonneg Φ t)).trans_eq
  rw [← Finset.mul_sum,Finset.sum_comm,continuousRowBudget,mul_left_comm,Finset.mul_sum]
  simp only [factor_sum]

private theorem product_le (x y : ℂ) : ‖x‖*‖y‖≤‖x‖^2+‖y‖^2 := by
  nlinarith only [sq_nonneg (‖x‖-‖y‖),sq_nonneg ‖x‖,sq_nonneg ‖y‖]

theorem discrete_pair (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (S T : Finset ℕ) (u v : ℕ → ℂ) (f j : ℕ → ℤ)
    (hf : ∀ p∈S,f p≠0) (hj : ∀ n∈T,j n≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    let Φ := spectralTest ell Y
    Summable (fun i : actualCuspBasisIndex N (NeZero.pos N) =>
      (8*kTransform (basisOrder N (NeZero.pos N) i) Φ)*
        (star (markedRow S u f (basisR N (NeZero.pos N) i g))*markedRow T v j (basisR N (NeZero.pos N) i h))) := by
  let B := discrete_row N g S u f hf ell hY
  let C := discrete_row N h T v j hj ell hY
  apply Summable.of_norm_bounded (B.add C)
  intro i
  simp only [basisWeight,norm_mul,norm_star,← mul_add]
  exact mul_le_mul_of_nonneg_left (product_le _ _) (norm_nonneg _)

theorem continuous_pair_bound (N : ℕ) [NeZero N] (b c : Bool) (S T : Finset ℕ) (u v : ℕ → ℂ) (f j : ℕ → ℤ)
    (Φ : ℝ → ℂ) (t : ℝ) :
    ‖continuousDensity Φ N t (fun a => markedRow S u f (fun m => nativeR a b m t))
      (fun a => markedRow T v j (fun m => nativeR a c m t))‖ ≤
        continuousRowBudget N b S u f Φ t+continuousRowBudget N c T v j Φ t := by
  let X := fun a : Parameters N => markedRow S u f (fun m => nativeR a b m t)
  let Z := fun a : Parameters N => markedRow T v j (fun m => nativeR a c m t)
  have H : ‖∑ a,star (X a)*Z a‖≤(∑ a,‖X a‖^2)+(∑ a,‖Z a‖^2) := by
    rw [← Finset.sum_add_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => by rw [norm_mul,norm_star]; exact product_le _ _))
  have E : ‖continuousDensity Φ N t X Z‖=contFactor Φ t*‖∑ a,star (X a)*Z a‖ := by
    simp only [continuousDensity,contFactor,norm_div,norm_mul,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Real.norm_of_nonneg (Real.cosh_pos _).le]
    ring
  rw [show ‖continuousDensity Φ N t _ _‖=_ from E]
  have J := mul_le_mul_of_nonneg_left H (factor_nonneg Φ t)
  rw [mul_add] at J
  exact J.trans (add_le_add (cont_row N b S u f Φ t) (cont_row N c T v j Φ t))

end
end ImbalancedChen.Part3.ActualMarkedSpectralMajorants20261112
