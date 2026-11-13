import ImbalancedChen.Part3OriginalSwitchedIntervalReturn
import ImbalancedChen.Part3OriginalSwitchedIntervalUnit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Eliminate both Mellin frequencies from the complementary return.
Only the full level-and-slot energy is maximized over common prefixes. -/
namespace ImbalancedChen.Part3.OriginalSwitchedReturnedWindow20261113
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Classical
open OriginalSwitchedIntervalReturn20261113 (bill both returned)
open OriginalSwitchedIntervalUnit20261113 (short_unit)
open OriginalSwitchedMellinRows20261113 (density density_integrable density_decay)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy prefix_energy)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels tau exceptional)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

private def moment (t : ℝ) := ‖density t‖*(1+|t/2|)^2

private theorem moment_integrable : Integrable moment := by
  obtain ⟨B,bp,decay⟩ := density_decay
  apply (integrable_inv_one_add_sq.const_mul (4*B)).mono'
    (density_integrable.aestronglyMeasurable.norm.mul
      (show Continuous (fun t : ℝ => (1+|t/2|)^2) from by fun_prop).aestronglyMeasurable)
  filter_upwards [] with t
  have t2 : t^2=|t|^2 := (sq_abs t).symm
  have p : (1+|t/2|)^2≤2*(1+t^2) := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),t2]
    nlinarith only [sq_nonneg (1-|t|),sq_nonneg |t|]
  have q : (1+t^2)^2≤2*(1+t^4) := by nlinarith only [sq_nonneg (1-t^2)]
  have cross := mul_le_mul_of_nonneg_right p (by positivity : 0≤1+t^2)
  have r : (1+|t/2|)^2*(1+t^2)≤4*(1+t^4) := by nlinarith only [cross,q]
  change ‖‖density t‖*(1+|t/2|)^2‖≤(4*B)*(1+t^2)⁻¹
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_right (decay t) (sq_nonneg _)).trans
  rw [←div_eq_mul_inv (4*B) (1+t^2)]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1+t^2)).mpr
  rw [show B/(1+t^4)*(1+|t/2|)^2*(1+t^2)=(B*((1+|t/2|)^2*(1+t^2)))/(1+t^4) by ring]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<1+t^4)).mpr
  exact (mul_le_mul_of_nonneg_left r bp.le).trans_eq (by ring)

def prefixMax (L : Finset ℕ+) (X ω : ℝ) (a b : ℕ) (ab : a≤b) :=
  (Finset.Icc a b).sup' ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,ab⟩⟩
    (fun n => intervalEnergy L X ω a (min b (n+1)) 0)

/-- For each returned dyadic level window and each allowed subinterval
of the original frequency block. Every constant precedes the windows,
the original dyadic block, its subinterval and the common phase. -/
theorem prefix_return {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (Q B : ℝ),0<Q → 0<B → ∀ (ω : ℝ) (j a b : ℕ)
      (lo : 2^j≤a) (ab : a≤b), b≤2^(j+1) →
      let M := classicalMScale j
      bill (classicalLevels B) T Y Q ω a b≤C*(prefixMax (classicalLevels B) Y ω a b ab+
          Y^ε*(B+M)*M) := by
  obtain ⟨K,X,kp,x1,H⟩ := returned tp t1 ep
  let A := ∫ t : ℝ,moment t
  let D := ∫ t : ℝ,‖density t‖
  let C := 1+2*A+64*sieveConstant*D
  have ap : 0≤A := integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have dp : 0≤D := integral_nonneg (fun _ => norm_nonneg _)
  have cp := sieveConstant_pos
  have dn : 0≤64*sieveConstant*D := by positivity
  have cpos : 0<C := by dsimp only [C];linarith
  refine ⟨K*C,X,mul_pos kp cpos,x1,fun Y hy Q B qp bp ω j a b lo ab hi => ?_⟩
  let L := classicalLevels B
  let M := classicalMScale j
  let U := prefixMax L Y ω a b ab
  let V := Y^ε*(B+M)*M
  have yp := zero_lt_one.trans_le (x1.trans hy)
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have vp : 0≤V := by dsimp only [V];positivity
  have up : 0≤U := by
    apply (show 0≤intervalEnergy L Y ω a (min b (a+1)) 0 from Finset.sum_nonneg (fun z _ =>
      Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg yp.le _) (sq_nonneg _)))).trans
    exact Finset.le_sup' _ (Finset.mem_Icc.mpr ⟨le_rfl,ab⟩)
  have a0 := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have cap : b≤2*a := by rw [pow_succ] at hi;omega
  have main (t : ℝ) : both L Y ω a b t≤2*((1+|t/2|)^2*U) := by
    have p := prefix_energy L yp.le ω (-(t/2)) a0 ab cap
    have q := prefix_energy L yp.le ω (t/2) a0 ab cap
    rw [abs_neg] at p
    exact (add_le_add p q).trans_eq (by change _=2*((1+|t/2|)^2*U);rw [two_mul])
  have low (t : ℝ) : both L 1 ω a b t≤64*sieveConstant*(B+M)*M := by
    have p := short_unit bp j a b lo hi ω (-(t/2))
    have q := short_unit bp j a b lo hi ω (t/2)
    exact (add_le_add p q).trans_eq (by dsimp only [M];ring)
  let g (t : ℝ) := ‖density t‖*(both L Y ω a b t+Y^ε*both L 1 ω a b t)
  let h (t : ℝ) := moment t*(2*U)+‖density t‖*((64*sieveConstant)*V)
  have ih : Integrable h := (moment_integrable.mul_const _).add (density_integrable.norm.mul_const _)
  have nn (X' : ℝ) (xx : 0≤X') (t : ℝ) : 0≤both L X' ω a b t := by
    unfold both intervalEnergy
    apply add_nonneg <;> exact Finset.sum_nonneg (fun z _ => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg xx _) (sq_nonneg _)))
  have mh (t : ℝ) : ‖g t‖≤h t := by
    have gn : 0≤g t := mul_nonneg (norm_nonneg _) (add_nonneg (nn _ yp.le _)
      (mul_nonneg (Real.rpow_nonneg yp.le _) (nn 1 zero_le_one _)))
    rw [Real.norm_of_nonneg gn]
    apply (mul_le_mul_of_nonneg_left (add_le_add (main t)
      (mul_le_mul_of_nonneg_left (low t) (Real.rpow_nonneg yp.le _))) (norm_nonneg (density t))).trans_eq
    dsimp only [h,moment,V];ring
  have gb : |∫ t,g t|≤∫ t,h t := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le ih (ae_of_all _ mh)
  have int := (le_abs_self (∫ t,g t)).trans gb
  have hval : (∫ t,h t)=2*A*U+(64*sieveConstant*D)*V := by
    rw [show (∫ t,h t)=(∫ t,moment t*(2*U))+(∫ t,‖density t‖*((64*sieveConstant)*V)) from
      integral_add (moment_integrable.mul_const _) (density_integrable.norm.mul_const _),
      integral_mul_const,integral_mul_const]
    dsimp only [A,D];ring
  have c1 : 2*A≤C := by dsimp only [C];linarith only [dn]
  have c2 : 64*sieveConstant*D≤C := by dsimp only [C];linarith only [ap]
  have z := add_le_add (mul_le_mul_of_nonneg_right c1 up) (mul_le_mul_of_nonneg_right c2 vp)
  have e := H Y hy Q qp L ω a b a0
  exact e.trans ((mul_le_mul_of_nonneg_left ((int.trans_eq hval).trans z) kp.le).trans_eq (by
    change K*(C*U+C*V)=(K*C)*(U+V);ring))

end
end ImbalancedChen.Part3.OriginalSwitchedReturnedWindow20261113
