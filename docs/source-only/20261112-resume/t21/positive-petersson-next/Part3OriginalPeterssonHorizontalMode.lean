import ImbalancedChen.Part3OriginalPeterssonLipschitz
import ImbalancedChen.Part3NativePeriod64Reconstruction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Fourier.AddCircle

namespace ImbalancedChen.Part3.OriginalPeterssonHorizontalMode20261112

noncomputable section
open Set Complex UpperHalfPlane MeasureTheory AddCircle
open scoped UpperHalfPlane Topology
open OriginalPeterssonLipschitz20261112
open P3Period64NativeReconstructionSourceOnly (e e_add norm_e)

def point (x : ℝ) : ℍ := ⟨(x:ℂ)+I,by simp⟩
def amplitude (n : ℕ) : ℂ := (Q (point 0))^n
def horizontal (n : ℕ) (F : ℝ→ℂ) : ℂ :=
  (amplitude n)⁻¹ * ∫ x in (0:ℝ)..1, e (-((n:ℝ)*x))*F x

theorem point_continuous : Continuous point :=
  Continuous.subtype_mk (Complex.continuous_ofReal.add continuous_const) _

theorem amp_ne (n : ℕ) : amplitude n≠0 := pow_ne_zero _ (Complex.exp_ne_zero _)

theorem point_phase (n : ℕ) (x t : ℝ) :
    (Q (point (x+t)))^n=amplitude n * e ((n:ℝ)*t)*e ((n:ℝ)*x) := by
  simp only [Q,point,amplitude,e,← Complex.exp_nat_mul,← Complex.exp_add]
  push_cast;congr 1;ring

private theorem char_eq (n : ℤ) (x : ℝ) : e ((n:ℝ)*x)=fourier n (x:UnitAddCircle) := by
  rw [fourier_coe_apply,e];push_cast;congr 1;ring

theorem horizontal_char (h n : ℕ) (z : ℂ) :
    horizontal h (fun x => z*e ((n:ℝ)*x))=if h=n then (amplitude h)⁻¹*z else 0 := by
  have H := congrFun (fourierCoeff_fourier (T:=1) (n:ℤ)) (h:ℤ)
  rw [fourierCoeff_eq_intervalIntegral _ _ (0:ℝ)] at H
  simp only [zero_add,div_one,one_smul,smul_eq_mul,Pi.single_apply] at H
  have Q : (∫ x in (0:ℝ)..1,e (-((h:ℝ)*x))*e ((n:ℝ)*x))=if h=n then 1 else 0 := by
    simpa only [← char_eq,Int.cast_neg,Int.cast_natCast,neg_mul,Int.natCast_inj,eq_comm (a:=n)] using H
  rw [horizontal,show (fun x : ℝ => e (-((h:ℝ)*x))*(z*e ((n:ℝ)*x)))=
    fun x => z*(e (-((h:ℝ)*x))*e ((n:ℝ)*x)) from funext fun _ => by ring,
    intervalIntegral.integral_const_mul,Q]
  split_ifs <;> simp

theorem horizontal_const_mul (h : ℕ) (z : ℂ) (F : ℝ→ℂ) :
    horizontal h (fun x => z*F x)=z*horizontal h F := by
  unfold horizontal
  simp_rw [show ∀x : ℝ,e (-((h:ℝ)*x))*(z*F x)=z*(e (-((h:ℝ)*x))*F x) by intro;ring]
  rw [intervalIntegral.integral_const_mul];ring

theorem horizontal_add (h : ℕ) {F G : ℝ→ℂ} (hF : Continuous F) (hG : Continuous G) :
    horizontal h (fun x => F x+G x)=horizontal h F+horizontal h G := by
  have q : Continuous (fun x : ℝ => e (-((h:ℝ)*x))) := by unfold e;fun_prop
  simp only [horizontal,mul_add,intervalIntegral.integral_add
    ((q.mul hF).intervalIntegrable ..) ((q.mul hG).intervalIntegrable ..)]

theorem horizontal_finite {ι : Type*} [Fintype ι] (h : ℕ) (F : ι→ℝ→ℂ)
    (hc : ∀i,Continuous (F i)) :
    horizontal h (fun x => ∑ i,F i x)=∑ i,horizontal h (F i) := by
  have q : Continuous (fun x : ℝ => e (-((h:ℝ)*x))) := by unfold e;fun_prop
  simp only [horizontal,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (q.mul (hc i)).intervalIntegrable ..),Finset.mul_sum]

/-- Extraction at a fixed original positive integer h on Im(w)=1. -/
theorem horizontal_hasSum {ι : Type*} [Countable ι] (h : ℕ) (F : ι→ℝ→ℂ) (f : ℝ→ℂ)
    (hF : ∀i,Continuous (F i)) {b : ι→ℝ} (hb : Summable b) (hB : ∀i x,‖F i x‖≤b i)
    (hs : ∀x,HasSum (fun i => F i x) (f x)) :
    HasSum (fun i => horizontal h (F i)) (horizontal h f) := by
  have q : Continuous (fun x : ℝ => e (-((h:ℝ)*x))) := by unfold e;fun_prop
  apply HasSum.mul_left
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => b i)
    (fun i => (q.mul (hF i)).aestronglyMeasurable)
    (fun i => .of_forall (fun x _ => by simpa only [norm_mul,norm_e,one_mul] using hB i x))
    (.of_forall (fun _ _ => hb)) intervalIntegrable_const
    (.of_forall (fun x _ => (hs x).mul_left _))

theorem translated_horizontal {a : ℕ} (ha : 1≤a) (h : ℕ) (V : ℂ) (t : ℝ) :
    horizontal h (fun x => translated a V (point (x+t))) =
      e ((h:ℝ)*t)*(∑' j : ℕ,modeTerm a V h j) := by
  let G := fun n : ℕ => ∑' j : ℕ,modeTerm a V n j
  let F := fun (n : ℕ) (x : ℝ) => G n*(Q (point (x+t)))^n
  let b := fun n : ℕ => ∑' j : ℕ,‖modeTerm a V n j*amplitude n‖
  have S := (freq_abs (a:=a) V (point 0)).prod_symm
  have hB : Summable b := S.prod
  have bound (n : ℕ) (x : ℝ) : ‖F n x‖≤b n := by
    rw [F,point_phase,norm_mul,norm_mul,norm_mul,norm_e,norm_e,mul_one,mul_one,← norm_mul,G,← tsum_mul_right]
    exact norm_tsum_le_tsum_norm (S.prod_factor n)
  have hh := horizontal_hasSum h F (fun x => translated a V (point (x+t)))
    (fun n => by dsimp [F,Q,point];fun_prop) hB bound (fun x => by
      rw [translated_modes ha]
      exact ((hB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => bound n x)).of_norm).hasSum)
  have eq (n : ℕ) : horizontal h (F n) =
      if h=n then e ((h:ℝ)*t)*G h else 0 := by
    dsimp [F]
    simp_rw [point_phase,← mul_assoc]
    rw [horizontal_char]
    split_ifs with hn
    · subst n;field_simp [amp_ne h];ring
    · rfl
  rw [← hh.tsum_eq]
  simp only [eq,tsum_ite_eq]

theorem translated_bessel {a : ℕ} (ha : 1≤a) {m h : ℕ} (hm : 0<m) (hh : 0<h)
    {C : ℝ} (hC : 0<C) (t : ℝ) :
    horizontal h (fun x => (1/(C:ℂ)^(a+1))*translated a (B*m/(C:ℂ)^2) (point (x+t))) =
      e ((h:ℝ)*t) * ((2*Real.pi/C:ℝ)*(-I)^(a+1)*
        ((Real.sqrt h/Real.sqrt m:ℝ):ℂ)^a*
        ActualGeneralJBesselSourceOnly.generalJ (a:ℂ) (argument (Real.sqrt m) (Real.sqrt h) C)) := by
  rw [horizontal_const_mul,translated_horizontal ha,← (mode_bessel a m h hC hm hh).tsum_eq,tsum_mul_left]
  ring

theorem translated_continuous {a : ℕ} (ha : 1≤a) (V : ℂ) (t : ℝ) :
    Continuous (fun x => translated a V (point (x+t))) := by
  let G := fun n : ℕ => ∑' j : ℕ,modeTerm a V n j
  let b := fun n : ℕ => ∑' j : ℕ,‖modeTerm a V n j*amplitude n‖
  have S := (freq_abs (a:=a) V (point 0)).prod_symm
  simp_rw [translated_modes ha]
  apply continuous_tsum (u:=b) (fun n => by dsimp [Q,point];fun_prop) S.prod
  intro n x
  rw [point_phase,norm_mul,norm_mul,norm_mul,norm_e,norm_e,mul_one,mul_one,← norm_mul,← tsum_mul_right]
  exact norm_tsum_le_tsum_norm (S.prod_factor n)

end
end ImbalancedChen.Part3.OriginalPeterssonHorizontalMode20261112
