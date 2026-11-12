import ImbalancedChen.Part3PrescribedLogTensorCoefficients
import ImbalancedChen.Part3OriginalPrescribedAbelLift

/-! The actual (ell,Y) Abel lift, with a single coefficient family used
on the geometric side and on both spectral sides. -/
namespace ImbalancedChen.Part3.PrescribedLogTensorExpansion20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Classical BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3TwoLogMixed22SourceOnly
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open OriginalPrescribedAbelLift20261112

def c (ell : D4 → ℤ) (Y : ℝ) := coefficient (logLift ell Y)
def productAt (q : Modes) (a b : ℝ) : ℂ :=
  pattern q.1.1 q.2.1 a * star (rightPattern q.1.2 q.2.2 b)
def heightWeight (A : ℝ) (q : Modes) : ℝ :=
  Real.exp (A*(|(q.1.1:ℝ)|+|(q.1.2:ℝ)|))

private theorem decay_data (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) {A : ℝ} (hA : 0 ≤ A) :
    JetDecay (logLift ell Y) A := fun r s => logLift_jets ell hY r s A hA

theorem coefficients (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Modes,
      ‖c ell Y q‖ ≤ B*tail A q.1.1 q.1.2*decay q.2.1*decay q.2.2 :=
  coeff_decay (logLift ell Y) (logLift_smooth ell hY) hA (decay_data ell hY hA)

private def heightTail (i : ℤ) := Real.exp (-|(i:ℝ)|)
private theorem heightTail_summable : Summable heightTail := by
  have h := summable_geometric_of_lt_one (Real.exp_pos (-1)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ) < 0))
  have e (n : ℕ) : Real.exp (-(n:ℝ)) = Real.exp (-1)^n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  apply Summable.of_nat_of_neg <;>
    simpa only [heightTail,Int.cast_natCast,Int.cast_neg,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg _),e] using h

theorem absolute_centers (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) {A : ℝ} (hA : 0 ≤ A) :
    Summable (fun q : Modes => ‖c ell Y q‖*heightWeight A q) := by
  obtain ⟨B,hB,hc⟩ := coefficients ell hY (A := A+1) (by linarith)
  have hd := summable_decay.mul_of_nonneg summable_decay
    (fun n => by unfold decay; positivity) (fun n => by unfold decay; positivity)
  have hi := heightTail_summable.mul_of_nonneg heightTail_summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hh := (hi.mul_of_nonneg hd (fun p => by dsimp [heightTail]; positivity)
    (fun p => by dsimp [decay]; positivity)).mul_left B
  apply hh.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  rintro ⟨⟨i,j⟩,⟨k,l⟩⟩
  have ht : tail (A+1) i j*Real.exp (A*(|(i:ℝ)|+|(j:ℝ)|)) = heightTail i*heightTail j := by
    unfold tail heightTail; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (B*tail (A+1) i j*decay k*decay l)*Real.exp (A*(|(i:ℝ)|+|(j:ℝ)|)) :=
      mul_le_mul_of_nonneg_right (hc _) (Real.exp_pos _).le
    _ = _ := by linear_combination B*decay k*decay l*ht

theorem absolute_coefficients (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun q : Modes => ‖c ell Y q‖) := by
  simpa only [heightWeight,zero_mul,Real.exp_zero,mul_one] using absolute_centers ell hY (A := 0) le_rfl

theorem product_bound (q : Modes) (a b : ℝ) : ‖productAt q a b‖ ≤ 1 := by
  have B (i k : ℤ) (y : ℝ) : ‖pattern i k y‖ ≤ 1 := by
    rw [pattern_norm]; split_ifs <;> first | exact (win_bounds _).2 | norm_num
  rw [productAt,norm_mul,norm_star,right_norm]
  exact (mul_le_mul (B _ _ _) (B _ _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem cell_hasSum (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (i j : ℤ) (x y : ℝ) :
    HasSum (fun kl : ℤ × ℤ => c ell Y ((i,j),kl) * productAt ((i,j),kl) (Real.exp x) (Real.exp y))
      (rho (x-(i:ℝ))*rho (y-(j:ℝ))*logLift ell Y x y) := by
  let H := logLift ell Y
  let v := x-(i:ℝ)
  let u := y-(j:ℝ)
  let G := cellKernel H i j
  have hprod (kl : ℤ × ℤ) : productAt ((i,j),kl) (Real.exp x) (Real.exp y) =
      ((win v:ℂ)*(win u:ℂ))*(basis kl.1 v*basis kl.2 u) := by
    simp only [productAt,rightPattern,star_star,pattern_exp,v,u]; ring
  have hwin (t : ℝ) : (win t : ℂ)*rho t = rho t := by
    by_cases h : rho t = 0
    · simp [h]
    · simp only [win_plateau (Ioo_subset_Icc_self (rho_nonzero h)),Complex.ofReal_one,one_mul]
  have target : ((win v:ℂ)*(win u:ℂ))*G u v = rho v*rho u*H x y := by
    dsimp [G,cellKernel,v,u]
    rw [show (i:ℝ)+(x-(i:ℝ))=x by ring,show (j:ℝ)+(y-(j:ℝ))=y by ring]
    linear_combination (win (y-(j:ℝ)):ℂ)*rho (y-(j:ℝ))*H x y*hwin (x-(i:ℝ)) +
      rho (x-(i:ℝ))*H x y*hwin (y-(j:ℝ))
  by_cases hwu : win u = 0
  · have hr : rho u = 0 := by simpa [hwu] using (hwin u).symm
    change HasSum _ (rho v*rho u*H x y)
    simpa only [hprod,hwu,hr,Complex.ofReal_zero,mul_zero,zero_mul] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0:ℂ)) 0)
  by_cases hwv : win v = 0
  · have hr : rho v = 0 := by simpa [hwv] using (hwin v).symm
    change HasSum _ (rho v*rho u*H x y)
    simpa only [hprod,hwv,hr,Complex.ofReal_zero,zero_mul,mul_zero] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0:ℂ)) 0)
  obtain ⟨B,hB,hb⟩ := cell_budget H (logLift_smooth ell hY) (A := 0) le_rfl (decay_data ell hY le_rfl)
  have hu := win_nonzero hwu
  have hv := win_nonzero hwv
  have hs := C2_hasSum G (cell_regularity H (logLift_smooth ell hY) i j) (cell_support H i j)
    (B*tail 0 i j) (mul_nonneg hB (Real.exp_pos _).le) (hb i j) u v
    ⟨by linarith [hu.1],by linarith [hu.2]⟩ ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ha := (Equiv.prodComm ℤ ℤ).hasSum_iff.mpr hs
  have hs' := ha.mul_left ((win v:ℂ)*(win u:ℂ))
  rw [target] at hs'
  convert hs' using 1
  funext kl
  simp only [hprod,c,coefficient,Equiv.prodComm_apply,G,Function.comp_apply]
  ring

theorem pointwise (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (x y : ℝ) :
    HasSum (fun q : Modes => c ell Y q*productAt q (Real.exp x) (Real.exp y)) (logLift ell Y x y) := by
  let R := logLift ell Y x y
  have hs : Summable (fun q : Modes => c ell Y q*productAt q (Real.exp x) (Real.exp y)) :=
    (absolute_coefficients ell hY).of_norm_bounded (fun q => by
      rw [norm_mul]; simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (product_bound q _ _) (norm_nonneg (c ell Y q)))
  have hxy : (∑' ij : ℤ × ℤ, rho (x-(ij.1:ℝ))*rho (y-(ij.2:ℝ))*R) = R := by
    have hg := hs.prod.congr (fun ij => (cell_hasSum ell hY ij.1 ij.2 x y).tsum_eq)
    rw [hg.tsum_prod]
    have hk (i : ℤ) : (∑' j : ℤ, rho (x-(i:ℝ))*rho (y-(j:ℝ))*R) = rho (x-(i:ℝ))*R := by
      simpa only [mul_one] using (((rho_sum y).mul_left (rho (x-(i:ℝ)))).mul_right R).tsum_eq
    simp_rw [hk]
    simpa only [one_mul] using ((rho_sum x).mul_right R).tsum_eq
  apply hs.hasSum_iff.mpr
  rw [hs.tsum_prod]
  calc
    _ = ∑' ij : ℤ × ℤ, rho (x-(ij.1:ℝ))*rho (y-(ij.2:ℝ))*R :=
      tsum_congr (fun ij => (cell_hasSum ell hY ij.1 ij.2 x y).tsum_eq)
    _ = _ := hxy

def floor (Y : ℝ) : ℝ := (Y/(64*Real.pi))^2*Real.exp (-6)
theorem floor_pos {Y : ℝ} (hY : 0 < Y) : 0 < floor Y := by dsimp [floor]; positivity

theorem coeff_active (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (q : Modes) (hc : c ell Y q ≠ 0) :
    (Y/(64*Real.pi))^2 < Real.exp ((q.1.1:ℝ)+(q.1.2:ℝ)+2) := by
  by_contra! h
  have hz : cellKernel (logLift ell Y) q.1.1 q.1.2 = fun _ _ => 0 := by
    funext u v
    by_cases hu : rho u = 0
    · simp [cellKernel,hu]
    by_cases hv : rho v = 0
    · simp [cellKernel,hv]
    have hcut := (Real.exp_le_exp.mpr (show ((q.1.1:ℝ)+v)+((q.1.2:ℝ)+u) ≤
      (q.1.1:ℝ)+(q.1.2:ℝ)+2 by linarith [(rho_nonzero hu).2,(rho_nonzero hv).2])).trans h
    simp only [cellKernel,logLift_below ell hY _ _ hcut,mul_zero]
  apply hc
  simp only [c,coefficient,hz,C2,coeff64_zero]

theorem active_product (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (q : Modes) {a b : ℝ}
    (hc : c ell Y q ≠ 0) (hh : productAt q a b ≠ 0) : floor Y ≤ a*b := by
  have h := mul_ne_zero_iff.mp hh
  have hφ : pattern q.1.2 q.2.2 b ≠ 0 := by simpa [rightPattern] using h.2
  exact product_floor (pattern_support _ _ (subset_tsupport _ h.1))
    (pattern_support _ _ (subset_tsupport _ hφ)) (coeff_active ell hY q hc)

end
end ImbalancedChen.Part3.PrescribedLogTensorExpansion20261112
