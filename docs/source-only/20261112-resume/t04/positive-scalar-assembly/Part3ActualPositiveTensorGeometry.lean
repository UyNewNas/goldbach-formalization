import ImbalancedChen.Part3ActualPositiveTensorIntegral
import ImbalancedChen.Part3OriginalPositiveScalarGeometry
import Mathlib.MeasureTheory.Integral.Prod
import Batteries.Tactic.OpenPrivate

/-! Absolute tensor summation in the compact physical Bruhat integral and
in the identity cell. A single lower height excludes all small arguments. -/
namespace ImbalancedChen.Part3.ActualPositiveTensorGeometry20261112
noncomputable section
open Set MeasureTheory Complex
open scoped Topology
open OriginalPositiveScalarGeometry20261112 OriginalPositiveHeightTest20261112 ActualPositiveTensorIntegral20261112
open PrescribedLogTensorCoefficients20261112 (Modes)
open PrescribedLogTensorExpansion20261112 (productAt)
open P3Period64NativeReconstructionSourceOnly (e)
open RadialSchrodingerL2Form20261025a
open OriginalAbelOrbit (heights)

private def second (k : ℝ) (z : ℝ×ℝ) := k*z.2/(z.1^2+z.2^2)
private def osc (k : ℝ) (z : ℝ×ℝ) : ℂ :=
  (((z.2⁻¹)^2:ℝ):ℂ)*e (z.1+k*z.1/(z.1^2+z.2^2))

private theorem form (H : ℝ→ℝ→ℂ) (k : ℝ) (z : ℝ×ℝ) :
    plane H k z.1 z.2=H z.2 (second k z)*osc k z := by
  dsimp [plane,osc,second,Complex.real_smul]; ring

private theorem height_bound {k l u : ℝ} (kl : 0≤k) (hl : 0<l) {z : ℝ×ℝ}
    (a : z.2∈Icc l u) (b : second k z∈Icc l u) :
    |z.1|≤1+k*u/l ∧ l^2≤k := by
  have ap := hl.trans_le a.1
  have d : 0<z.1^2+z.2^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ap)
  have bm := (le_div_iff₀ d).mp b.1
  have su := mul_le_mul_of_nonneg_left a.2 kl
  have Q : z.1^2≤k*u/l := (le_div_iff₀ hl).mpr (by nlinarith [mul_nonneg (sq_nonneg z.2) hl.le])
  have r : z.2*second k z≤k := by
    dsimp [second]; rw [←mul_div_assoc,div_le_iff₀ d]; nlinarith [mul_nonneg (sq_nonneg z.1) kl]
  have q := mul_le_mul a.1 b.1 hl.le ap.le
  exact ⟨by nlinarith [sq_nonneg (|z.1|-1),sq_abs z.1],by nlinarith⟩

private theorem osc_meas (k : ℝ) : Measurable (osc k) := by unfold osc e; fun_prop
private theorem second_meas (k : ℝ) : Measurable (second k) := by unfold second; fun_prop

theorem orbit (η H : RadialTest) (R q : ℝ) :
    HasSum (fun v : Modes => coeff η H R v*induced (productAt v) q)
      (induced (height η H R) q) := by
  let k := (q/(4*Real.pi))^2
  let μ := volume.prod heights
  obtain ⟨B,_,cov⟩ := box η H R
  let l := Real.exp (-B); let u := Real.exp B; let V := 1+k*u/l
  let K : Set (ℝ×ℝ) := Icc (-V) V ×ˢ Icc l u
  have Kc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have lp : 0<l := Real.exp_pos _
  have om : ∀ z : ℝ×ℝ,‖osc k z‖=(z.2⁻¹)^2 := fun z => by
    simp only [osc,norm_mul,P3Period64NativeReconstructionSourceOnly.norm_e,Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _),mul_one]
  let m := K.indicator (fun _ : ℝ×ℝ => (l⁻¹)^2)
  have fin : μ K<⊤ := by
    dsimp only [μ,K,heights]
    rw [Measure.prod_prod]; exact ENNReal.mul_lt_top isCompact_Icc.measure_lt_top
      ((Measure.restrict_le_self (μ:=volume) (s:=Ioi (0:ℝ)) _).trans_lt isCompact_Icc.measure_lt_top)
  have I : Integrable m μ := (integrable_indicator_iff Kc.measurableSet).mpr ((integrableOn_const fin.ne))
  have maj := exchange μ η H R Prod.snd (second k) (osc k) m measurable_snd (second_meas _) (osc_meas _).aestronglyMeasurable I
    (fun z => indicator_nonneg (fun _ _ => sq_nonneg _) z) (by
      intro v c z h
      obtain ⟨a,b⟩ := cov v c _ _ h
      have hb := height_bound (sq_nonneg _) lp a b
      rw [m,indicator_of_mem (show z∈K from ⟨abs_le.mp hb.1,a⟩),om]
      exact pow_le_pow_left₀ (inv_nonneg.mpr (lp.trans_le a.1).le) (inv_anti₀ lp a.1) 2)
  have target : induced (height η H R) q=(4*Real.pi/q:ℝ) •
      (∫ z : ℝ×ℝ,height η H R z.2 (second k z)*osc k z ∂μ) := by
    rw [integral_prod _ maj.1,induced]; simp_rw [form]
  rw [target]
  apply (maj.2.2.const_smul (4*Real.pi/q)).congr_fun
  intro v
  have step := integral_prod _ (maj.2.1 v)
  dsimp only [μ] at step
  simp_rw [integral_const_mul] at step
  rw [induced]; simp_rw [form]
  simp only [Complex.real_smul]
  linear_combination (4*Real.pi/q:ℝ:ℂ)*step.symm

theorem diagonal_sum (η H : RadialTest) (R : ℝ) (z p : ℕ) (h : ℤ) :
    HasSum (fun v : Modes => coeff η H R v*diagonal (productAt v) z p h)
      (diagonal (height η H R) z p h) := by
  by_cases hit : z=1 ∧ (p:ℤ)=h
  · obtain ⟨B,_,cov⟩ := box η H R
    let l := Real.exp (-B); let u := Real.exp B
    let K := Icc l u
    let W := fun x : ℝ => ((x⁻¹)^2:ℝ:ℂ)
    let m := K.indicator (fun _ : ℝ => (l⁻¹)^2)
    have bounded : Integrable m heights :=
      ((integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const isCompact_Icc.measure_lt_top.ne) : Integrable m volume).restrict
    have S := exchange heights η H R id id W m measurable_id measurable_id
      (by dsimp [W]; fun_prop) bounded (fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x) (by
        intro v c x hx
        have a := (cov v c x x hx).1
        rw [m,indicator_of_mem a]; simp only [W,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (inv_nonneg.mpr ((Real.exp_pos _).trans_le a.1).le) (inv_anti₀ (Real.exp_pos _) a.1) 2)
    simpa only [diagonal,if_pos hit,Complex.real_smul,id_eq,W,mul_comm (((_:ℝ)⁻¹^2:ℝ):ℂ)] using S.2.2
  · simp [diagonal,hit]

theorem small (η H : RadialTest) (R : ℝ) :
    ∃ δ : ℝ,0<δ ∧ ∀ q,0<q → q<δ → (∀ v : Modes,coeff η H R v*induced (productAt v) q=0) ∧
      induced (height η H R) q=0 := by
  obtain ⟨B,_,C⟩ := box η H R
  let l := Real.exp (-B)
  have lp : 0<l := Real.exp_pos _
  refine ⟨4*Real.pi*l,by positivity,fun q pq hq => ?_⟩
  let k := (q/(4*Real.pi))^2
  have qq : 0<q/(4*Real.pi) := by positivity
  have eq : q/(4*Real.pi)<l := (div_lt_iff₀ (by positivity)).mpr (by simpa only [mul_comm l] using hq)
  have kk : k<l^2 := pow_lt_pow_left₀ eq qq.le (by norm_num)
  have zero (v : Modes) : coeff η H R v*induced (productAt v) q=0 := by
    by_cases c : coeff η H R v=0
    · simp [c]
    have e (z : ℝ×ℝ) : productAt v z.2 (second k z)=0 := by
      by_contra hn
      have ab := C v c _ _ hn
      exact (not_le_of_gt kk) (height_bound (sq_nonneg _) lp ab.1 ab.2).2
    unfold induced
    simp_rw [form]
    change coeff η H R v*((4*Real.pi/q:ℝ) • (∫ x : ℝ,∫ a,productAt v a (second k (x,a))*osc k (x,a) ∂heights))=0
    simp only [e,zero_mul,integral_zero,smul_zero,mul_zero]
  refine ⟨zero,?_⟩
  simpa only [zero,tsum_zero] using (orbit η H R q).tsum_eq.symm

end
end ImbalancedChen.Part3.ActualPositiveTensorGeometry20261112
