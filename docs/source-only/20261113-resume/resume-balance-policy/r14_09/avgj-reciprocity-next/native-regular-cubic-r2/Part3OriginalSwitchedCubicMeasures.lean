import ImbalancedChen.Part3OriginalSwitchedCubicBands
import ImbalancedChen.Part3OriginalRegularCumulativeMeasures

/-! Cubic summation of the two native positive measures. The large-sieve
constant precedes the dyadic coefficient interval, level and coefficients. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCubicMeasures20261113
noncomputable section
open Real Set MeasureTheory
open scoped Classical MatrixGroups
open OriginalSwitchedCubicBands20261113
open ActualMarkedCubicPrice20261112 (cubic linePrice slotPrice slotPrice_nn)
open ActualUnitBandSpectralMass20261112 (exceptional height)
open ActualFullCuspEigenbasis20261026b
open OriginalRegularPacketTest20261113 (Dyadic energy energy_nonneg discreteRow lineMass lineMass_nonneg mark)
open OriginalRegularBaseCumulative20261113 (baseTerm lineTerm)
open OriginalRegularCumulativeMeasures20261113 (manuscript_weight_zero)
open OriginalCumulativeContinuousRemoval20261110 (marked_density_cont)

private theorem discrete {ι : Type*} (x : ι→ℝ) (f : ι→ℝ) (nn : ∀ i,0≤f i)
    {A D E : ℝ} (a0 : 0≤A) (d0 : 0≤D) (e0 : 0≤E)
    (cap : ∀ n : ℕ,let F := fun i => if |x i|≤radius (n+1) then f i else 0
      Summable F ∧ (∑' i,F i)≤D*((radius (n+1))^2+A)*E) :
    Summable (fun i => cubic (x i)*f i) ∧
      (∑' i,cubic (x i)*f i)≤8*D*(1+A)*E := by
  classical
  let F := fun (n : ℕ) i => if |x i|≤radius (n+1) then f i else 0
  let G := fun v : ℕ×ι => discount v.1*F v.1 v.2
  let B := 4*D*(1+A)*E
  have pos (v : ℕ×ι) : 0≤G v := by
    apply mul_nonneg (discount_nn _)
    dsimp only [F];split <;> first | exact nn _ | rfl
  have row (n : ℕ) : Summable (fun i => G (n,i)) := (cap n).1.mul_left _
  have bound (n : ℕ) : (∑' i,G (n,i))≤bill B n := by
    change (∑' i,discount n*F n i)≤_
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left (cap n).2 (discount_nn n)).trans (dyadic_charge a0 d0 e0 n)
  have gsum := (bill_sum B).summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => pos (n,i))) bound
  have S : Summable G := (summable_prod_of_nonneg pos).mpr ⟨row,gsum⟩
  let embed := fun i => (Classical.choose (cover (x i)),i)
  have inj : Function.Injective embed := fun _ _ h => congrArg Prod.snd h
  have le (i : ι) : cubic (x i)*f i≤G (embed i) := by
    let n := Classical.choose (cover (x i))
    have h : x i∈shell n := Classical.choose_spec (cover (x i))
    have ok : |x i|≤radius (n+1) := abs_le.mpr (within h)
    simpa only [G,embed,F,if_pos ok] using mul_le_mul_of_nonneg_right (cubic_le h) (nn i)
  have small := (S.comp_injective inj).of_nonneg_of_le (fun i => mul_nonneg (by unfold cubic;positivity) (nn i)) le
  refine ⟨small,(Summable.tsum_le_tsum_of_inj embed inj (fun v _ => pos v) le small S).trans ?_⟩
  rw [S.tsum_prod]
  exact (gsum.tsum_le_tsum bound (bill_sum B).summable).trans_eq
    ((bill_sum B).tsum_eq.trans (by dsimp only [B];ring))

private theorem incoming (f : ℝ→ℝ) (fc : Continuous f) (nn : ∀ t,0≤f t)
    {A D E : ℝ} (a0 : 0≤A) (d0 : 0≤D) (e0 : 0≤E)
    (cap : ∀ n : ℕ,(∫ t in Icc (-(radius (n+1))) (radius (n+1)),f t)≤D*((radius (n+1))^2+A)*E) :
    Integrable (fun t => cubic t*f t) ∧ (∫ t,cubic t*f t)≤8*D*(1+A)*E := by
  let V := fun t => cubic t*f t
  let B := 4*D*(1+A)*E
  let W := fun n => Icc (-(radius (n+1))) (radius (n+1))
  have Vc : Continuous V := (by unfold cubic;fun_prop (disch := positivity) : Continuous cubic).mul fc
  have vp (t) : 0≤V t := mul_nonneg (by unfold cubic;positivity) (nn t)
  have V1 (n) : IntegrableOn V (shell n) := (Vc.continuousOn.integrableOn_compact
    (isCompact_Icc : IsCompact (W n))).mono_set (fun _ h => within h)
  have fw (n) : IntegrableOn f (W n) := fc.continuousOn.integrableOn_compact isCompact_Icc
  have sub (n) : shell n⊆W n := fun _ h => within h
  have price (n) : (∫ t in shell n,V t)≤bill B n := by
    have I := integral_mono_ae (V1 n) (((fw n).mono_set (sub n)).const_mul (discount n))
      ((ae_restrict_mem (μ:=volume) (shell_meas n)).mono (fun t ht => mul_le_mul_of_nonneg_right (cubic_le ht) (nn t)))
    rw [integral_const_mul] at I
    have R := setIntegral_mono_set (fw n) (ae_of_all _ nn) (ae_of_all _ (fun _ h => sub n h))
    exact I.trans ((mul_le_mul_of_nonneg_left (R.trans (cap n)) (discount_nn n)).trans (dyadic_charge a0 d0 e0 n))
  have S := (bill_sum B).summable.of_nonneg_of_le (fun n => setIntegral_nonneg (shell_meas n) (fun t _ => vp t)) price
  have N : Summable (fun n => ∫ t in shell n,‖V t‖) := by simpa only [Real.norm_of_nonneg (vp _)] using S
  have whole := integrableOn_iUnion_of_summable_integral_norm V1 N
  have val := integral_iUnion shell_meas shells_disjoint whole
  rw [all_shells,Measure.restrict_univ] at val
  rw [all_shells,integrableOn_univ] at whole
  refine ⟨whole,val.le.trans ((S.tsum_le_tsum price (bill_sum B).summable).trans_eq ?_)⟩
  exact (bill_sum B).tsum_eq.trans (by dsimp only [B];ring)

theorem native_cubic {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) [NeZero N] (one neg : Bool) {M : ℝ},1/2≤M →
      ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic M S →
      let B := C*(1+M^(1+ε)/(N:ℝ))*energy S a
      let D := fun i => slotPrice N i*‖discreteRow N one neg S a i‖^2
      let E := fun t => linePrice t*lineMass N one neg S a t
      Summable D ∧ (∑' i,D i)≤B ∧ Integrable E ∧ (∫ t,E t)≤B := by
  obtain ⟨K,kp,H⟩ := manuscript_weight_zero ε ep
  refine ⟨8*K,by positivity,fun N inst one neg M hm S a band => ?_⟩
  let A := M^(1+ε)/(N:ℝ)
  let E := energy S a
  let x := height N
  let f := fun i => if exceptional N i then 0 else
    ‖discreteRow N one neg S a i‖^2/cosh (π*x i)
  have x0 (i) : 0≤x i := sqrt_nonneg _
  have f0 (i) : 0≤f i := by dsimp only [f];split <;> positivity
  have a0 : 0≤A := div_nonneg (rpow_nonneg (by linarith only [hm]) _) (Nat.cast_nonneg _)
  have P (n : ℕ) := H N one neg (radius_one (n+1)) hm S a band
  have piece (n : ℕ) (i) : (if |x i|≤radius (n+1) then f i else 0)=baseTerm N one neg (radius (n+1)) S a i := by
    rw [abs_of_nonneg (x0 i)]
    by_cases e : exceptional N i <;> by_cases y : x i≤radius (n+1) <;>
      simp only [baseTerm,f,e,not_true_eq_false,not_false_eq_true,false_and,true_and,
        if_false,if_true,show height N i=x i from rfl,y]
  have D := discrete x f f0 a0 kp.le (energy_nonneg S a) (fun n => by
    simp_rw [piece];exact ⟨(P n).1,(P n).2.1⟩)
  have R := incoming (lineTerm N one neg S a) (marked_density_cont N S a (mark neg) one)
    (fun t => div_nonneg (lineMass_nonneg N one neg S a t) (cosh_pos _).le)
    a0 kp.le (energy_nonneg S a) (fun n => (P n).2.2.2)
  have disc (i) : cubic (x i)*f i=slotPrice N i*‖discreteRow N one neg S a i‖^2 := by
    by_cases h : exceptional N i <;> simp [slotPrice,linePrice,x,f,h] <;> ring
  have cont (t) : cubic t*lineTerm N one neg S a t=linePrice t*lineMass N one neg S a t := by
    dsimp only [linePrice,lineTerm];ring
  simp_rw [disc] at D
  simp_rw [cont] at R
  exact ⟨D.1,D.2,R.1,R.2⟩

end
end ImbalancedChen.Part3.OriginalSwitchedCubicMeasures20261113
