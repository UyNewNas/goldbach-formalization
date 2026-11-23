import ImbalancedChen.P1OriginalSingletonShortMediumSignedRow
import ImbalancedChen.P1OriginalSingletonMediumLiveRowInventory
import ImbalancedChen.P1OriginalSingletonOneLongConsumer

/-! The original occupied singleton HB row after paying its short-head
low-first triples on the retained band. Each other word, each long fibre
and the actual post-modulus Fourier tail remain explicit. Source only. -/
namespace ImbalancedChen.P1OriginalSingletonShortMediumLiveRow
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P1OriginalSingletonMediumReconstruction (scalar)
open P1OriginalSingletonMediumFourier (frequencyMode original retained original_eq_fourier
  retained_eq_band amplitude amplitude_integrable mode_integrable atMode)
open P1OriginalSingletonMediumRestoringBudget (modulusCost scalar_cost)
open P1OriginalSingletonMediumLiveRowInventory (liveComplements onComplement occurrenceAtom_partition
  fibreCost liveRowCost live_row_amplitude_cost)
open P1OriginalSingletonShortMediumSignedRow (otherMode exists_mode_cost)
open P1OriginalSingletonOneLongRectangle (occurrenceAtom)
open P1OriginalSingletonOneLongProfile (profileHeight)
open P1OriginalSingletonOneLongRestoration (height_one_le)
open P1OriginalSingletonOneLongConsumer (heightConstant heightConstant_one_le eventually_height_le_log)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalHighRankPostModulusRow (H)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalShortMediumWordKernel (otherKernel)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.AllRankCauchyCubeTail (outsideCube measurableSet_outsideCube)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open PrimeProducts.MellinInsertion20261028 (functional functional_integrable functional_mul
  exactDiscrepancy residueKernel)

variable {order : ℕ} {kap zeta kap0 : ℝ} (I : Index order kap zeta kap0)

private def fullMode (K : ℕ) (xi : Fin (size I.j)→ℝ) : ℂ :=
  exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
    completeProduct I.P.N (frequencyMode I K xi)

private theorem integrable_kernel (K : ℕ) (F : ℕ→ℂ) :
    Integrable (fun xi => amplitude I xi*functional (fibre I.bv I.i I.C)
      (fun y => F (completeProduct y)) (frequencyMode I K xi)) := by
  have h (y : Fin (size I.j)→ℕ) :
      Integrable (fun xi => amplitude I xi*frequencyMode I K xi y) := by
    have hh := (mode_integrable I y).const_mul (hbSlots (I.Z K) I.truncations I.roles y)
    exact hh.congr (Eventually.of_forall (fun xi => by dsimp only [frequencyMode]; ring))
  simpa only [functional_mul] using
    functional_integrable (fibre I.bv I.i I.C) (fun y => F (completeProduct y))
      (fun xi y => amplitude I xi*frequencyMode I K xi y) (fun y _ => h y)

def tail (K : ℕ) : ℂ :=
  ∫ xi in outsideCube (size I.j) (H I.P.N order),amplitude I xi*fullMode I K xi

def otherBand (K : ℕ) : ℂ :=
  ∫ xi in (outsideCube (size I.j) (H I.P.N order))ᶜ,amplitude I xi*otherMode I K xi

/-- On a short fibre the untruncated contribution consists of the exact
whole-modulus tail and the retained integral of all surviving words. -/
def remainingFibre (K : ℕ) : ℂ :=
  if I.U≤I.x^(1/16:ℝ) then tail I K+otherBand I K else original I K

private theorem fibre_difference (K : ℕ) (hkap : kap<1) {E : ℝ} (hE : 0≤E)
    (h : I.U≤I.x^(1/16:ℝ) → ∀ xi∈(outsideCube (size I.j) (H I.P.N order))ᶜ,
      ‖fullMode I K xi-otherMode I K xi‖≤(scalar I*modulusCost I)*E) :
    ‖original I K-remainingFibre I K‖≤((∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I)*E := by
  let V := outsideCube (size I.j) (H I.P.N order)
  let f := fullMode I K
  let g := otherMode I K
  let a := amplitude I
  let e := (scalar I*modulusCost I)*E
  have hv : MeasurableSet V := measurableSet_outsideCube _ _
  have hf : Integrable (fun xi => a xi*f xi) :=
    integrable_kernel I K (fun n => ∑ q∈products I.P,(free I.P q:ℂ)*residueKernel q I.P.N n)
  have hg : Integrable (fun xi => a xi*g xi) := integrable_kernel I K (otherKernel I.P I.x I.U zeta)
  have ha : Integrable a := amplitude_integrable I
  have hs := (scalar_cost I hkap).1.le
  have hm : 0≤modulusCost I := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have he : 0≤e := mul_nonneg (mul_nonneg hs hm) hE
  have ha0 : 0≤∫ xi,‖amplitude I xi‖ := integral_nonneg (fun _ => norm_nonneg _)
  by_cases short : I.U≤I.x^(1/16:ℝ)
  · have parts : original I K=tail I K+retained I K := by
      rw [original_eq_fourier,retained_eq_band]
      exact (integral_add_compl hv hf).symm
    rw [remainingFibre,if_pos short,parts]
    rw [show tail I K+retained I K-(tail I K+otherBand I K)=retained I K-otherBand I K by ring,
      retained_eq_band]
    change ‖(∫ xi in Vᶜ,a xi*f xi)-(∫ xi in Vᶜ,a xi*g xi)‖≤_
    rw [←integral_sub hf.integrableOn hg.integrableOn]
    calc
      _≤∫ xi in Vᶜ,‖a xi‖*e := by
        apply norm_integral_le_of_norm_le (ha.norm.mul_const e).integrableOn
        filter_upwards [ae_restrict_mem (μ:=volume) hv.compl] with xi hxi
        rw [←mul_sub,norm_mul]
        exact mul_le_mul_of_nonneg_left (h short xi hxi) (norm_nonneg _)
      _=(∫ xi in Vᶜ,‖a xi‖)*e := integral_mul_const e _
      _≤(∫ xi,‖a xi‖)*e :=
        mul_le_mul_of_nonneg_right (setIntegral_le_integral ha.norm
          (Eventually.of_forall (fun xi => norm_nonneg (a xi)))) he
      _=_ := by dsimp only [a,e]; ring
  · rw [remainingFibre,if_neg short,sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg ha0 hs) hm) hE

def remainingRow (K : ℕ) : ℂ :=
  ∑ c∈(liveComplements I).attach,
    P5Z.SmoothChartHBDyadicPartition.scalar I.j.val*remainingFibre (onComplement I c) K

/-- The signed source64 rectangle, including its original HB coefficient.
Its complementary blocks are the full live subbank at cap 2N. The local
precision A+82 pays the L1, role, three modulus-owner and one complement
costs from the actual row inventory. -/
theorem exists_live_row_cost (K order A : ℕ) (omega T : ℝ) (ho : 0<omega)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ N : ℕ in atTop,∀ I : Index order kap zeta kap0,
      I.P.N=N → I.P.omega=omega → I.P.T=T → 0≤I.P.e → (I.P.e:ℝ)≤1/2048 →
      0<I.P.q → I.P.T≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      ‖P5Z.SmoothChartHBDyadicPartition.scalar I.j.val*
        occurrenceAtom kap 6 I.P.N I.cj K kap0 I.j.val I.bs
          (products I.P) (fun q => (free I.P q:ℂ))-remainingRow I K‖≤
        C*N/(Real.log (N:ℝ))^A := by
  let p := A+82
  obtain ⟨D,hD,HM⟩ := exists_mode_cost K order p (by dsimp only [p]; omega)
    hkap hz hz0 hk hkz ht ht1
  obtain ⟨B,hB,HB⟩ := live_row_amplitude_cost omega T ho
  have hh : 0≤heightConstant := zero_le_one.trans heightConstant_one_le
  refine ⟨B*heightConstant^82*D,by positivity,?_⟩
  filter_upwards [HM,eventually_height_le_log,eventually_ge_atTop (2:ℕ)] with N Hmode Hheight hNN
  intro I hn hw hT he he' hq hmesh hell hell'
  subst N
  have hN : 1<I.P.N := by omega
  have hnR : 1<(I.P.N:ℝ) := by exact_mod_cast hN
  let L := Real.log (I.P.N:ℝ)
  let E := D*I.P.N/L^p
  have hL : 0<L := Real.log_pos hnR
  have hE : 0≤E := div_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg hL.le _)
  have hrest := HB order kap zeta kap0 I hkap hN hw hT he (by linarith only [hell',hz0])
  have hlog : Real.log ((I.P.N:ℝ)+2)≤profileHeight I.P.N := by
    have h := Real.log_le_log (by positivity : 0<(I.P.N:ℝ)+2)
      (show (I.P.N:ℝ)+2≤8*(I.P.N:ℝ)+8 by linarith)
    dsimp only [profileHeight]
    linarith only [h]
  have hscale : logScale (I.P.N:ℝ)≤profileHeight I.P.N := by
    unfold logScale profileHeight
    apply add_le_add_left
    exact Real.log_le_log (mul_pos (by norm_num) (zero_lt_one.trans hnR)) (by linarith)
  have l0 : 0≤Real.log ((I.P.N:ℝ)+2) := Real.log_nonneg (by linarith)
  have s0 : 0≤logScale (I.P.N:ℝ) := zero_le_one.trans (logScale_one_le hnR.le)
  have v0 : 0≤profileHeight I.P.N := zero_le_one.trans (height_one_le _)
  have rest : liveRowCost I≤B*heightConstant^82*L^82 := by
    apply hrest.trans
    calc
      _≤B*profileHeight I.P.N^72*profileHeight I.P.N^6*profileHeight I.P.N^4 :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ l0 hlog 72) hB) (pow_nonneg v0 6))
          (pow_le_pow_left₀ s0 hscale 4) (pow_nonneg s0 4)
          (mul_nonneg (mul_nonneg hB (pow_nonneg v0 72)) (pow_nonneg v0 6))
      _=B*profileHeight I.P.N^82 := by ring
      _≤B*(heightConstant*L)^82 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ v0 Hheight _) hB
      _=_ := by rw [mul_pow]; ring
  have one (c : {c // c∈liveComplements I}) :
      ‖original (onComplement I c) K-remainingFibre (onComplement I c) K‖≤
        ((∫ xi,‖amplitude (onComplement I c) xi‖)*scalar (onComplement I c)*
          modulusCost (onComplement I c))*E := by
    apply fibre_difference (onComplement I c) K hkap hE
    intro short xi hxi
    exact Hmode (atMode (onComplement I c) xi hxi) rfl he he' hq hmesh hell hell' short
  rw [occurrenceAtom_partition I K hkap,Finset.mul_sum,remainingRow,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑ c∈(liveComplements I).attach,fibreCost (onComplement I c)*E := by
      apply Finset.sum_le_sum
      intro c _
      rw [←mul_sub,norm_mul]
      exact (mul_le_mul_of_nonneg_left (one c) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    _=liveRowCost I*E := by rw [liveRowCost,Finset.sum_mul]
    _≤(B*heightConstant^82*L^82)*E := mul_le_mul_of_nonneg_right rest hE
    _=(B*heightConstant^82*D)*I.P.N/L^A := by
      dsimp only [E,p]
      rw [pow_add]
      field_simp [hL.ne'] <;> ring

/-- The same occupied row in the original sieve normalization. -/
theorem eventually_live_row_removed (K order : ℕ) (omega T eta : ℝ) (ho : 0<omega) (heta : 0<eta)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index order kap zeta kap0,
      I.P.N=N → I.P.omega=omega → I.P.T=T → 0≤I.P.e → (I.P.e:ℝ)≤1/2048 →
      0<I.P.q → I.P.T≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      ‖P5Z.SmoothChartHBDyadicPartition.scalar I.j.val*
        occurrenceAtom kap 6 I.P.N I.cj K kap0 I.j.val I.bs
          (products I.P) (fun q => (free I.P q:ℂ))-remainingRow I K‖≤eta*singularNormalization N := by
  obtain ⟨C,_,Hrow⟩ := exists_live_row_cost K order 3 omega T ho hkap hz hz0 hk hkz ht ht1
  filter_upwards [Hrow,p5z_eventually_logCube_le_singularNormalization C eta heta] with N Hrow Hpay
  intro I hn hw hT he he' hq hm hell hell'
  exact (Hrow I hn hw hT he he' hq hm hell hell').trans Hpay

end
end ImbalancedChen.P1OriginalSingletonShortMediumLiveRow
