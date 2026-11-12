import ImbalancedChen.P4BOriginalRankTwoChartScales
import ImbalancedChen.P2GammaPrimeLocalConductorSaving
import ImbalancedChen.P2GammaRetainedActualNorms

/-! Actual two-prime rectangles for the selected original dyadic label.
Only the first coordinate is split, at its shared right-closed endpoint. -/
namespace ImbalancedChen.P4BOriginalRankTwoConductorWindows
noncomputable section
open Classical Filter Set MeasureTheory
open scoped BigOperators Topology
open P4BOriginalRankTwoChartScales
open P5Z.ActualEtaPsiOccurrenceBudget (psi psi_smooth)
open P2GammaVariablePrimeProfile P2GammaPrimeTargetDeletion P2GammaPrimeCharacterSW
open P2GammaSmallConductorIntervalBridge P2GammaOriginalCartesianMask
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping P2GammaPrimeSmallConductorSum
open P2GammaRetainedActualNorms (paddedRow_energy primeInterval_subset_cap)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def profile (V y : ℝ) : ℂ := (psi (y/V):ℝ)
def primeRow (V : ℝ) := targetDeleted 1 (profilePrimeCoefficient (profile V))
def headScale (left : Bool) (u : ℝ) := if left then u/2 else u

theorem row_apply (V : ℝ) (p : ℕ) :
    primeRow V p=if p.Prime then profile V p else 0 := by
  by_cases hp : p.Prime <;> simp [primeRow,targetDeleted,profilePrimeCoefficient,primeSWBeta,hp]

theorem profile_norm (u y : ℝ) : ‖profile u y‖≤1 := by
  simpa only [profile,Complex.norm_real,Real.norm_eq_abs] using psi_size (y/u)

private theorem profile_deriv (V y : ℝ) :
    HasDerivAt (profile V) ((deriv psi (y/V)/V:ℝ):ℂ) y := by
  have h := (psi_smooth.differentiable (by simp) (y/V)).hasDerivAt.comp y
    ((hasDerivAt_id y).div_const V)
  simpa [profile,div_eq_mul_inv] using h.ofReal_comp

/-- The original bump is dilated together with its interval. Its
derivative contributes a single absolute constant at every scale. -/
theorem exists_profile_cost :
    ∃ W : ℝ,1≤W ∧ ∀ V u v : ℝ,0<V → V/2≤u → u≤v → v≤2*V →
      (∀ t∈Icc u v,DifferentiableAt ℝ (profile V) t) ∧
      IntegrableOn (deriv (profile V)) (Icc u v) ∧ profileAbelNorm (profile V) u v≤W := by
  have dcont : Continuous (deriv psi) := psi_smooth.continuous_deriv (by simp)
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (1/2:ℝ) 2)).exists_bound_of_continuousOn
    dcont.continuousOn
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨1+2*D,by linarith,?_⟩
  intro V u v hV hlo huv hhi
  have hc : Continuous (deriv (profile V)) := by
    have he : deriv (profile V)=fun t => ((deriv psi (t/V)/V:ℝ):ℂ) :=
      funext fun t => (profile_deriv V t).deriv
    rw [he]
    exact Complex.continuous_ofReal.comp ((dcont.comp (continuous_id.div_const V)).div_const V)
  refine ⟨fun t _ => (profile_deriv V t).differentiableAt,hc.integrableOn_Icc,?_⟩
  have hi : (∫ t in Ioc u v,‖deriv (profile V) t‖)≤2*D := by
    calc
      _ ≤ ∫ _t in Ioc u v,D/V := by
        apply setIntegral_mono_on (hc.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
        intro t ht
        have ht' : t/V∈Icc (1/2:ℝ) 2 :=
          ⟨(le_div_iff₀ hV).mpr (by linarith [ht.1]),(div_le_iff₀ hV).mpr (ht.2.trans hhi)⟩
        rw [(profile_deriv V t).deriv,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hV]
        exact div_le_div_of_nonneg_right ((hB _ ht').trans (le_max_left _ _)) hV.le
      _ = (v-u)*(D/V) := by
        rw [← intervalIntegral.integral_of_le huv,intervalIntegral.integral_const,smul_eq_mul]
      _ ≤ (2*V)*(D/V) := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hD hV.le)
      _ = _ := by field_simp [hV.ne']
  exact add_le_add (profile_norm V v) hi

theorem row_cost {V u v L : ℝ} (hL : 0≤L) (hhi : v≤2*L) :
    rowMass (primeSWInterval u v) (primeRow V)≤2*L ∧
    rowEnergy (paddedRow (primeSWInterval u v) (primeRow V)) 0 (Nat.floor (2*L))≤2*L := by
  have hS := primeInterval_subset_cap (u:=u) hhi
  have hcount : ((primeSWInterval u v).card:ℝ)≤2*L := by
    refine le_trans ?_ (Nat.floor_le (show 0≤2*L by linarith))
    exact_mod_cast (show (primeSWInterval u v).card≤Nat.floor (2*L) by
      simpa using Finset.card_le_card hS)
  have hunit (p : ℕ) : ‖primeRow V p‖≤1 := by
    rw [row_apply]
    split_ifs
    · exact profile_norm _ _
    · simp
  constructor
  · exact (Finset.sum_le_sum (s:=primeSWInterval u v) (fun p _ => hunit p)).trans
      (by simpa using hcount)
  · rw [paddedRow_energy _ _ _ hS]
    calc
      _ ≤ ∑ _p∈primeSWInterval u v,(1:ℝ)^2 :=
        Finset.sum_le_sum (fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hunit p) 2)
      _ ≤ _ := by simpa using hcount

def rectangle (left : Bool) (N d : ℕ) : ℂ :=
  let u := U N
  let M := headScale left u
  naturalRectangleDiscrepancy (primeSWInterval M (2*M)) (primeSWInterval (4*u) (16*u))
    (primeRow u) (primeRow (8*u)) N d

def modulusCap (N : ℕ) := Nat.floor ((N:ℝ)^(2/5:ℝ))

/-- The conductor result is called at local x=M*(8U), on the original
inverse target, with deletion parameter one. Its constants precede both
physical rectangles and the chosen subset of complete moduli. -/
theorem eventually_rectangles (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d ∧ d≤modulusCap N ∧ N.Coprime d ∧ |c d|≤1) →
      ∀ left : Bool,‖∑ d∈S,(c d:ℂ)*rectangle left N d‖≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  obtain ⟨W,hW,HP⟩ := exists_profile_cost
  obtain ⟨K,hK,x0,hx0,H⟩ := P2GammaPrimeLocalConductorSaving.exists_actual_prime_local_conductor_saving
    ((A+1:ℕ):ℝ) 0 0 (1/4) (1/20) 0 W 0 2 2 2 2 (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop
    (K*2^(A+1)/delta)
  have HN := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop
    (max (1024*x0) (4096*64^2))
  filter_upwards [eventually_ge_atTop (2^12:ℕ),eventually_power 1024 (1/10:ℝ) (by norm_num),
    Hlog,HN] with N hN hten hlog hNbig
  intro S c hS left
  let u := U N
  let M := headScale left u
  let v := 8*u
  let x := M*v
  have hu := U_pos N
  change 0<u at hu
  obtain ⟨_,hl,hh⟩ := scales hN
  change 1024*u^2≤(N:ℝ) at hl
  change (N:ℝ)<4096*u^2 at hh
  have hu64 : 64≤u := by
    have h := (le_max_right (1024*x0) (4096*64^2)).trans hNbig
    by_contra! hlt
    have hs := mul_self_lt_mul_self hu.le hlt
    nlinarith
  have hm : u/2≤M ∧ M≤u := by cases left <;> simp [M,headScale] <;> linarith
  have hm0 : 0<M := by linarith
  have hxlo : 4*u^2≤x := by
    have h := mul_le_mul_of_nonneg_right hm.1 (by positivity : 0≤8*u)
    change 4*u^2≤M*(8*u)
    nlinarith only [h]
  have hxhi : x≤8*u^2 := by
    have h := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0≤8*u)
    change M*(8*u)≤8*u^2
    nlinarith only [h]
  have hnx : (N:ℝ)/1024≤x := by linarith
  have hxn : x≤(N:ℝ) := by linarith
  have hx0' : x0≤x := by linarith [(le_max_left (1024*x0) (4096*64^2)).trans hNbig]
  have hx : 1<x := hx0.trans_le hx0'
  have hpM : x^(1/4:ℝ)≤M := by
    have hsq : 8*u^2≤(u/2)^4 := by
      have h1 : 128≤u^2 := by nlinarith [sq_nonneg (u-64)]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg u)
      nlinarith
    have H' := Real.rpow_le_rpow (by linarith : 0≤x) (hxhi.trans hsq) (by norm_num : 0≤(1/4:ℝ))
    have he : ((u/2)^4)^(1/4:ℝ)=u/2 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0≤u/2)]
      norm_num
    exact (H'.trans_eq he).trans hm.1
  have hpV : x^(1/4:ℝ)≤v := hpM.trans (by dsimp [v]; linarith [hm.2])
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hnr := zero_lt_one.trans hNr
  have hn9 : (N:ℝ)^(9/10:ℝ)≤x := by
    have he : (N:ℝ)^(9/10:ℝ)*(N:ℝ)^(1/10:ℝ)=(N:ℝ) := by
      rw [← Real.rpow_add hnr]; norm_num
    have H' := mul_lt_mul_of_pos_left hten (Real.rpow_pos_of_pos hnr (9/10))
    linarith
  have hQ : (modulusCap N:ℝ)≤x^(1/2-1/20:ℝ) := by
    apply (Nat.floor_le (Real.rpow_nonneg hnr.le (2/5))).trans
    have H' := Real.rpow_le_rpow (Real.rpow_nonneg hnr.le _) hn9
      (by norm_num : 0≤(1/2-1/20:ℝ))
    rw [← Real.rpow_mul hnr.le] at H'
    exact (Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num)).trans H'
  have hlogx : Real.log (N:ℝ)/2≤Real.log x := by
    have hh' := Real.log_le_log (Real.rpow_pos_of_pos hnr (9/10)) hn9
    rw [Real.log_rpow hnr] at hh'
    linarith [Real.log_nonneg hNr.le]
  have hP := primeInterval_subset_cap (u:=M) (le_refl (2*M))
  have hT := primeInterval_subset_cap (u:=4*u) (M:=v) (v:=16*u) (by dsimp [v]; linarith)
  obtain ⟨hdiff,hint,hcost⟩ := HP u M (2*M) hu hm.1 (by linarith) (by linarith [hm.2])
  have ha := (row_cost (V:=u) (u:=M) (L:=M) hm0.le (le_refl (2*M))).2
  have hb := row_cost (V:=v) (u:=4*u) (v:=16*u) (L:=v) (by dsimp [v]; positivity)
    (by dsimp [v]; linarith)
  let Q := modulusCap N
  let P := Nat.floor (2*M)
  let V := Nat.floor (2*v)
  let T := primeSWInterval (4*u) (16*u)
  let f := profile u
  let g := primeRow v
  have hmain := H x M v M (2*M) hx0' rfl hpM hpV le_rfl (by linarith) le_rfl f
    hdiff hint (by simpa using hcost) (fun y _ => by simpa [f] using (profile_norm u y).trans hW)
    1 (by norm_num) (by simp) P V Q T g hP hT (fun d => ((N:ZMod d)⁻¹))
    (by simpa [primeRow,f] using (ha.trans (show 2*M≤2^2*M by linarith)))
    (by simpa [T,g] using (hb.2.trans (show 2*v≤2^2*v by dsimp [v]; linarith)))
    (by simpa [T,g] using hb.1)
    ((Nat.floor_le (by positivity : 0≤2*M)).trans (by linarith))
    ((Nat.floor_le (by dsimp [v]; positivity : 0≤2*v)).trans (by dsimp [v]; linarith))
    hQ
  have hsub : S⊆(Finset.Icc 1 Q).filter (fun d => N.Coprime d) := by
    intro d hd'
    obtain ⟨hp,hl',hc,_⟩ := hS d hd'
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp,hl'⟩,hc⟩
  have hrect := natural_rectangle_norm_sum_le_character_sum
    (primeSWInterval M (2*M)) T (primeRow u) g P V N Q hP hT
  have hbudget : K*x/(Real.log x)^(A+1)≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
    have hL := Real.log_pos hx
    have hNlog := Real.log_pos hNr
    have hpow := pow_le_pow_left₀ (div_nonneg hNlog.le (by norm_num : (0:ℝ)≤2)) hlogx (A+1)
    rw [div_pow] at hpow
    have hcoef := (div_le_iff₀ hd).mp hlog
    apply (div_le_iff₀ (pow_pos hL (A+1))).mpr
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hNlog A)]
    calc
      _ ≤ K*(N:ℝ)*Real.log (N:ℝ)^A := by gcongr
      _ ≤ delta*(N:ℝ)*((Real.log (N:ℝ))^(A+1)/(2:ℝ)^(A+1)) := by
        rw [← mul_div_assoc,le_div_iff₀ (by positivity : (0:ℝ)<2^(A+1)),pow_succ (Real.log (N:ℝ))]
        have hp := mul_le_mul_of_nonneg_right hcoef (by positivity : 0≤(N:ℝ)*Real.log (N:ℝ)^A)
        nlinarith only [hp]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ d∈S,‖(c d:ℂ)*rectangle left N d‖ := norm_sum_le _ _
    _ ≤ ∑ d∈S,‖rectangle left N d‖ := by
      apply Finset.sum_le_sum
      intro d hd'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (hS d hd').2.2.2 (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ∑ d∈(Finset.Icc 1 Q).filter (fun d => N.Coprime d),‖rectangle left N d‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ ≤ _ := hrect.trans (hmain.trans (by simpa only [Real.rpow_natCast] using hbudget))

end
end ImbalancedChen.P4BOriginalRankTwoConductorWindows
