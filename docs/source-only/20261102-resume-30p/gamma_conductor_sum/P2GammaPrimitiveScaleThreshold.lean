import ImbalancedChen.P2GammaConductorScaleThreshold

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

The complete scale is x=M*N. M and N are the original support scales,
not the lengths of the possibly short prime subintervals. The only row
inputs are the two original L2 energies. In particular, no combined energy,
dyadic estimate, small-conductor estimate or discrepancy bound is a premise.
The fixed below-half gap epsilon is arbitrary; it is not replaced by .05.
-/

namespace ImbalancedChen.P2GammaPrimitiveScaleThreshold
noncomputable section
open scoped Classical BigOperators
open Filter
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping
open P2GammaDyadicConductorSum P2GammaConductorScaleThreshold

/-- The literal polynomial coefficient of O's weaker large sieve. -/
def highCoefficient (ea eb c : ℝ) : ℝ :=
  ea*eb*(8*(c^2+2*c)+
    8*(lsLogCoefficient+1)*dyadicCountCoefficient*(c^2+2*c)+
    64*lsLogCoefficient)

theorem highCoefficient_nonneg {ea eb c : ℝ}
    (hea : 0≤ea) (heb : 0≤eb) (hc : 0≤c) :
    0≤highCoefficient ea eb c := by
  have := lsLogCoefficient_pos
  have := dyadicCountCoefficient_pos
  unfold highCoefficient
  positivity

/-- Derive all combined norm/length inputs from the actual two support
scales and the two separate L2 bounds. The interval caps need only be upper
bounds. Neither La nor Lb has a positive-length lower bound. Squared fixed
constants are a harmless parameterization of arbitrary nonnegative ones. -/
theorem primitive_scale_bounds
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb C : ℕ)
    (x M N l eta ea eb c : ℝ)
    (hx : 0<x) (hl : 0≤l) (hea : 0≤ea) (heb : 0≤eb) (hc : 0≤c)
    (hMN : M*N=x) (hMpower : x^eta≤M) (hNpower : x^eta≤N)
    (hLa : (La : ℝ)≤c^2*M) (hLb : (Lb : ℝ)≤c^2*N)
    (hEa : rowEnergy a Ma La≤ea^2*M*l^C)
    (hEb : rowEnergy b Mb Lb≤eb^2*N*l^C) :
    energyProduct a b Ma Mb La Lb≤ea*eb*Real.sqrt x*l^C ∧
      Real.sqrt La*Real.sqrt Lb≤(c^2+2*c)*Real.sqrt x ∧
      Real.sqrt La+Real.sqrt Lb≤
        (c^2+2*c)*Real.sqrt x/x^(eta/2) := by
  have hM : 0<M := (Real.rpow_pos_of_pos hx eta).trans_le hMpower
  have hN : 0<N := (Real.rpow_pos_of_pos hx eta).trans_le hNpower
  have hroots : Real.sqrt M*Real.sqrt N=Real.sqrt x := by
    rw [← Real.sqrt_mul hM.le,hMN]
  have hrootLa : Real.sqrt La≤c*Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt hM.le]
    exact hLa
  have hrootLb : Real.sqrt Lb≤c*Real.sqrt N := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt hN.le]
    exact hLb
  have ht : 0<x^(eta/2) := Real.rpow_pos_of_pos hx _
  have htsq : (x^(eta/2))^2=x^eta := by
    rw [pow_two,← Real.rpow_add hx]
    congr 1
    ring
  have htM : x^(eta/2)≤Real.sqrt M := by
    apply (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mp
    rw [htsq,Real.sq_sqrt hM.le]
    exact hMpower
  have htN : x^(eta/2)≤Real.sqrt N := by
    apply (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mp
    rw [htsq,Real.sq_sqrt hN.le]
    exact hNpower
  have hrootM : Real.sqrt M*x^(eta/2)≤Real.sqrt x := by
    calc
      _ ≤ Real.sqrt M*Real.sqrt N :=
        mul_le_mul_of_nonneg_left htN (Real.sqrt_nonneg _)
      _ = _ := hroots
  have hrootN : Real.sqrt N*x^(eta/2)≤Real.sqrt x := by
    calc
      _ ≤ Real.sqrt N*Real.sqrt M :=
        mul_le_mul_of_nonneg_left htM (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_comm,hroots]
  refine ⟨?_,?_,?_⟩
  · apply (sq_le_sq₀ (energyProduct_nonneg _ _ _ _ _ _) (by positivity)).mp
    calc
      _ = rowEnergy a Ma La*rowEnergy b Mb Lb := by
        unfold energyProduct
        rw [mul_pow,Real.sq_sqrt (rowEnergy_nonneg _ _ _),
          Real.sq_sqrt (rowEnergy_nonneg _ _ _)]
      _ ≤ (ea^2*M*l^C)*(eb^2*N*l^C) :=
        mul_le_mul hEa hEb (rowEnergy_nonneg _ _ _) (by positivity)
      _ = (ea*eb*Real.sqrt x*l^C)^2 := by
        rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hx.le,← hMN]
        ring
  · calc
      _ ≤ (c*Real.sqrt M)*(c*Real.sqrt N) :=
        mul_le_mul hrootLa hrootLb (Real.sqrt_nonneg _) (by positivity)
      _ = c^2*Real.sqrt x := by rw [← hroots]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg x)
  · apply (le_div_iff₀ ht).mpr
    calc
      _ ≤ (c*Real.sqrt M+c*Real.sqrt N)*x^(eta/2) :=
        mul_le_mul_of_nonneg_right (add_le_add hrootLa hrootLb) ht.le
      _ = c*(Real.sqrt M*x^(eta/2)+Real.sqrt N*x^(eta/2)) := by ring
      _ ≤ c*(Real.sqrt x+Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (add_le_add hrootM hrootN) hc
      _ = (2*c)*Real.sqrt x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg c])
        (Real.sqrt_nonneg x)

/-- A common threshold at the complete original scale, with an arbitrary
fixed below-half power gap. All rows, their integer translations, endpoints,
support caps, characters, quotients and residues follow the threshold. The
energy exponent C and all fixed constants precede it. -/
theorem exists_primitive_high_conductor_threshold
    (A C : ℕ) (eta epsilon ea eb c : ℝ)
    (heta : 0<eta) (hepsilon : 0<epsilon)
    (hea : 0≤ea) (heb : 0≤eb) (hc : 0≤c) :
    ∃ x0 : ℝ,1<x0 ∧ ∀ x : ℝ,x0≤x →
      ∀ M N : ℝ,M*N=x → x^eta≤M → x^eta≤N →
      ∀ (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q : ℕ),
      (La : ℝ)≤c^2*M → (Lb : ℝ)≤c^2*N →
      rowEnergy a Ma La≤ea^2*M*(Real.log x)^C →
      rowEnergy b Mb Lb≤eb^2*N*(Real.log x)^C →
      (Q : ℝ)≤x^((1 : ℝ)/2-epsilon) →
      highConductorTotal a b Ma Mb La Lb Q
        (cutoffExponent (1+Real.log x) (A+C+3)) ≤
      highCoefficient ea eb c*x/(Real.log x)^A := by
  have hlarge : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ (1+Real.log x)^(A+C+3)≤x^(eta/2) ∧
        (1+Real.log x)^(A+C+3)≤x^epsilon ∧ 1≤x := by
    filter_upwards [eventually_one_add_log_power_le_fixed_power (A+C+3)
      (eta/2) (by linarith),
      eventually_one_add_log_power_le_fixed_power (A+C+3) epsilon hepsilon,
      eventually_ge_atTop (1 : ℝ)] with x hx hy hx1
    exact ⟨hx.1,hx.2,hy.2,hx1⟩
  obtain ⟨x1,hx1⟩ := eventually_atTop.mp hlarge
  refine ⟨max 2 x1,by linarith [le_max_left (2 : ℝ) x1],?_⟩
  intro x hx M N hMN hM hN a b Ma Mb La Lb Q hLa hLb hEa hEb hQ
  obtain ⟨hl,hpow,hpowLevel,hxge⟩ := hx1 x ((le_max_right _ _).trans hx)
  have hxpos : 0<x := zero_lt_one.trans_le hxge
  have hlpos : 0<Real.log x := zero_lt_one.trans_le hl
  have hll : 1≤1+Real.log x := by linarith
  have hMpos := (Real.rpow_pos_of_pos hxpos eta).trans_le hM
  have hNpos := (Real.rpow_pos_of_pos hxpos eta).trans_le hN
  have hEa' : rowEnergy a Ma La≤ea^2*M*(1+Real.log x)^C := by
    exact hEa.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlpos.le (by linarith) C) (by positivity))
  have hEb' : rowEnergy b Mb Lb≤eb^2*N*(1+Real.log x)^C := by
    exact hEb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlpos.le (by linarith) C) (by positivity))
  obtain ⟨hE,hproduct,hlength0⟩ := primitive_scale_bounds a b Ma Mb La Lb C
    x M N (1+Real.log x) eta ea eb c hxpos (by positivity) hea heb hc
    hMN hM hN hLa hLb hEa' hEb'
  have hg : logGauge Q≤1+Real.log x := by
    have hQx : (Q : ℝ)≤x := hQ.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hxge
        (show (1 : ℝ)/2-epsilon≤1 by linarith))
    unfold logGauge
    exact add_le_add_left (Real.log_le_log (by positivity) (max_le hxge hQx)) 1
  have hlevel : (Q : ℝ)≤Real.sqrt x/(1+Real.log x)^(A+C+3) := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0<1+Real.log x) _)).mpr
    calc
      _ ≤ x^((1 : ℝ)/2-epsilon)*x^epsilon :=
        mul_le_mul hQ hpowLevel (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = Real.sqrt x := by
        rw [← Real.rpow_add hxpos]
        rw [show (1 : ℝ)/2-epsilon+epsilon=1/2 by ring,Real.sqrt_eq_rpow]
  have hlength : Real.sqrt La+Real.sqrt Lb≤
      (c^2+2*c)*Real.sqrt x/(1+Real.log x)^(A+C+3) :=
    hlength0.trans (div_le_div_of_nonneg_left (by positivity)
      (pow_pos (by positivity : 0<1+Real.log x) _) hpow)
  have hh := highConductorTotal_scale_le a b Ma Mb La Lb Q
    (cutoffExponent (1+Real.log x) (A+C+3)) A C x (1+Real.log x)
    (ea*eb) (c^2+2*c) hxpos.le hll (mul_nonneg hea heb) (by positivity)
    hg hE hproduct hlength (cutoffExponent_bounds _ hll _).1 hlevel
  change highConductorTotal a b Ma Mb La Lb Q
    (cutoffExponent (1+Real.log x) (A+C+3)) ≤
      highCoefficient ea eb c*x/(1+Real.log x)^A at hh
  exact hh.trans (div_le_div_of_nonneg_left
    (mul_nonneg (highCoefficient_nonneg hea heb hc) hxpos.le)
    (pow_pos hlpos _) (pow_le_pow_left₀ hlpos.le (by linarith) A))

end
end ImbalancedChen.P2GammaPrimitiveScaleThreshold
