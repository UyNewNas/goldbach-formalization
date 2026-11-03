import ImbalancedChen.P2EnhancedBadGamma5ArithmeticGeometry

/-! SOURCE ONLY / UNCOMPILED.
The original constant-a0 rough source, its arithmetic unit atom, and
its same-Theta positive marked payment. The analytic global omega cap,
scalar rough estimate and genuine reciprocal quadrature are supplied
theorems, not licence hypotheses. No PP or K/4 count licence is asserted.
-/
namespace ImbalancedChen.P2EnhancedBadGamma5CostTheta
noncomputable section
open Real Finset Set Filter MeasureTheory Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2EnhancedNonunitWordMass (rawScale)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2SeedOmegaLiteralFibre (a0 a2 s0 omegaCap badArgument)
open P2SeedOmegaLiteralFunctional (badMassLog)
open P2EnhancedBadGamma5PrimeQuadrature P2EnhancedBadGamma5ArithmeticGeometry
open P2EnhancedBadGamma5ConstantCutoff
open scoped Classical BigOperators Topology

def badRawCost : ℝ := (omegaCap/a0)*badMassLog

theorem actual_bad_argument_cap {N d : ℕ} {Q : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hR : 1 < Q/d) (ha : 2 ≤ trueAlpha N Q d)
    {l : List ℕ} (hl : l ∈ badLabels N Q d) :
    let x := (N : ℝ)/(d*l.prod : ℕ)
    let z := cutoff Q d (227/50)
    z ≤ x ∧ buchstab (log x/log z) ≤ omegaCap := by
  have hpair := (mem_filter.mp hl).1
  have hdata := pair_data hpair
  have hp := pair_primes hpair
  let p := l.getD 0 0
  let q := l.getD 1 0
  have hel : l=[p,q] := pair_eq hpair
  have hwp := mem_primeWindow.mp (hdata.2.2 p (by rw [hel]; simp))
  have hwq := mem_primeWindow.mp (hdata.2.2 q (by rw [hel]; simp))
  have hu : coordinate (Q/d) p ≤ a2 :=
    HighNonunit.log_coordinate_upper hR hp.1.pos hwp.2.2.2.le
  have hv : coordinate (Q/d) q ≤ a2 :=
    HighNonunit.log_coordinate_upper hR hp.2.pos hwq.2.2.2.le
  have hfloor := P2SeedOmegaLiteralFibre.bad_argument_lower ha hu hv
  have harg : log ((N : ℝ)/(d*l.prod : ℕ))/log (cutoff Q d (227/50)) =
      badArgument (trueAlpha N Q d) (coordinate (Q/d) p) (coordinate (Q/d) q) := by
    rw [hel]
    simp only [List.prod_cons,List.prod_nil,mul_one]
    rw [show d*(p*q)=d*p*q by ring,actual_constant_argument hN hd hp.1.pos hp.2.pos hR]
    norm_num [badArgument,a0,s0] <;> ring
  have hz : 0 < cutoff Q d (227/50) := by
    rw [original_cutoff]; exact rpow_pos_of_pos (zero_lt_one.trans hR) _
  have hzlog : 0 < log (cutoff Q d (227/50)) := by
    rw [original_cutoff_log hR]
    exact mul_pos (by norm_num [a0]) (log_pos hR)
  have hx : 0 < (N : ℝ)/(d*l.prod : ℕ) :=
    div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr (Nat.mul_pos hd (pair_prod_pos hpair)))
  have hlog : 1 ≤ log ((N : ℝ)/(d*l.prod : ℕ))/log (cutoff Q d (227/50)) := by
    rw [harg]; linarith
  constructor
  · apply (log_le_log_iff hz hx).mp
    simpa only [one_mul] using (le_div_iff₀ hzlog).mp hlog
  · rw [harg]
    exact P2SeedOmegaGlobalEnvelope.actual_buchstab_global_cap (by linarith)

theorem scalar_bad_upper {eta tau : ℝ} (heta : 0 < eta) (htau : 0 < tau) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ordinaryBadNonunit N Q d ≤
        rawScale N Q d*((omegaCap+tau)/a0)*labelReciprocal N Q d := by
  obtain ⟨T,hT,hscalar⟩ := NonunitRoughUniform.uniform_upper
    (mul_pos heta (show 0 < a0 by norm_num [a0])) htau
  refine ⟨T,hT,?_⟩
  intro N hN Q d hd hscale ha
  have hN4 := hT.trans hN
  have hN0 : 0 < N := by omega
  have hR : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le hscale
  have hzfloor : (N : ℝ)^(eta*a0) ≤ cutoff Q d (227/50) := by
    rw [original_cutoff,rpow_mul (Nat.cast_nonneg N)]
    exact rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) hscale (by norm_num [a0])
  unfold ordinaryBadNonunit labelReciprocal
  rw [mul_sum]
  apply sum_le_sum
  intro l hl
  have hpair := (mem_filter.mp hl).1
  have hprod := pair_prod_pos hpair
  have hD := Nat.mul_pos hd hprod
  let x := (N : ℝ)/(d*l.prod : ℕ)
  let z := cutoff Q d (227/50)
  have hxN : x ≤ N := div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)
  obtain ⟨_,hu⟩ := hscalar N hN x z hxN hzfloor
  obtain ⟨hzx,hw⟩ := actual_bad_argument_cap hN0 hd hR ha hl
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _)
  have hlogz : 0 < log z := by
    rw [original_cutoff_log hR]
    exact mul_pos (by norm_num [a0]) (log_pos hR)
  have hmain : (omegaCap+tau)*x/log z =
      rawScale N Q d*((omegaCap+tau)/a0)*(1/(l.prod : ℝ)) := by
    dsimp [x,z,rawScale]
    rw [original_cutoff_log hR]
    push_cast
    field_simp [(Nat.cast_pos.mpr hd : (0 : ℝ) < d).ne',
      (Nat.cast_pos.mpr hprod : (0 : ℝ) < l.prod).ne',
      (log_pos hR).ne',show a0 ≠ 0 by norm_num [a0]]
    ring
  calc
    _ ≤ (buchstab (log x/log z)+tau)*x/log z := hu hzx
    _ ≤ (omegaCap+tau)*x/log z :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (add_le_add_right hw tau) hx0) hlogz.le
    _ = _ := hmain

/-- One original-N threshold precedes every physical Q,d. The bad pair
square has not been enlarged to a feedback triangle or reset to alpha=2. -/
theorem actual_bad_nonunit_upper {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ordinaryBadNonunit N Q d ≤ rawScale N Q d*(badRawCost+epsilon) := by
  let tau := epsilon*a0/1250
  let e := epsilon*a0/(2*omegaCap)
  have htau : 0 < tau := by dsimp [tau]; norm_num [a0]; positivity
  have heq : 0 < e := by dsimp [e]; norm_num [a0,omegaCap]; positivity
  obtain ⟨Ts,hTs,hs⟩ := scalar_bad_upper heta htau
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp ((reciprocal_quadrature heq).and reciprocal_mass_coarse)
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop R0)
  refine ⟨max Ts T0,hTs.trans (le_max_left _ _),?_⟩
  intro N hN Q d hd hscale ha
  have hNs := (le_max_left Ts T0).trans hN
  have hN4 := hTs.trans hNs
  have hR : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le hscale
  have hh := hR0 (Q/d) ((hT0 N ((le_max_right _ _).trans hN)).trans hscale)
  have hr := label_reciprocal_le_closed hd hR
  have hrec : labelReciprocal N Q d ≤ 625 := hr.trans hh.2
  have hquad : labelReciprocal N Q d ≤ badMassLog+e := by
    have h := (le_abs_self _).trans hh.1.le
    linarith
  have hc : (omegaCap+tau)/a0*labelReciprocal N Q d ≤ badRawCost+epsilon := by
    have hlead := mul_le_mul_of_nonneg_left hquad
      (show 0 ≤ omegaCap/a0 by norm_num [a0,omegaCap])
    have herror := mul_le_mul_of_nonneg_left hrec
      (show 0 ≤ tau/a0 by positivity)
    have hepay : (omegaCap/a0)*e=epsilon/2 := by
      dsimp [e]; field_simp [show a0 ≠ 0 by norm_num [a0],
        show omegaCap ≠ 0 by norm_num [omegaCap]]; ring
    have htpay : (tau/a0)*625=epsilon/2 := by
      dsimp [tau]; field_simp [show a0 ≠ 0 by norm_num [a0]]; ring
    rw [mul_add,hepay] at hlead
    rw [htpay] at herror
    dsimp [badRawCost]
    calc
      _ = (omegaCap/a0)*labelReciprocal N Q d+
        (tau/a0)*labelReciprocal N Q d := by ring
      _ ≤ _ := by linarith
  exact (hs N hNs Q d hd hscale ha).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hc (div_nonneg (Nat.cast_nonneg N)
      (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)))

theorem actual_bad_inclusive_upper {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ordinaryBad N Q d ≤ rawScale N Q d*(badRawCost+epsilon) := by
  obtain ⟨Tu,hTu,hu⟩ := actual_bad_unit_upper heta (half_pos he)
  obtain ⟨Tn,hTn,hn⟩ := actual_bad_nonunit_upper heta (half_pos he)
  refine ⟨max Tu Tn,hTu.trans (le_max_left _ _),?_⟩
  intro N hN Q d hd hscale ha
  have hunit := hu N ((le_max_left _ _).trans hN) Q d hd hscale ha
  have hnonunit := hn N ((le_max_right _ _).trans hN) Q d hd hscale ha
  rw [original_unit_partition hd]
  nlinarith

def convertedBad (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d*thetaConversion N d*ordinaryBad N Q d

/-- Original inclusive constant-a0 bad-Gamma5 mass to the original
positive marked normalization. Empty support and zero Theta are allowed. -/
theorem original_badGamma5_cost_theta {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedBad N Q D sigma ≤ badRawCost*Theta N Q D sigma+
        epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,h⟩ := actual_bad_inclusive_upper heta he
  refine ⟨T,hT,?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hN4 := hT.trans hN
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  have hp (d : ℕ) (hm : d ∈ D) :
      sigma d*thetaConversion N d*ordinaryBad N Q d ≤
        sigma d*thetaAtom N Q d*(badRawCost+epsilon) := by
    have hw := mul_nonneg (hsigma d hm)
      (P2EnhancedUnitSourceMass.thetaConversion_nonneg hN4 (hd d hm) (hR d hm))
    calc
      _ ≤ sigma d*thetaConversion N d*
          rawMainAtom N Q d (fun _ => badRawCost+epsilon) := by
        simpa only [rawMainAtom,rawScale] using mul_le_mul_of_nonneg_left
          (h N hN Q d (hd d hm) (hscale d hm) (ha d hm)) hw
      _ = sigma d*(thetaConversion N d*
          rawMainAtom N Q d (fun _ => badRawCost+epsilon)) := by ring
      _ = _ := by
        rw [rawMainAtom_to_thetaAtom (by omega : 0 < N) (hd d hm) Q (hR d hm)]
        ring
  have hs := sum_le_sum (s := D) hp
  simpa only [convertedBad,mul_add,sum_add_distrib,← sum_mul,← Theta_eq_sum_atoms,mul_comm]
    using hs

end
end ImbalancedChen.P2EnhancedBadGamma5CostTheta
