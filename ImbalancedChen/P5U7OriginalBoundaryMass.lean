import ImbalancedChen.P5U7OriginalSourceMass
import ImbalancedChen.ActualPrimeReciprocalMass
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Original U7 boundary payment, source only / uncompiled.
The first import is the preceding exclusive draft's proposed installed path.
All older draft files are frozen.

The boundary is an ACTUAL arithmetic window. Its four-prime branch is
empty for eta<=1 because the original product wall is strict. The closed
rough mother still contains one and may contain a prime-square endpoint;
those objects are not silently identified with the arithmetic family.
No interior double-prime transport or desired boundary-mass estimate is
assumed. A native PNT/Abel finite-window bound supplies the eta dependence.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7BoundaryGate (N : ℕ) (eta : ℝ) (t : ℕ × ℕ) : Prop :=
  Real.log ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) ≤ (1+eta)*Real.log (t.2 : ℝ)

def p5U7BoundaryPairs (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59/250 : ℝ))).filter (p5U7BoundaryGate N eta)

def p5U7BoundaryThree (N : ℕ) (eta : ℝ) : Finset P5U7ThreeLabel :=
  (p5U7ArithmeticThree N).filter (fun x => p5U7BoundaryGate N eta x.1)

def p5U7BoundaryFour (N : ℕ) (eta : ℝ) : Finset P5U7FourLabel :=
  (p5U7ArithmeticFour N).filter (fun x => p5U7BoundaryGate N eta x.1)

def p5U7BoundarySecondWindow (N : ℕ) (eta : ℝ) (p : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun q => (p,q) ∈ p5U7BoundaryPairs N eta)

def p5U7BoundaryPairReciprocalMass (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7BoundaryPairs N eta, 1 / ((t.1*t.2 : ℕ) : ℝ)

theorem p5U7Boundary_gate_iff_argument {N : ℕ} {t : ℕ × ℕ} (eta : ℝ)
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59/250 : ℝ))) :
    p5U7BoundaryGate N eta t ↔
      Real.log ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) / Real.log (t.2 : ℝ) ≤ 1+eta := by
  obtain ⟨hc,_⟩ := Finset.mem_filter.mp ht
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hlog : 0 < Real.log (t.2 : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  exact (div_le_iff₀ hlog).symm

/-- Original strict products exclude even the r=s=p2 endpoint when s<=2. -/
theorem p5U7Boundary_four_empty {N : ℕ} {eta : ℝ} (heta : eta ≤ 1) :
    p5U7BoundaryFour N eta = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxA,hgate⟩ := Finset.mem_filter.mp hx
  obtain ⟨ht,hrs⟩ := Finset.mem_sigma.mp hxA
  obtain ⟨hc,_⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
  obtain ⟨_hrsc,hwall,horder,hlt⟩ := Finset.mem_filter.mp hrs
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp h₂).2.1
  have hb := (p5U7Mass_outer_geometry ht).1
  have hbR : (0 : ℝ) < ((x.1.1*x.1.2 : ℕ) : ℝ) := by exact_mod_cast hb
  have hp₂R : (0 : ℝ) < x.1.2 := by exact_mod_cast hp₂.pos
  have hlog : 0 < Real.log (x.1.2 : ℝ) := Real.log_pos (by exact_mod_cast hp₂.one_lt)
  have hprod : x.1.2 ^ 2 ≤ x.2.1*x.2.2 := by
    simpa only [pow_two] using Nat.mul_le_mul hwall (hwall.trans horder)
  have hprodR : (x.1.2 : ℝ)^2 ≤ ((x.2.1*x.2.2 : ℕ) : ℝ) := by exact_mod_cast hprod
  have hltR : ((x.1.1*x.1.2 : ℕ) : ℝ)*((x.2.1*x.2.2 : ℕ) : ℝ)<N := by exact_mod_cast hlt
  have hquot : (x.1.2 : ℝ)^2 < (N : ℝ)/((x.1.1*x.1.2 : ℕ) : ℝ) :=
    hprodR.trans_lt ((lt_div_iff₀ hbR).mpr (by simpa only [mul_comm] using hltR))
  have hlogs := Real.log_lt_log (sq_pos_of_pos hp₂R) hquot
  rw [Real.log_pow] at hlogs
  have hfactor : (1+eta)*Real.log (x.1.2 : ℝ) ≤ 2*Real.log (x.1.2 : ℝ) := by nlinarith
  exact (not_lt_of_ge (hgate.trans hfactor)) (by simpa using hlogs)

/-- The closed rough mother retains its unit at the square boundary. -/
theorem p5U7Boundary_rough_unit_and_square {p : ℕ} (hp : Nat.Prime p) :
    1 ∈ roughNumbers ((p : ℝ)^2) (p : ℝ) ∧
      p^2 ∈ roughNumbers ((p : ℝ)^2) (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  constructor
  · exact one_mem_roughNumbers.mpr (by nlinarith)
  · apply mem_roughNumbers.mpr
    refine ⟨pow_pos hp.pos 2, by simp, ?_⟩
    intro q hq hd
    rw [pow_two] at hd
    rcases hq.dvd_mul.mp hd with h | h
    all_goals have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
    all_goals exact_mod_cast heq.ge

private theorem p5U7Boundary_inv_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => 1/t) (-(1/x^2)) x := by
  simpa only [one_div] using hasDerivAt_inv hx.ne'

/-- A finite, uniform reciprocal-prime interval bound from the actual PNT.
The extra 1/a retains the possible included lower prime endpoint. -/
theorem p5U7Boundary_prime_reciprocal_interval {a b : ℝ}
    (ha : primeErrorStart ≤ a) (hab : a ≤ b) :
    (∑ p ∈ primesIcc a b, 1/(p : ℝ)) ≤
      2/Real.log a + 2*Real.log (Real.log b/Real.log a) + 1/a := by
  have ha1 : 1 < a := by linarith [primeErrorStart_spec.1]
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla := Real.log_pos ha1
  have hlb := Real.log_pos hb1
  have hc : ContinuousOn (fun t : ℝ => 1/t^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (ha0.trans_le ht.1)))
  have hd : IntegrableOn (deriv (fun t : ℝ => 1/t)) (Icc a b) := by
    refine hc.neg.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro t ht
    exact (p5U7Boundary_inv_deriv (ha0.trans_le ht.1)).deriv.symm
  have habel := prime_abel ha0.le hab
    (fun t ht => (p5U7Boundary_inv_deriv (ha0.trans_le ht.1)).differentiableAt) hd
  have hid : (∫ t in a..b, deriv (fun s : ℝ => 1/s) t * primePi t) =
      -(∫ t in a..b, (1/t^2)*primePi t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    rw [(p5U7Boundary_inv_deriv (ha0.trans_le ht.1)).deriv]
    ring
  have hki : IntervalIntegrable (fun t : ℝ => (1/t^2)*primePi t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_mul_primePi ha0.le hc.integrableOn_Icc)
  have hli : IntervalIntegrable (fun t : ℝ => 2/(t*Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply continuousOn_const.div (continuousOn_id.mul ?_)
    · intro t ht
      exact (Real.continuousAt_log (ne_of_gt (ha0.trans_le ht.1))).continuousWithinAt
    · intro t ht
      exact mul_ne_zero (ne_of_gt (ha0.trans_le ht.1))
        (Real.log_pos (ha1.trans_le ht.1)).ne'
  have hile := intervalIntegral.integral_mono_on hab hki hli (fun t ht => by
    have ht0 := ha0.trans_le ht.1
    have hlog := Real.log_pos (ha1.trans_le ht.1)
    have hpi := mul_le_mul_of_nonneg_left (primePi_le_two_mul (ha.trans ht.1))
      (show 0 ≤ 1/t^2 by positivity)
    convert hpi using 1 <;> field_simp [ht0.ne',hlog.ne'] <;> ring)
  have hilog : (∫ t in a..b, 2/(t*Real.log t)) =
      2*Real.log (Real.log b/Real.log a) := by
    calc
      _ = 2*(∫ t in a..b, t⁻¹/Real.log t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = 2*(Real.log (Real.log b)-Real.log (Real.log a)) := by
        rw [integral_inv_div_log ha1 hb1]
      _ = _ := by rw [Real.log_div hlb.ne' hla.ne']
  have hbe : (1/b)*primePi b ≤ 2/Real.log b := by
    have hpi := mul_le_mul_of_nonneg_left (primePi_le_two_mul (ha.trans hab))
      (show 0 ≤ 1/b by positivity)
    convert hpi using 1 <;> field_simp [hb0.ne',hlb.ne'] <;> ring
  have hae : 0 ≤ (1/a)*primePi a := by unfold primePi; positivity
  rw [hid] at habel
  rw [hilog] at hile
  have hioc : (∑ p ∈ primesIoc a b, 1/(p : ℝ)) ≤
      2/Real.log b + 2*Real.log (Real.log b/Real.log a) := by linarith only [habel,hile,hbe,hae]
  have hlogmono := Real.log_le_log ha0 hab
  have hdiv : 2/Real.log b ≤ 2/Real.log a :=
    div_le_div_of_nonneg_left (by norm_num) hla hlogmono
  rw [sum_primesIcc_eq_sum_primesIoc_add hb0.le (fun t : ℝ => 1/t)]
  split_ifs <;> linarith [one_div_pos.mpr ha0]

/-- Arbitrary finite prime windows have a uniform bound in terms of their
actual logarithmic width, without any interval-limit hypothesis. -/
theorem p5U7Boundary_finite_prime_window (S : Finset ℕ) {A kappa : ℝ}
    (hA : primeErrorStart ≤ A) (hk : 1 ≤ kappa)
    (hp : ∀ p ∈ S, Nat.Prime p) (hlo : ∀ p ∈ S, A ≤ (p : ℝ))
    (hwidth : ∀ p ∈ S, ∀ q ∈ S, Real.log (q : ℝ) ≤ kappa*Real.log (p : ℝ)) :
    (∑ p ∈ S, 1/(p : ℝ)) ≤ 2/Real.log A + 2*Real.log kappa + 1/A := by
  have hA1 : 1 < A := by linarith [primeErrorStart_spec.1]
  have hA0 : 0 < A := by linarith
  have hlA := Real.log_pos hA1
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ham : a ∈ S := Finset.min'_mem _ _
    have hbm : b ∈ S := Finset.max'_mem _ _
    have hab : (a : ℝ) ≤ b := by exact_mod_cast Finset.min'_le S b hbm
    have hAa : A ≤ (a : ℝ) := hlo a ham
    have ha1 : (1 : ℝ) < a := hA1.trans_le hAa
    have hb1 : (1 : ℝ) < b := ha1.trans_le hab
    have hla := Real.log_pos ha1
    have hlb := Real.log_pos hb1
    have hsub : S ⊆ primesIcc (a : ℝ) (b : ℝ) := by
      intro p hpm
      exact (mem_primesIcc (by linarith : (0 : ℝ) ≤ b)).mpr
        ⟨hp p hpm, by exact_mod_cast Finset.min'_le S p hpm,
          by exact_mod_cast Finset.le_max' S p hpm⟩
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hpm _ => one_div_nonneg.mpr (Nat.cast_nonneg p))
    have hraw := p5U7Boundary_prime_reciprocal_interval (hA.trans hAa) hab
    have hratio : Real.log (b : ℝ)/Real.log (a : ℝ) ≤ kappa :=
      (div_le_iff₀ hla).mpr (hwidth a ham b hbm)
    have hlratio := Real.log_le_log (div_pos hlb hla) hratio
    have hdiv : 2/Real.log (a : ℝ) ≤ 2/Real.log A :=
      div_le_div_of_nonneg_left (by norm_num) hlA (Real.log_le_log hA0 hAa)
    have hinv : 1/(a : ℝ) ≤ 1/A := one_div_le_one_div_of_le hA0 hAa
    exact hsum.trans (hraw.trans (by linarith only [hlratio,hdiv,hinv]))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by norm_num) (Real.log_nonneg hk)))
      (one_div_nonneg.mpr hA0.le)

/-- A genuine source-pair window forces this bound for EVERY two of its
second primes, so min/max endpoints can be chosen after the source is fixed. -/
theorem p5U7Boundary_second_window_log_width {N p q r : ℕ} {eta : ℝ}
    (hq : q ∈ p5U7BoundarySecondWindow N eta p)
    (hr : r ∈ p5U7BoundarySecondWindow N eta p) :
    Real.log (r : ℝ) ≤ (1+eta/2)*Real.log (q : ℝ) := by
  have hqpair := (Finset.mem_filter.mp hq).2
  have hrpair := (Finset.mem_filter.mp hr).2
  obtain ⟨hqt,hqgate⟩ := Finset.mem_filter.mp hqpair
  obtain ⟨hrt,_hrgate⟩ := Finset.mem_filter.mp hrpair
  obtain ⟨hqc,_hD,_hoq,_hcq⟩ := Finset.mem_filter.mp hqt
  obtain ⟨hpc,hqpc⟩ := Finset.mem_product.mp hqc
  have hp := (mem_chenAdditivePrimeCarrier.mp hpc).2.1
  have hqp := (mem_chenAdditivePrimeCarrier.mp hqpc).2.1
  obtain ⟨hrc,_hDr,_hor,hcap⟩ := Finset.mem_filter.mp hrt
  have hrp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hrc).2).2.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrp.pos
  have hNp : (0 : ℝ) < N := by exact_mod_cast hp.pos.trans (mem_chenAdditivePrimeCarrier.mp hpc).1
  have hsq : (r : ℝ)^2 < (N : ℝ)/(p : ℝ) := by
    have h := (sq_lt_sq₀ hrR.le (Real.sqrt_nonneg _)).mpr hcap
    rwa [Real.sq_sqrt (div_nonneg hNp.le hpR.le)] at h
  have hlogr := Real.log_lt_log (sq_pos_of_pos hrR) hsq
  rw [Real.log_pow,Real.log_div hNp.ne' hpR.ne'] at hlogr
  change Real.log ((N : ℝ)/((p*q : ℕ) : ℝ)) ≤ (1+eta)*Real.log (q : ℝ) at hqgate
  rw [Nat.cast_mul,Real.log_div hNp.ne' (mul_ne_zero hpR.ne' hqR.ne'),
    Real.log_mul hpR.ne' hqR.ne'] at hqgate
  nlinarith only [hlogr.le,hqgate]

def p5U7BoundaryWindowError (N : ℕ) : ℝ :=
  2/((59/250 : ℝ)*Real.log (N : ℝ)) + 1/(N : ℝ)^(59/250 : ℝ)

/-- Quantitative finite inner-window bound; no thin-region integral limit
is required and all arithmetic endpoint atoms are retained. -/
theorem p5U7Boundary_second_window_reciprocal_le {N : ℕ} {eta : ℝ}
    (hN : 2 ≤ N) (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ)) (heta : 0 ≤ eta)
    (p : ℕ) :
    (∑ q ∈ p5U7BoundarySecondWindow N eta p, 1/(q : ℝ)) ≤ eta+p5U7BoundaryWindowError N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hk : 1 ≤ (1+eta/2 : ℝ) := by linarith
  have hraw := p5U7Boundary_finite_prime_window (p5U7BoundarySecondWindow N eta p)
    hstart hk
    (fun q hq => (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1)
    (fun q hq => (p5U7Mass_outer_geometry
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2).1).2.1)
    (fun q hq r hr => p5U7Boundary_second_window_log_width hq hr)
  have hlog := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ)<1+eta/2)
  rw [Real.log_rpow hNp] at hraw
  unfold p5U7BoundaryWindowError
  linarith only [hraw,hlog]

theorem p5U7Boundary_three_card_eq_primeFibres (N : ℕ) (eta : ℝ) :
    ((p5U7BoundaryThree N eta).card : ℝ) =
      ∑ t ∈ p5U7BoundaryPairs N eta, ((p5U7MassPrimeFibre N (t.1*t.2) t.2).card : ℝ) := by
  have heq : p5U7BoundaryThree N eta =
      (p5U7BoundaryPairs N eta).sigma (fun t => p5U7MassPrimeFibre N (t.1*t.2) t.2) := by
    ext x
    simp only [p5U7BoundaryThree,p5U7BoundaryPairs,p5U7ArithmeticThree,
      p5U7MassPrimeFibre,Finset.mem_filter,Finset.mem_sigma]
    constructor
    · rintro ⟨⟨ht,hq⟩,hg⟩
      exact ⟨⟨ht,hg⟩,hq⟩
    · rintro ⟨⟨ht,hg⟩,hq⟩
      exact ⟨⟨ht,hq⟩,hg⟩
  rw [heq]
  simp only [Finset.card_sigma,Nat.cast_sum]

/-- The original boundary source pays a concrete prime-density kernel.
The thin pair mass is an actual finite prime sum, not a target hypothesis. -/
theorem p5U7Boundary_three_le_PNT_kernel {N : ℕ} (eta : ℝ)
    (hN : 2 ≤ N) (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ)) :
    ((p5U7BoundaryThree N eta).card : ℝ) ≤
      (500/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ))*p5U7BoundaryPairReciprocalMass N eta := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hNp := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  rw [p5U7Boundary_three_card_eq_primeFibres,p5U7BoundaryPairReciprocalMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hto := (Finset.mem_filter.mp ht).1
  have hg := p5U7Mass_outer_geometry hto
  have hbR : (0 : ℝ)<((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hy : primeErrorStart ≤ (t.2 : ℝ) := hstart.trans hg.2.1
  have hx : primeErrorStart ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := hy.trans hg.2.2.1.le
  have hxpos : (0 : ℝ)<(N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := div_pos hNp hbR
  have hlower : (59/250 : ℝ)*Real.log (N : ℝ) ≤
      Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNp _) (hg.2.1.trans hg.2.2.1.le)
    rwa [Real.log_rpow hNp] at h
  have hden : 0 < (59/250 : ℝ)*Real.log (N : ℝ) := mul_pos (by norm_num) hlog
  calc
    _ ≤ primePi ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) := p5U7Mass_primeFibre_card_le_primePi _ _ _ hg.1
    _ ≤ 2*((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))) := primePi_le_two_mul hx
    _ ≤ 2*((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)/((59/250 : ℝ)*Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hxpos.le hden hlower) (by norm_num)
    _ = _ := by field_simp [hbR.ne',hlog.ne']; ring

def p5U7BoundaryOuterPrimes (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun p => (N : ℝ)^(59/250 : ℝ) ≤ (p : ℝ))

def p5U7BoundaryOuterReciprocalMass (N : ℕ) : ℝ :=
  ∑ p ∈ p5U7BoundaryOuterPrimes N, 1/(p : ℝ)

theorem p5U7Boundary_pair_mass_eq_windows (N : ℕ) (eta : ℝ) :
    p5U7BoundaryPairReciprocalMass N eta =
      ∑ p ∈ p5U7BoundaryOuterPrimes N, (1/(p : ℝ))*
        (∑ q ∈ p5U7BoundarySecondWindow N eta p, 1/(q : ℝ)) := by
  let T := (p5U7BoundaryOuterPrimes N).sigma (p5U7BoundarySecondWindow N eta)
  have hsum : p5U7BoundaryPairReciprocalMass N eta =
      ∑ v ∈ T, (1/(v.1 : ℝ))*(1/(v.2 : ℝ)) := by
    refine Finset.sum_bij (fun t _ => ⟨t.1,t.2⟩) ?_ ?_ ?_ ?_
    · intro t ht
      have hto := (Finset.mem_filter.mp ht).1
      obtain ⟨hc,hD,_ho,_hcap⟩ := Finset.mem_filter.mp hto
      obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
      exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨h₁,hD⟩,
        Finset.mem_filter.mpr ⟨h₂,ht⟩⟩
    · intro t ht u hu heq
      exact Prod.ext (congrArg (fun v : Σ _ : ℕ, ℕ => v.1) heq)
        (congrArg (fun v : Σ _ : ℕ, ℕ => v.2) heq)
    · intro v hv
      have hq := (Finset.mem_sigma.mp hv).2
      refine ⟨(v.1,v.2),(Finset.mem_filter.mp hq).2,?_⟩
      cases v
      rfl
    · intro t ht
      simp only [Nat.cast_mul,one_div_mul_one_div]
  rw [hsum,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

theorem p5U7Boundary_pair_mass_le_thin_windows {N : ℕ} {eta : ℝ}
    (hN : 2 ≤ N) (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ)) (heta : 0 ≤ eta) :
    p5U7BoundaryPairReciprocalMass N eta ≤
      p5U7BoundaryOuterReciprocalMass N * (eta+p5U7BoundaryWindowError N) := by
  rw [p5U7Boundary_pair_mass_eq_windows,p5U7BoundaryOuterReciprocalMass,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (p5U7Boundary_second_window_reciprocal_le hN hstart heta p)
    (one_div_nonneg.mpr (Nat.cast_nonneg p))

/-- Primitive outer prime mass is controlled by the existing actual
reciprocal-prime supplier on the fixed power window [d,1). -/
theorem p5U7Boundary_outer_mass_le_actual (N : ℕ) :
    p5U7BoundaryOuterReciprocalMass N ≤ actualPrimeReciprocalMass N (59/250) 1 := by
  let R := roughPrimeFinset N (Nat.ceil ((N : ℝ)^(1 : ℝ)))
    ((N : ℝ)^(59/250 : ℝ)) ((N : ℝ)^(1 : ℝ))
  have hs : p5U7BoundaryOuterPrimes N ⊆ R := by
    intro p hp
    obtain ⟨hpc,hD⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime,hcop⟩ := mem_chenAdditivePrimeCarrier.mp hpc
    apply (mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)).mpr
    refine ⟨hprime,hprime.coprime_iff_not_dvd.mp hcop,hD,?_⟩
    simpa only [Real.rpow_one] using (show (p : ℝ)<N by exact_mod_cast hpN)
  calc
    _ ≤ ∑ p ∈ p5U7BoundaryOuterPrimes N, 1/((p : ℝ)-1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
      have hpR : (1 : ℝ)<p := by exact_mod_cast hprime.one_lt
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    _ ≤ ∑ p ∈ R, 1/((p : ℝ)-1) := Finset.sum_le_sum_of_subset_of_nonneg hs (by
      intro p hp hn
      have hp2 : (2 : ℝ)≤p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.two_le
      exact one_div_nonneg.mpr (by linarith))
    _ = _ := rfl

theorem p5U7Boundary_eventually_outer_mass_le_five :
    ∀ᶠ N : ℕ in atTop, p5U7BoundaryOuterReciprocalMass N ≤ 5 := by
  have hlog : Real.log ((1 : ℝ)/(59/250)) < 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<1/(59/250))
    norm_num at h
    linarith
  have hlim := tendsto_actualPrimeReciprocalMass (by norm_num : (0 : ℝ)<59/250)
    (by norm_num : (59/250 : ℝ)<1)
  filter_upwards [hlim.eventually (gt_mem_nhds hlog)] with N hN
  exact (p5U7Boundary_outer_mass_le_actual N).trans hN.le

theorem p5U7Boundary_window_error_tendsto_zero :
    Tendsto p5U7BoundaryWindowError atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfirst : Tendsto (fun N : ℕ => 2/((59/250 : ℝ)*Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h := hlog.const_div_atTop ((2 : ℝ)/(59/250))
    convert h using 1
    funext N
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  simpa only [p5U7BoundaryWindowError,zero_add] using hfirst.add (hgrowth.const_div_atTop (1 : ℝ))

/-- The actual arithmetic boundary costs O(eta) on N/log N. One common
threshold even precedes eta in [0,1]; in particular eta may be fixed first.
No real-integral DCT or desired mass bound is an input. -/
theorem p5U7Boundary_eventually_arithmetic_mass_le (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, 0≤eta → eta≤1 →
      ((p5U7BoundaryThree N eta).card : ℝ)+((p5U7BoundaryFour N eta).card : ℝ) ≤
        (50*eta+epsilon)*((N : ℝ)/Real.log (N : ℝ)) := by
  have hsmall := p5U7Boundary_window_error_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ)<epsilon*(59/2500)))
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall,p5U7Boundary_eventually_outer_mass_le_five,
    hgrowth.eventually (eventually_ge_atTop primeErrorStart),eventually_ge_atTop (2 : ℕ)]
    with N herr houter hstart hN
  intro eta heta heta1
  rw [p5U7Boundary_four_empty heta1,Finset.card_empty,Nat.cast_zero,add_zero]
  have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hlog := Real.log_pos hNr
  have hscale : 0≤(N : ℝ)/Real.log (N : ℝ) := div_nonneg (Nat.cast_nonneg N) hlog.le
  have herror : 0≤p5U7BoundaryWindowError N := by
    unfold p5U7BoundaryWindowError
    positivity
  have hpair := p5U7Boundary_pair_mass_le_thin_windows hN hstart heta
  have hpair5 : p5U7BoundaryPairReciprocalMass N eta ≤ 5*(eta+p5U7BoundaryWindowError N) :=
    hpair.trans (mul_le_mul_of_nonneg_right houter (add_nonneg heta herror))
  have hcoef : (500/59 : ℝ)*5*(eta+p5U7BoundaryWindowError N) ≤ 50*eta+epsilon := by
    nlinarith only [herr.le,heta]
  calc
    _ ≤ (500/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ))*p5U7BoundaryPairReciprocalMass N eta :=
      p5U7Boundary_three_le_PNT_kernel eta hN hstart
    _ ≤ (500/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ))*(5*(eta+p5U7BoundaryWindowError N)) :=
      mul_le_mul_of_nonneg_left hpair5 (mul_nonneg (by norm_num) hscale)
    _ = ((500/59 : ℝ)*5*(eta+p5U7BoundaryWindowError N))*((N : ℝ)/Real.log (N : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hscale

/-- Exact original U7 ledger coefficient TWO; epsilon is still arbitrary. -/
theorem p5U7Boundary_eventually_two_arithmetic_mass_le (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, 0≤eta → eta≤1 →
      2*(((p5U7BoundaryThree N eta).card : ℝ)+((p5U7BoundaryFour N eta).card : ℝ)) ≤
        (100*eta+epsilon)*((N : ℝ)/Real.log (N : ℝ)) := by
  filter_upwards [p5U7Boundary_eventually_arithmetic_mass_le (epsilon/2) (by positivity)]
    with N hN
  intro eta heta heta1
  have h := mul_le_mul_of_nonneg_left (hN eta heta heta1) (by norm_num : (0 : ℝ)≤2)
  convert h using 1 <;> ring

end

end ImbalancedChen
