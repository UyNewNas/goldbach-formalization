import ImbalancedChen.P4BActualUpperRoughPrimeReserveZero
import ImbalancedChen.P2OriginalGammaDivisorNorm
import ImbalancedChen.P5ProperPowerPhysicalPolynomialPayment
import ImbalancedChen.P5OriginalSingletonLowerTrimPaid

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The complete-product trim in the actual arbitrary-width upper source is
paid after the full signed modulus sum.  The independent original primes
remain ordered, including equal primes.  Their product fibres are bounded
by the already proved ordered-factor count.  The nonzero target difference
and exact coprime mean use the existing physical signed-row supplier.

The only coefficient premise is a primitive polynomial active-cap bound
on the SAME attachedUpperCoefficient.  No trim estimate, source identity,
source mass or PP estimate is an input.  A final full87 instance of that
support condition is a separate obligation.
-/
namespace ImbalancedChen.P4BActualUpperTrimPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.IndependentPrimeSourceWordDictionary
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.LicensedOriginalIntegerProfile
open P5Z.ProperPowerSignedMeanHBTransport
open P5Z.ProperPowerPhysicalPolynomialPayment
open P2OriginalGammaDivisorNorm
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The source carrier keeps all original labelled prime occurrences. -/
def lowPrimeWords (cap k Y : ℕ) : Finset (List ℕ) :=
  (primeTuples cap k).filter (fun ps => ps.prod ≤ Y)

theorem prime_word_product_pos {cap k : ℕ} {ps : List ℕ}
    (hps : ps ∈ primeTuples cap k) : 0 < ps.prod :=
  List.prod_pos (fun p hp => ((primeTuples_spec cap k hps).2 p hp).1.pos)

/-- The complete product is not treated as an injective label. -/
theorem lowPrimeWords_card_le (cap k Y : ℕ) :
    ((lowPrimeWords cap k Y).card : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 Y, (fouvryTau k m : ℝ) := by
  have hmap : ∀ ps ∈ lowPrimeWords cap k Y, ps.prod ∈ Finset.Icc 1 Y := by
    intro ps hps
    obtain ⟨hps, hY⟩ := Finset.mem_filter.mp hps
    exact Finset.mem_Icc.mpr ⟨prime_word_product_pos hps, hY⟩
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := lowPrimeWords cap k Y) (t := Finset.Icc 1 Y) (g := List.prod)
    hmap (fun _ => (1 : ℝ))
  calc
    _ = ∑ m ∈ Finset.Icc 1 Y,
        ∑ ps ∈ lowPrimeWords cap k Y with ps.prod = m, (1 : ℝ) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hf.symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      have hsub : (lowPrimeWords cap k Y).filter (fun ps => ps.prod = m) ⊆
          orderedFactors k m := by
        intro ps hps
        obtain ⟨hps, hprod⟩ := Finset.mem_filter.mp hps
        have hprime := (Finset.mem_filter.mp hps).1
        exact (mem_orderedFactors k m ps).mpr
          ⟨(primeTuples_spec cap k hprime).1, hprod,
            hprod ▸ prime_word_product_pos hprime⟩
      have hc := Finset.card_le_card hsub
      rw [card_orderedFactors] at hc
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        (Nat.cast_le.mpr hc :
          (((lowPrimeWords cap k Y).filter (fun ps => ps.prod = m)).card : ℝ) ≤
            (fouvryTau k m : ℝ))

/-- The source multiplicity is supplied by the existing divisor theorem;
the constant is chosen before N, the source cap and the low cut. -/
theorem exists_lowPrimeWords_card_budget (k : ℕ) (hk : 1 ≤ k)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap Y : ℕ, Y ≤ N →
      ((lowPrimeWords cap k Y).card : ℝ) ≤
        (Y : ℝ) * (C * (N : ℝ)^eps) := by
  obtain ⟨C, hC, htau⟩ :=
    Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow hk heps
  refine ⟨C, hC, ?_⟩
  intro N cap Y hYN
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, (fouvryTau k m : ℝ) := lowPrimeWords_card_le cap k Y
    _ ≤ ∑ _m ∈ Finset.Icc 1 Y, C * (N : ℝ)^eps := by
      apply Finset.sum_le_sum
      intro m hm
      exact (htau m (Finset.mem_Icc.mp hm).1).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast (Finset.mem_Icc.mp hm).2.trans hYN) heps.le) hC.le)
    _ = _ := by simp

/-- An exact kernel dictionary.  The target N and complete word product
occur in the same positions in the count and coprime mean. -/
theorem wordKernel_eq_signedRow (Q : Finset ℕ) (rho : ℕ → ℂ)
    (N : ℕ) (ps : List ℕ) :
    wordKernel Q rho N ps = signedRow Q rho N ps.prod := by
  unfold wordKernel signedRow
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  rw [residueKernel_real]
  by_cases hc : Nat.ModEq q ps.prod N <;>
    by_cases hg : ps.prod.Coprime q <;> simp [signedKernel, hc, hg]

theorem actual_listExtension_bounds {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
    (hgap : 2*width ≤ baseline b kappa-nu*r) (N : ℕ) (ps : List ℕ) :
    0 ≤ listExtension (licence hb hnu hr hw hgap N) ps ∧
      listExtension (licence hb hnu hr hw hgap N) ps ≤ 1 := by
  unfold listExtension
  split_ifs
  · exact bounds b kappa width N _
  · exact ⟨le_rfl, zero_le_one⟩

theorem actual_trim_factor_norm_le {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
    (hgap : 2*width ≤ baseline b kappa-nu*r) (N : ℕ)
    (kappa0 : ℝ) (ps : List ℕ) :
    ‖(1-(P5Z.ActualEtaPsiOccurrenceBudget.eta
        ((ps.prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ)) *
      (listExtension (licence hb hnu hr hw hgap N) ps : ℂ)‖ ≤ 1 := by
  have he := P5Z.ActualEtaPsiOccurrenceBudget.eta_bounds
    ((ps.prod : ℝ)/(N : ℝ)^(1-kappa0))
  have hwgt := actual_listExtension_bounds hb hnu hr hw hgap N ps
  have hreal : |(1-P5Z.ActualEtaPsiOccurrenceBudget.eta
      ((ps.prod : ℝ)/(N : ℝ)^(1-kappa0))) *
        listExtension (licence hb hnu hr hw hgap N) ps| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hwgt.1)]
    nlinarith
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] using hreal

/-- Finite full-modulus trim estimate on its actual low-product carrier.
No collision term is needed because the genuine cut Y is strictly below N. -/
theorem exists_actual_trim_budget {eps : ℝ} (heps : 0 < eps) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ b kappa nu r width : ℝ, ∀ hb : 0 < b, ∀ hnu : 0 < nu,
      ∀ hr : 0 < r, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa-nu*r,
      ∀ (N Y : ℕ) (kappa0 epsilon theta : ℝ)
        (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      1 ≤ N → Y < N → 0 ≤ theta →
      2*(N : ℝ)^(1-kappa0) ≤ (Y : ℝ) →
      (P4BActualSmoothHyperbolaCorrection.actualActiveUpperCap
        nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
      ‖trimReserve (licence hb hnu hr hw hgap N) N N kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ))‖ ≤
        ((Y : ℝ)*(C*(N : ℝ)^eps)) *
          ((D*3^eps)*(N : ℝ)^eps+4*(1+theta*Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hcount⟩ := exists_lowPrimeWords_card_budget 2 (by norm_num) heps
  obtain ⟨D, hD, hrow⟩ := physical_noncollision_signedRow_subpower heps
  refine ⟨C, D, hC, hD, ?_⟩
  intro b kappa nu r width hb hnu hr hw hgap N Y kappa0 epsilon theta retain cap
    hN hYN htheta hcut hcap
  let B : ℝ := (D*3^eps)*(N : ℝ)^eps+4*(1+theta*Real.log (N : ℝ))
  have hB : 0 ≤ B := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [B]
    positivity
  have hpositive : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzero (ps : List ℕ) (hY : Y < ps.prod) :
      1-(P5Z.ActualEtaPsiOccurrenceBudget.eta
        ((ps.prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) = 0 := by
    have hprod : 2*(N : ℝ)^(1-kappa0) ≤ (ps.prod : ℝ) :=
      hcut.trans (by exact_mod_cast hY.le)
    rw [P5Z.ActualEtaPsiOccurrenceBudget.eta_one
      ((le_div_iff₀ (Real.rpow_pos_of_pos hpositive _)).mpr hprod)]
    simp
  calc
    _ ≤ ∑ ps ∈ primeTuples N 2,
        ‖((1-(P5Z.ActualEtaPsiOccurrenceBudget.eta
          ((ps.prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ)) *
          (listExtension (licence hb hnu hr hw hgap N) ps : ℂ)) *
          wordKernel (attachedUpperModuli nu r epsilon retain cap N)
            (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) N ps‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ps ∈ primeTuples N 2, if ps.prod ≤ Y then B else 0 := by
      apply Finset.sum_le_sum
      intro ps hps
      by_cases hl : ps.prod ≤ Y
      · rw [if_pos hl, norm_mul]
        apply (mul_le_mul (actual_trim_factor_norm_le hb hnu hr hw hgap N kappa0 ps)
          (le_refl _) (norm_nonneg _) zero_le_one).trans
        rw [one_mul, wordKernel_eq_signedRow]
        have hh := hrow 1 (by norm_num) theta nu r epsilon htheta retain cap N
          hN hcap ps.prod (prime_word_product_pos hps)
          (by simpa only [one_mul, Nat.ceil_natCast] using hl.trans hYN.le)
          (Nat.ne_of_lt (hl.trans_lt hYN))
        simpa only [physicalRho, show (1 : ℝ)+2=3 by norm_num] using hh
      · simp only [if_neg hl, hzero ps (lt_of_not_ge hl), zero_mul, norm_zero]
    _ = ((lowPrimeWords N 2 Y).card : ℝ)*B := by
      rw [← Finset.sum_filter]
      simp only [lowPrimeWords, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcount N N Y hYN.le) hB

/-- The entire literal upper trim has arbitrary logarithmic accuracy.
The threshold precedes every legal width, policy and enumeration cap.
The bound is for the original signed count-minus-exact-coprime-mean. -/
theorem eventually_actual_upper_trim_logAccuracy
    (kappa0 : ℝ) (hkappa0 : 0 < kappa0) (hkappa01 : kappa0 < 1)
    (theta : ℝ) (htheta : 0 ≤ theta) (A : ℕ) (tolerance : ℝ)
    (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, ∀ b kappa nu r width : ℝ,
      ∀ hb : 0 < b, ∀ hnu : 0 < nu, ∀ hr : 0 < r, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa-nu*r,
      ∀ (epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (P4BActualSmoothHyperbolaCorrection.actualActiveUpperCap
        nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
      ‖trimReserve (licence hb hnu hr hw hgap N) N N kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ))‖ ≤
        tolerance*(N : ℝ)/Real.log (N : ℝ)^A := by
  let eps : ℝ := kappa0/4
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨C, D, hC, hD, hbudget⟩ := exists_actual_trim_budget heps
  filter_upwards
    [P5OriginalSingletonLowerTrimPaid.eventually_originalLowerCut_lt
      kappa0 hkappa0 hkappa01,
      eventually_powerLog_le_logAccuracy
        (3*C*(D*3^eps)) (1-kappa0/2) 0 A (by linarith)
        (tolerance/3) (by positivity),
      eventually_powerLog_le_logAccuracy
        (12*C) (1-3*kappa0/4) 0 A (by linarith)
        (tolerance/3) (by positivity),
      eventually_powerLog_le_logAccuracy
        (12*C*theta) (1-3*kappa0/4) 1 A (by linarith)
        (tolerance/3) (by positivity),
      eventually_ge_atTop (1 : ℕ)] with N hcut hAP hM0 hM1 hN
  intro b kappa nu r width hb hnu hr hw hgap epsilon retain cap hcap
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hbound := hbudget b kappa nu r width hb hnu hr hw hgap N
    (P5OriginalSharpPrime.originalLowerCut kappa0 N) kappa0 epsilon theta retain cap
    hN hcut.1 htheta (Nat.le_ceil _) hcap
  have hB : 0 ≤ (D*3^eps)*(N : ℝ)^eps+4*(1+theta*Real.log (N : ℝ)) := by
    positivity
  have hpow1 : (N : ℝ)^(1-kappa0)*(N : ℝ)^eps = (N : ℝ)^(1-3*kappa0/4) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    dsimp [eps]
    ring
  have hpow2 : (N : ℝ)^(1-3*kappa0/4)*(N : ℝ)^eps = (N : ℝ)^(1-kappa0/2) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    dsimp [eps]
    ring
  calc
    _ ≤ ((3*(N : ℝ)^(1-kappa0))*(C*(N : ℝ)^eps))*
        ((D*3^eps)*(N : ℝ)^eps+4*(1+theta*Real.log (N : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcut.2 (by positivity)) hB)
    _ = (3*C*(D*3^eps))*(N : ℝ)^(1-kappa0/2) +
        12*C*(N : ℝ)^(1-3*kappa0/4) +
        (12*C*theta)*(N : ℝ)^(1-3*kappa0/4)*Real.log (N : ℝ) := by
      calc
        _ = (3*C*(D*3^eps))*
              ((N : ℝ)^(1-kappa0)*(N : ℝ)^eps)*(N : ℝ)^eps +
            12*C*((N : ℝ)^(1-kappa0)*(N : ℝ)^eps) +
            (12*C*theta)*((N : ℝ)^(1-kappa0)*(N : ℝ)^eps)*Real.log (N : ℝ) := by ring
        _ = _ := by rw [hpow1, mul_assoc (3*C*(D*3^eps)), hpow2]
    _ ≤ _ := by
      simp only [pow_zero, pow_one, mul_one] at hAP hM0 hM1
      linarith

end
end ImbalancedChen.P4BActualUpperTrimPayment
