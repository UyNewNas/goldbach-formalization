import ImbalancedChen.P4BOriginalFiniteSmoothCount
import ImbalancedChen.P4BActualUpperTrimPayment

/-! The smooth complete-product trim in section 2 of the prime-product
completion, on the finite rectangular coefficient used to count RealB. -/
namespace ImbalancedChen.P4BOriginalFiniteSignedTrim
noncomputable section

open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (Q coefficient weight)
open P4BArbitraryWidthUpperPairProfile (licence)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P5Z.ActualLabelledPrimeSmoothCharts (primeTuples)
open P5Z.IndependentPrimeSourceWordDictionary
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve)
open P5Z.LicensedOriginalIntegerProfile
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ProperPowerSignedModulusPayment (meanBudget norm_signedRow_le rowBudget)
open P5OriginalPrimeEndpoint (distance distance_pos)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev pairLicence {b kappa s : ℝ} (hb : 0<b) (hs : 0<s)
    (hgap : 2*s≤baseline b kappa-19/96) (N : ℕ) :=
  licence hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs
    (by simpa only [one_mul] using hgap) N

/-- The independent labelled primes and their ordering agree with the
original count. The factor is identically one for complete products at
least twice the cutoff power and identically zero through the cutoff power. -/
def trimmedWeight (b kappa s kappa0 : ℝ) (N : ℕ)
    (u : Fin 2 → Fin (N+1)) : ℝ :=
  eta ((Part3.labelledProduct u : ℝ)/(N:ℝ)^(1-kappa0))*weight b kappa s N u

/-- Removing zero amplitudes only inside the reciprocal-totient bound
preserves the full signed carrier in both parts of the discrepancy. -/
private theorem mean_le {N : ℕ} (S : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ d, |c d|≤1) (hrange : ∀ d, c d≠0 → d≤N) :
    meanBudget S (fun d => (c d : ℂ)) ≤ 4*(1+Real.log (max 1 (N:ℝ))) := by
  let A := S.filter (fun d => d∈Finset.Icc 1 N)
  have hzero : meanBudget S (fun d => (c d : ℂ)) =
      meanBudget A (fun d => (c d : ℂ)) := by
    symm
    unfold meanBudget
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hda
    have hout : d∉Finset.Icc 1 N := fun hin => hda (Finset.mem_filter.mpr ⟨hd,hin⟩)
    by_cases hz : d=0
    · simp [hz]
    · have hdz : c d=0 := by
        by_contra h
        exact hout (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hz,hrange d h⟩)
      simp [hdz]
  rw [hzero]
  calc
    _ ≤ ∑ d∈A, 1/(d.totient:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hc d
    _ ≤ _ := sum_reciprocal_totient_subset_le_log A N (fun _ hd => (Finset.mem_filter.mp hd).2)

/-- A target-independent divisor constant controls the AP term at every
complete product below N. The exact coprime mean retains the same c. -/
private theorem exists_row_bound (eps : ℝ) (heps : 0<eps) :
    ∃ D : ℝ,0<D ∧ ∀ (N : ℕ),1≤N → ∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d, |c d|≤1) → (∀ d, c d≠0 → d≤N) → ∀ x<N,
      ‖signedRow S (fun d => (c d : ℂ)) N x‖ ≤ D*(N:ℝ)^eps := by
  obtain ⟨C,hC,hdivisor⟩ :=
    Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow (k:=2) (by norm_num) heps
  refine ⟨C+4*(1+1/eps),by positivity,?_⟩
  intro N hN S c hc hrange x hx
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hNpos := zero_lt_one.trans_le hN1
  have hsum := mean_le S c hc hrange
  rw [max_eq_right hN1] at hsum
  have hlog := Real.log_le_rpow_div hNpos heps
  have hpow := Real.one_le_rpow hN1 heps.le
  have hlogcost : 1+Real.log (N:ℝ)≤(1+1/eps)*(N:ℝ)^eps := by
    calc
      _ ≤ (N:ℝ)^eps+((N:ℝ)^eps)/eps := add_le_add hpow hlog
      _ = _ := by ring
  have hdist : distance N x≤N := by
    simp only [distance,if_pos hx.le]
    exact Nat.sub_le _ _
  have hdiv : ((distance N x).divisors.card:ℝ)≤C*(N:ℝ)^eps := by
    have h := hdivisor (distance N x) (distance_pos hx.ne)
    rw [fouvryTau_two] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdist) heps.le) hC.le)
  have hrow := norm_signedRow_le S (fun d => (c d : ℂ)) 1 (by norm_num)
    (fun d _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hc d) N x
  simp only [rowBudget,if_neg hx.ne,one_mul] at hrow
  have hmean := hsum.trans (mul_le_mul_of_nonneg_left hlogcost (by norm_num : (0:ℝ)≤4))
  exact hrow.trans ((add_le_add hdiv hmean).trans_eq (by ring))

/-- The modulus bound supplied by the actual density/PP schedule is
used only for the reciprocal-totient sum. The target threshold below
precedes every eligible source width, policy and rectangle index. -/
private theorem exists_trim_bound (eps : ℝ) (heps : 0<eps) :
    ∃ C : ℝ,0<C ∧ ∀ b kappa s kappa0 : ℝ,∀ hb : 0<b,∀ hs : 0<s,
    ∀ hgap : 2*s≤baseline b kappa-19/96,∀ N Y : ℕ,1≤N → Y<N →
    2*(N:ℝ)^(1-kappa0)≤(Y:ℝ) → ∀ (S : Finset ℕ) (c : ℕ → ℝ),
    (∀ d, |c d|≤1) → (∀ d, c d≠0 → d≤N) →
    ‖trimReserve (pairLicence hb hs hgap N) N N kappa0 S (fun d => (c d:ℂ))‖
      ≤ C*(Y:ℝ)*(N:ℝ)^(2*eps) := by
  obtain ⟨B,hB,hwords⟩ := P4BActualUpperTrimPayment.exists_lowPrimeWords_card_budget
    2 (by norm_num) heps
  obtain ⟨D,hD,hrows⟩ := exists_row_bound eps heps
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro b kappa s kappa0 hb hs hgap N Y hN hYN hcut S c hc hrange
  let L := pairLicence hb hs hgap N
  let R := D*(N:ℝ)^eps
  have hR : 0≤R := mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have heq : (N:ℝ)^eps*(N:ℝ)^eps=(N:ℝ)^(2*eps) := by
    rw [← Real.rpow_add hNr,two_mul]
  calc
    _ ≤ ∑ ps∈primeTuples N 2,
        ‖((1-(eta ((ps.prod:ℝ)/(N:ℝ)^(1-kappa0)):ℂ))*(listExtension L ps:ℂ))*
          wordKernel S (fun d => (c d:ℂ)) N ps‖ := norm_sum_le _ _
    _ ≤ ∑ ps∈primeTuples N 2, if ps.prod≤Y then R else 0 := by
      apply Finset.sum_le_sum
      intro ps hps
      by_cases hlow : ps.prod≤Y
      · rw [if_pos hlow,norm_mul]
        have hfactor := P4BActualUpperTrimPayment.actual_trim_factor_norm_le hb
          (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs
          (by simpa only [one_mul] using hgap) N kappa0 ps
        have hrow := hrows N hN S c hc hrange ps.prod (hlow.trans_lt hYN)
        rw [← P4BActualUpperTrimPayment.wordKernel_eq_signedRow] at hrow
        exact (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans
          ((one_mul _).le.trans hrow)
      · have hp : 2*(N:ℝ)^(1-kappa0)≤(ps.prod:ℝ) :=
          hcut.trans (by exact_mod_cast (lt_of_not_ge hlow).le)
        have htrim := P5Z.ActualEtaPsiOccurrenceBudget.eta_one
          ((le_div_iff₀ (Real.rpow_pos_of_pos hNr _)).mpr hp)
        simp only [if_neg hlow,htrim,Complex.ofReal_one,sub_self,zero_mul,norm_zero,le_refl]
    _ = ((P4BActualUpperTrimPayment.lowPrimeWords N 2 Y).card:ℝ)*R := by
      rw [← Finset.sum_filter]
      simp only [P4BActualUpperTrimPayment.lowPrimeWords,Finset.sum_const,nsmul_eq_mul]
    _ ≤ ((Y:ℝ)*(B*(N:ℝ)^eps))*R := mul_le_mul_of_nonneg_right (hwords N N Y hYN.le) hR
    _ = _ := by
      dsimp only [R]
      rw [← heq]
      ring

/-- Exact signed difference at the original labelled tuples, with the
target in the count and coprime mean. This is the trim term appearing
in the original group HB decomposition. -/
theorem difference_eq_trim {b kappa s : ℝ} {N : ℕ}
    (hb : 0<b) (hs : 0<s) (hgap : 2*s≤baseline b kappa-19/96) (hN : 2≤N)
    (kappa0 : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    ((Part3.primeProductSignedError 2 N N S c (weight b kappa s N)-
       Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℝ):ℂ) =
      trimReserve (pairLicence hb hs hgap N) N N kappa0 S (fun d => (c d:ℂ)) := by
  let L := pairLicence hb hs hgap N
  let F := fun ps : List ℕ => (1-eta ((ps.prod:ℝ)/(N:ℝ)^(1-kappa0)))*listExtension L ps
  have hweight (u) (hu : u∈Part3.labelledPrimeTuples 2 N) :
      weight b kappa s N u = listExtension L (sourceWord u) := by
    have hp : ∀ i, Nat.Prime (u i).val := (Finset.mem_filter.mp hu).2
    rw [sourceWord,listExtension_ofFn,integerExtension_eq_on_primes L _ hp]
    exact P4BArbitraryWidthUpperPairProfile.original_caller b kappa s hN u hu
  have hdiff :
      Part3.primeProductSignedError 2 N N S c (weight b kappa s N)-
      Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N) =
      Part3.primeProductSignedError 2 N N S c (fun u => F (sourceWord u)) := by
    unfold Part3.primeProductSignedError
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← mul_sub,← Finset.sum_sub_distrib]
    apply congrArg (fun v : ℝ => c d*v)
    apply Finset.sum_congr rfl
    intro u hu
    simp only [F,trimmedWeight,sourceWord_product,← hweight u hu]
    ring
  rw [hdiff,original_prime_discrepancy_words]
  change (∑ ps∈primeTuples N 2, (F ps:ℂ)*wordKernel S (fun d => (c d:ℂ)) N ps) = _
  unfold trimReserve
  apply Finset.sum_congr rfl
  intro ps hps
  simp only [F,L,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]

/-- The final rectangles in the physical schedule have strict exponent
599/1000. The only external datum is that pointwise support fact at N.
The cutoff, product, actual coefficient size, and full signed trim budget
are all derived here. -/
theorem eventually_signed_trim (kappa0 : ℝ) (hk : 0<kappa0) (hk1 : kappa0<1)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kappa s : ℝ),0<b → 0<s →
      2*s≤baseline b kappa-19/96 →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      let S := Q omega N
      let c := coefficient m r n e q a omega k N level
      (∀ d : ℕ, c d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) →
      |Part3.primeProductSignedError 2 N N S c (weight b kappa s N)-
        Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N)|
        ≤ delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  let eps := kappa0/4
  have heps : 0<eps := by dsimp only [eps]; positivity
  obtain ⟨C,hC,hbound⟩ := exists_trim_bound eps heps
  filter_upwards [P5OriginalSingletonLowerTrimPaid.eventually_originalLowerCut_lt kappa0 hk hk1,
    eventually_powerLog_le_logAccuracy (3*C) (1-kappa0/2) 0 A (by linarith) delta hd,
    eventually_ge_atTop (2:ℕ)] with N hcut hcost hN
  intro b kappa s hb hs hgap m r n e q a omega k level
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N level
  have hh1 : 1≤N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast hh1
  have hcap : (N:ℝ)^(599/1000:ℝ)≤N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
      (show (599/1000:ℝ)≤1 by norm_num)
  have hc (d : ℕ) : |c d|≤1 :=
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ _
  have hsmall (d : ℕ) (hnz : c d≠0) : d≤N := by
    exact_mod_cast (hrange d hnz).le.trans hcap
  let Y := P5OriginalSharpPrime.originalLowerCut kappa0 N
  have ht := hbound b kappa s kappa0 hb hs hgap N Y hh1 hcut.1
    (Nat.le_ceil _) (Q omega N) c hc hsmall
  have hpower : (N:ℝ)^(1-kappa0)*(N:ℝ)^(2*eps)=(N:ℝ)^(1-kappa0/2) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hNr)]
    congr 1
    dsimp only [eps]
    ring
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcut.2 hC.le) (Real.rpow_nonneg (Nat.cast_nonneg N) (2*eps))
  have herr : ‖trimReserve (pairLicence hb hs hgap N) N N kappa0
      (Q omega N) (fun d => (c d:ℂ))‖ ≤ delta*(N:ℝ)/Real.log (N:ℝ)^A := by
    calc
      _ ≤ C*(Y:ℝ)*(N:ℝ)^(2*eps) := ht
      _ ≤ C*(3*(N:ℝ)^(1-kappa0))*(N:ℝ)^(2*eps) := hp
      _ = (3*C)*((N:ℝ)^(1-kappa0)*(N:ℝ)^(2*eps)) := by ring
      _ = (3*C)*(N:ℝ)^(1-kappa0/2) := by rw [hpower]
      _ ≤ _ := by simpa only [pow_zero,mul_one] using hcost
  rw [← difference_eq_trim hb hs hgap hN] at herr
  simpa only [Complex.norm_real,Real.norm_eq_abs] using herr

end
end ImbalancedChen.P4BOriginalFiniteSignedTrim
