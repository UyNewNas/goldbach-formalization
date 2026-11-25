import ImbalancedChen.P3OriginalPrimeRoughThreshold
import ImbalancedChen.P5OriginalU5AllMarkSmoothing
import ImbalancedChen.P5WordKernelSignedRow
import ImbalancedChen.P5ProperPowerSignedModulusPayment
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-! The original rough projector kills every complete even product
before a signed count or a coprime mean is estimated. The uncapped
all-mark U5 modulus carrier therefore incurs no diagonal cost. -/
namespace ImbalancedChen.P5OriginalU5AllMarkHBReserves
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (Policy moduli integerRho)
open P5OriginalU5AllMarkCosts
open P5CanonicalTentNarrowSingletonTransfer
open P5Z.OriginalChartRoughCutoff (argument chartCutoff roughF)
open P5Z.ActualLabelledPrimeSmoothCharts P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open Part3.OriginalProperPowerActualChart (integerWords)
open Part3.OriginalProperPowerChartCount (properPowers properPowers_card_le)
open Part3.AllKLambdaChartCorrection Part3.AllKFamilyLambdaCorrectionBound
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ProperPowerSignedModulusPayment (norm_signedRow_le rowBudget meanBudget)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (fouvryTau_two)

/-- All ranks and all charts, with the same pre-HB number used in their rows. -/
theorem original_cutoff_two_lt (K : ℕ) (js : List ℕ) : 2 < beforeHBCutoff K js := by
  have hprod : 1 ≤ (scales js).prod := by
    induction js with
    | nil => simp [scales]
    | cons j js ih =>
      change 1 ≤ (2 : ℝ)^j * (scales js).prod
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) ih
  have hf : (4 : ℝ) ≤ 2^(6*K+2) := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ 6*K+2 by omega)
  apply P3OriginalPrimeRoughThreshold.two_lt_rough_threshold
  change 4 ≤ (2 : ℝ)^(6*K+2) * (2^(scales js).length * (scales js).prod)
  exact hf.trans (le_mul_of_one_le_right (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hprod))

theorem rough_product_even_zero {z : ℝ} (hz : 2 ≤ z) (ps : List ℕ)
    (h : 2 ∣ ps.prod) : roughWord z ps = 0 := by
  induction ps with
  | nil => simp at h
  | cons m ps ih =>
    rcases Nat.prime_two.dvd_mul.mp (by simpa only [List.prod_cons] using h) with hm | hp
    · have he : Part3.roughOneSlot z m = 0 := by
        by_contra hn
        exact (not_lt_of_ge hz) (Part3.roughOneSlot_support z m hn 2 Nat.prime_two hm)
      simp [roughWord, he]
    · simp [roughWord, ih hp]

theorem original_even_collision_zero {N : ℕ} (hev : Even N) (K : ℕ) (js ps : List ℕ)
    (hp : ps.prod = N) :
    roughWord (beforeHBCutoff K js) ps = 0 := by
  apply rough_product_even_zero (original_cutoff_two_lt K js).le
  rw [hp]
  exact even_iff_two_dvd.mp hev

private theorem asSingleton {s : List ℕ} (h : s.length = 1) : ∃ n, s = [n] := by
  cases s with
  | nil => simp at h
  | cons n ns =>
    have he : ns = [] := List.length_eq_zero.mp (by simpa using h)
    exact ⟨n,by rw [he]⟩

private theorem single_value (t : ℝ) (B N n : ℕ) :
    listExtension (actualLicence t B N) [n] = smoothNatural t B N n := rfl

private theorem hprofile (t : ℝ) (B : ℕ) {N : ℕ} (hN : 2 ≤ N) {n : ℕ}
    (ha : listExtension (actualLicence t B N) [n] ≠ 0) :
    (N : ℝ)^(1-t) < n := by
  have hd := P5Z.ActualSingletonLogCollarFamily.logWidth_bounds B hN
  exact (P5Z.ActualSingletonLogCollarFamily.profile_support_short (1-t) hd.1 hd.2
    (show P5Z.ActualSingletonLogCollarFamily.profile (1-t)
      (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N (fun _ => (n : ℝ)) ≠ 0 from ha)).2.1

/-- Selecting the source lower smoothing after the HB trim scale makes
the literal complete-product trim zero, uniformly on every mark. -/
theorem eventually_original_trim_zero (t tau : ℝ) (ht : t < tau) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ),
      trimReserve (actualLicence t B N) (2*N) N tau Q rho = 0 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    ((tendsto_rpow_atTop (sub_pos.mpr ht)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with N hN hs
  intro B Q rho
  apply Finset.sum_eq_zero
  intro ps hps
  obtain ⟨n,rfl⟩ := asSingleton (primeTuples_spec _ _ hps).1
  by_cases hL : listExtension (actualLicence t B N) [n] = 0
  · simp [hL]
  have hn := hprofile t B hN hL
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : 2*(N : ℝ)^(1-tau) ≤ (n : ℝ) := by
    calc
      _ ≤ (N : ℝ)^(tau-t)*(N : ℝ)^(1-tau) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hNr.le _)
      _ = (N : ℝ)^(1-t) := by rw [← Real.rpow_add hNr]; congr 1; ring
      _ ≤ _ := hn.le
  have heta := P5Z.ActualEtaPsiOccurrenceBudget.eta_one
    ((le_div_iff₀ (Real.rpow_pos_of_pos hNr _)).mpr hm)
  simpa only [List.prod_cons, List.prod_nil, mul_one, heta, Complex.ofReal_one,
    sub_self, zero_mul]

private theorem proper_singleton_card (cap : ℕ) :
    (properChartWords cap 1).card ≤ (properPowers cap).card := by
  apply Finset.card_le_card_of_injOn List.prod
  · intro ps hps
    obtain ⟨hword,i,prime,j,hprime,hj,hid,_⟩ := properChartWords_spec hps
    have hw := words_spec (Finset.Icc 1 cap) 1 ps hword
    obtain ⟨n,rfl⟩ := asSingleton hw.1
    have hi : i.val = 0 := by omega
    have hn : n = prime^j := by simpa [hi] using hid
    simp only [List.prod_cons, List.prod_nil, mul_one]
    exact Finset.mem_filter.mpr ⟨hw.2 n (by simp),prime,j,hprime,hj,hn⟩
  · intro ps hps qs hqs h
    obtain ⟨n,rfl⟩ := asSingleton (words_spec _ _ _ (properChartWords_spec hps).1).1
    obtain ⟨m,rfl⟩ := asSingleton (words_spec _ _ _ (properChartWords_spec hqs).1).1
    simpa using h

/-- The complete modulus can exceed N. At nonzero distance its AP count
only sees divisors of that distance and its mean sees the full U5 primorial. -/
theorem exists_all_mark_row_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ {N : ℕ}, 2 ≤ N → Even N →
      ∀ (e : ℝ) (P : Policy), smallCutoff N e ≤ cutoff N →
      ∀ Q ⊆ moduli N e P, ∀ n ≤ 2*N, n ≠ N →
      ‖signedRow Q (fun q => ((integerRho N e P q : ℝ) : ℂ)) N n‖ ≤ E*(N : ℝ)^(1/4 : ℝ) := by
  obtain ⟨C,hC,htau⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1/4 by norm_num)
  obtain ⟨D,hD,hmass⟩ := exists_moduli_reciprocal_mass
  refine ⟨C+4*D, by positivity, ?_⟩
  intro N hN hev e P hw Q hQ n hn hne
  let rho := fun q => ((integerRho N e P q : ℝ) : ℂ)
  let d := P5OriginalPrimeEndpoint.distance N n
  have hd : 0 < d := P5OriginalPrimeEndpoint.distance_pos hne
  have hdN : d ≤ N := by
    dsimp [d,P5OriginalPrimeEndpoint.distance]
    split_ifs <;> omega
  have ht := htau d hd
  rw [fouvryTau_two] at ht
  have hdiv := ht.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
    (by exact_mod_cast hdN) (by norm_num : (0 : ℝ) ≤ 1/4)) hC.le)
  have hr (q : ℕ) (hq : q ∈ Q) : ‖rho q‖ ≤ 1 := by
    simpa only [rho,Complex.norm_real,Real.norm_eq_abs] using (full_modulus_data hN P hw (hQ hq)).2.1
  have hrec : meanBudget Q rho ≤ D*Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ q ∈ Q, 1/(Nat.totient q : ℝ) := Finset.sum_le_sum (fun q hq =>
        div_le_div_of_nonneg_right (hr q hq) (Nat.cast_nonneg _))
      _ ≤ ∑ q ∈ moduli N e P, 1/(Nat.totient q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hQ (by intros; positivity)
      _ ≤ _ := hmass N hN hev e P hw
  have hh := norm_signedRow_le Q rho 1 zero_le_one hr N n
  simp only [rowBudget,if_neg hne,one_mul] at hh
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (Nat.cast_nonneg N)
    (by norm_num : (0 : ℝ) < 1/4)) hD.le
  change ‖signedRow Q rho N n‖ ≤ _
  change ‖signedRow Q rho N n‖ ≤ (d.divisors.card : ℝ) + meanBudget Q rho at hh
  linarith only [hh, hdiv, hrec, hl]

private theorem chart_norm (t tau : ℝ) (B N n : ℕ) (js : List ℕ) :
    ‖originalChart (actualLicence t B N) N tau js [n]‖ ≤ 1 := by
  have hchi (x : ℝ) : 0 ≤ P5Z.ActualEtaPsiOccurrenceBudget.chi x ∧
      P5Z.ActualEtaPsiOccurrenceBudget.chi x ≤ 1 := by
    have hh := P5Z.ActualEtaPsiOccurrenceBudget.eta_bounds x
    unfold P5Z.ActualEtaPsiOccurrenceBudget.chi
    constructor <;> linarith only [hh.1,hh.2]
  have he (x : ℝ) : ‖(P5Z.ActualEtaPsiOccurrenceBudget.eta x : ℂ)‖ ≤ 1 := by
    have hh := P5Z.ActualEtaPsiOccurrenceBudget.eta_bounds x
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  have hw : ‖(listExtension (actualLicence t B N) [n] : ℂ)‖ ≤ 1 := by
    rw [single_value, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smooth_range t B N n).1]
    exact (smooth_range t B N n).2
  unfold originalChart chartTerm trimmedWeight
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (tupleProfile_norm_le_one _ hchi js [n])
    (mul_le_mul (he _) hw (norm_nonneg _) zero_le_one) (by positivity) zero_le_one).trans_eq
      (by norm_num)

/-- Each original proper-power chart is paid on its own physical carrier. -/
theorem exists_proper_chart_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ {N : ℕ}, 2 ≤ N → Even N → ∀ (e : ℝ) (P : Policy),
      smallCutoff N e ≤ cutoff N → ∀ Q ⊆ moduli N e P, ∀ (t tau : ℝ) (B K : ℕ) (js : List ℕ),
      ‖properPowerReserve (actualLicence t B N) K (2*N) N tau Q
        (fun q => ((integerRho N e P q : ℝ) : ℂ)) js‖ ≤
      (((Nat.sqrt (2*N)+1)*(Nat.log2 (2*N)+1) : ℕ) : ℝ)*(E*(N : ℝ)^(1/4 : ℝ)) := by
  obtain ⟨E,hE,hrow⟩ := exists_all_mark_row_bound
  refine ⟨E,hE,?_⟩
  intro N hN hev e P hw Q hQ t tau B K js
  let rho := fun q => ((integerRho N e P q : ℝ) : ℂ)
  let A := E*(N : ℝ)^(1/4 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcard := (proper_singleton_card (2*N)).trans (properPowers_card_le (by omega))
  unfold properPowerReserve
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ps ∈ properChartWords (2*N) 1, A := by
      apply Finset.sum_le_sum
      intro ps hps
      have hs := words_spec _ _ _ (properChartWords_spec hps).1
      obtain ⟨n,rfl⟩ := asSingleton hs.1
      have hlim := (Finset.mem_Icc.mp (hs.2 n (by simp))).2
      by_cases h : n = N
      · have hz := original_even_collision_zero hev K js [n] (by simpa using h)
        simpa only [hz,zero_mul,mul_zero,norm_zero] using hA
      · rw [P4BActualUpperTrimPayment.wordKernel_eq_signedRow]
        simp only [norm_mul,List.prod_cons,List.prod_nil,mul_one]
        have hh := hrow hN hev e P hw Q hQ n hlim h
        calc
          _ ≤ (1*1)*(1*A) := mul_le_mul
            (mul_le_mul (lambdaWord_norm_le_one [n]) (chart_norm t tau B N n js)
              (norm_nonneg _) zero_le_one)
            (mul_le_mul (roughWord_norm_le_one _ [n]) hh (norm_nonneg _) zero_le_one)
            (by positivity) (by norm_num)
          _ = _ := by ring
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hA

theorem eventually_all_mark_proper_sum_norm (p : ℕ) (tol : ℝ) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      ∀ Q ⊆ moduli N e P, ∀ (t tau : ℝ) (B K : ℕ),
      (∑ js ∈ chartBank (2*N) 1, ‖properPowerReserve (actualLicence t B N) K (2*N) N tau Q
        (fun q => ((integerRho N e P q : ℝ) : ℂ)) js‖) ≤ tol*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨E,hE,hchart⟩ := exists_proper_chart_bound
  let J : ℝ := 2 + 2 / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ : 0 < J := by dsimp [J]; positivity
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_one_le_nat_log,
    eventually_powerLog_le_logAccuracy (3*J^2*E) (3/4) 2 p (by norm_num) tol htol]
    with N hN hlog hpay
  intro hev e he he8 P Q hQ t tau B K
  have hw := (attachment_gates hN he he8).2.2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hj : ((Nat.log2 (2*N)+2 : ℕ) : ℝ) ≤ J*Real.log (N : ℝ) := by
    have hx : (2 : ℝ)^(Nat.log2 (2*N)) ≤ 2*(N : ℝ) := by
      exact_mod_cast Nat.log2_self_le (by omega : 2*N ≠ 0)
    have h := Real.log_le_log (by positivity) hx
    rw [Real.log_pow,Real.log_mul (by norm_num) hn.ne'] at h
    have hNlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2N
    have hj' : (Nat.log2 (2*N) : ℝ) ≤ (2*Real.log (N : ℝ))/Real.log 2 :=
      (le_div_iff₀ h2).mpr (by linarith only [h,hNlog])
    dsimp only [J]
    push_cast
    linarith only [hj',hlog]
  have hct : ((chartBank (2*N) 1).card : ℝ) ≤ J*Real.log (N : ℝ) := by
    simpa only [chartBank,P5Z.OriginalDyadicRankUnion.words_card,Finset.card_range,pow_one,
      cutoffIndex, Nat.add_assoc] using hj
  have hexp : ((Nat.log2 (2*N)+1 : ℕ) : ℝ) ≤ J*Real.log (N : ℝ) :=
    (Nat.cast_le.mpr (by omega : Nat.log2 (2*N)+1 ≤ Nat.log2 (2*N)+2)).trans hj
  have hsqrt : ((Nat.sqrt (2*N)+1 : ℕ) : ℝ) ≤ 3*Real.sqrt (N : ℝ) := by
    have h := Nat.sqrt_le' (2*N)
    have h' : (Nat.sqrt (2*N) : ℝ)^2 ≤ 2*(N : ℝ) := by exact_mod_cast h
    have hroot : (Nat.sqrt (2*N) : ℝ) ≤ 2*Real.sqrt (N : ℝ) :=
      (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
        (by nlinarith only [h', Real.sq_sqrt hn.le, hn.le])
    have hone : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by linarith)
    push_cast
    linarith
  let X := E*(N : ℝ)^(1/4 : ℝ)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hp : Real.sqrt (N : ℝ) * (N : ℝ)^(1/4 : ℝ) = (N : ℝ)^(3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
    norm_num
  have hprod := mul_le_mul hsqrt hexp (Nat.cast_nonneg _) (by positivity)
  have hsum := Finset.sum_le_sum (fun js (_ : js ∈ chartBank (2*N) 1) =>
    hchart hN hev e P hw Q hQ t tau B K js)
  rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_mul] at hsum
  refine hsum.trans ?_
  calc
    _ ≤ (J*Real.log (N : ℝ)) * ((3*Real.sqrt (N : ℝ)*(J*Real.log (N : ℝ)))*X) :=
      mul_le_mul hct (mul_le_mul_of_nonneg_right hprod hX) (by positivity) (by positivity)
    _ = (3*J^2*E)*(N : ℝ)^(3/4 : ℝ)*(Real.log (N : ℝ))^2 := by
      rw [← hp]; dsimp [X]; ring
    _ ≤ _ := hpay

private theorem eventually_active_rough_upper (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ)^a ≤ v → v ≤ C*N → roughF v < (N : ℝ)^a := by
  let L : ℝ := 1+2/a
  have hL : 1 ≤ L := by dsimp [L]; positivity
  have hLt : 2/a < L := by dsimp [L]; linarith
  filter_upwards [eventually_ge_atTop (2 : ℕ), tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop C), ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (Real.exp (Real.exp L)))] with N hN hCN hlarge
  intro v hv hvN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hN1
  have hv1 := (Real.one_lt_rpow hN1 ha).trans_le hv
  have hv2 : v ≤ (N : ℝ)^2 :=
    hvN.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_right hCN hNp.le)
  have hlog : Real.exp L ≤ Real.log v :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans hv1)).mpr (hlarge.trans hv)
  have hell := (Real.le_log_iff_exp_le (Real.log_pos hv1)).mpr hlog
  have hden := hLt.trans_le (hell.trans (le_self_pow₀ (hL.trans hell) (by norm_num : 3 ≠ 0)))
  have hpower : (1 : ℝ)/(Real.log (Real.log v))^3 < a/2 := by
    have hde : 0 < (Real.log (Real.log v))^3 := pow_pos (zero_lt_one.trans_le (hL.trans hell)) _
    apply (div_lt_iff₀ hde).mpr
    have hmul := (div_lt_iff₀ ha).mp hden
    linarith only [hmul]
  calc
    _ < v^(a/2) := Real.rpow_lt_rpow_of_exponent_lt hv1 hpower
    _ ≤ ((N : ℝ)^2)^(a/2) := Real.rpow_le_rpow (zero_lt_one.trans hv1).le hv2 (by positivity)
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num

/-- The pre-HB cutoff is fixed before the word. Its complete argument is
between the true source floor and a fixed multiple of N on occupied charts. -/
theorem eventually_original_rough_zero (t : ℝ) (ht : t < 1) (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (tau : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ),
      ∀ js ∈ chartBank (2*N) 1,
      roughPrimeReserve (actualLicence t B N) K (2*N) N tau Q rho js = 0 := by
  let F : ℝ := (2 : ℝ)^(6*K+2)
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_active_rough_upper (1-t) (8*F) (by linarith)] with N hN hcut
  intro B tau Q rho js hjs
  obtain ⟨j,rfl⟩ := asSingleton (words_spec _ _ _ hjs).1
  apply Finset.sum_eq_zero
  intro ps hps
  have hs := primeTuples_spec (2*N) 1 hps
  obtain ⟨n,rfl⟩ := asSingleton hs.1
  by_cases hw : originalChart (actualLicence t B N) N tau [j] [n] = 0
  · simp [hw]
  have hd := hw
  simp only [originalChart,chartTerm,trimmedWeight] at hd
  have htup := (mul_ne_zero_iff.mp hd).1
  have hWc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).2).2
  have hfloor := hprofile t B hN (n := n) (fun hz => hWc (by simp [hz]))
  have hwin := profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
    (fun _ hx => actual_chi_one hx) (fun _ hx => actual_chi_zero hx) [j] [n] htup
  have hw1 := (List.forall₂_cons.mp hwin).1
  have hnp := hs.2 n (by simp)
  have hn2 : (n : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hnp.2.2
  have harg : argument K (scales [j]) = F*(2*R j) := by simp [argument,scales,F]
  have ha : (N : ℝ)^(1-t) ≤ argument K (scales [j]) := by
    rw [harg]
    exact (hfloor.le.trans hw1.2.2).trans (le_mul_of_one_le_left (by positivity [R_pos j]) hF)
  have hb : argument K (scales [j]) ≤ (8*F)*(N : ℝ) := by
    rw [harg]
    calc
      _ ≤ F*(8*(N : ℝ)) := mul_le_mul_of_nonneg_left (by linarith only [hw1.2.1,hn2])
        (zero_le_one.trans hF)
      _ = _ := by ring
  have hz : beforeHBCutoff K [j] < (n : ℝ) := (hcut _ ha hb).trans hfloor
  have hrough := P5Z.OriginalPrimeAtlasReserveBranches.roughWord_one_on_prime_word
    (beforeHBCutoff K [j]) (ps := [n])
    (by intro m hm; simpa only [List.mem_singleton.mp hm] using hnp.1)
    (by intro m hm; simpa only [List.mem_singleton.mp hm] using hz)
  simp [hrough]

open P5Z.OriginalPrimeAtlasReserveBranches (mediumAtlas noMediumAtlas originalMediumLow originalMediumHigh)

def branches (t tau zeta : ℝ) (B N K : ℕ) (e : ℝ) (P : Policy) (Q : Finset ℕ) : ℂ :=
  let L := actualLicence t B N
  let rho := fun q => ((integerRho N e P q : ℝ) : ℂ)
  ∑ js ∈ chartBank (2*N) 1,
    (mediumAtlas L K (2*N) N tau (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js +
    noMediumAtlas L K (2*N) N tau (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js)

/-- All nonspectral corrections between the true smooth prime and its
original medium/no-medium decomposition are paid, across every U5 mark. -/
theorem eventually_smooth_to_branches (t tau : ℝ) (ht : t < 1) (htau : t < tau) (K p : ℕ)
    (tol : ℝ) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
    ∀ Q ⊆ moduli N e P, ∀ (B : ℕ) (zeta : ℝ),
    ‖(P5OriginalU5AllMarkSmoothing.smoothDiscrepancy t B N e P Q : ℂ) -
      branches t tau zeta B N K e P Q‖ ≤ tol*(N : ℝ)/(Real.log (N : ℝ))^p := by
  filter_upwards [eventually_original_trim_zero t tau htau, eventually_original_rough_zero t ht K,
    eventually_all_mark_proper_sum_norm p tol htol] with N htrim hrough hproper
  intro hev e he he8 P Q hQ B zeta
  let L := actualLicence t B N
  let rho := fun q => ((integerRho N e P q : ℝ) : ℂ)
  let S := chartBank (2*N) 1
  let m := fun js => mediumAtlas L K (2*N) N tau (originalMediumLow zeta js)
    (originalMediumHigh zeta js) Q rho js + noMediumAtlas L K (2*N) N tau
    (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js
  let f := fun js => properPowerReserve L K (2*N) N tau Q rho js
  have h := P5OriginalU5AllMarkSmoothing.smooth_original_atlas t B N K tau zeta e P Q
  change _ = trimReserve L (2*N) N tau Q rho + ∑ js ∈ S,
    (m js - f js + roughPrimeReserve L K (2*N) N tau Q rho js) at h
  rw [htrim B Q rho,zero_add] at h
  have hs : (∑ js ∈ S, (m js - f js + roughPrimeReserve L K (2*N) N tau Q rho js)) =
      (∑ js ∈ S, m js) - ∑ js ∈ S, f js := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun js hj => by rw [hrough B tau Q rho js hj,add_zero])
  rw [hs] at h
  change ‖_ - ∑ js ∈ S, m js‖ ≤ _
  rw [h, sub_sub_cancel_left, norm_neg]
  exact (norm_sum_le S f).trans (hproper hev e he he8 P Q hQ t tau B K)

/-- In particular this estimates the actual unpaid ledger from the old
short-rectangle production theorem, before its two remaining arithmetic branches. -/
theorem exists_original_complement_to_branches (t tau : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (htau : t < tau) (K p : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ zeta : ℝ,
      ‖(P5OriginalU5PlateauPrimeBV.remainingPrimitive N e P : ℂ) -
        branches t tau zeta (p+3) N K e P
          (moduli N e P \ P5OriginalU5PlateauPrimeBV.paidModuli N e P)‖ ≤
      D*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C,hC,hs⟩ := P5OriginalU5AllMarkSmoothing.exists_all_mark_smoothing t ht ht1 p
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hs,eventually_smooth_to_branches t tau ht1 htau K p 1 zero_lt_one]
    with N hS hB
  intro hev e he he8 P zeta
  let Q := moduli N e P \ P5OriginalU5PlateauPrimeBV.paidModuli N e P
  have hQ : Q ⊆ moduli N e P := Finset.sdiff_subset
  have h := hS hev e he he8 P Q hQ
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq] at h
  have hsc : ‖(P5OriginalU5PlateauPrimeBV.remainingPrimitive N e P : ℂ) -
      (P5OriginalU5AllMarkSmoothing.smoothDiscrepancy t (p+3) N e P Q : ℂ)‖ ≤
      C*(N : ℝ)/(Real.log (N : ℝ))^p := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact h
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hsc (hB hev e he he8 P Q hQ (p+3) zeta)).trans_eq (by ring))

end
end ImbalancedChen.P5OriginalU5AllMarkHBReserves
