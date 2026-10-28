import ImbalancedChen.P5OriginalSingletonLowerTrimPaid
import ImbalancedChen.P5ActualSingletonPrimeTestFamily
import ImbalancedChen.P2OriginalCanonicalPairTentBank

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
A real computed canonical TENT subbank supplies the chronological lower
retainEven predicate; the production original lower source supplies its
rho and independent prime testword u of rank ONE. This is not the full
adopted W/L5/L6 bank. The full smooth caller uses prime cap 2*N, never a
sharp truncation at N masquerading as a smooth Family. Both exact source
reserves are retained. The low reserve is paid; the broad upper collar
has only the explicit arithmetic majorant stated below, not log saving.
-/
namespace ImbalancedChen.P5CanonicalTentIndependentSingletonCaller
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P2OriginalPairSourceReceiver
open P5OriginalSharpPrime P5OriginalPrimeEndpoint
open P5OriginalSingletonLowerTrimPaid

def keep (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) (N : ℕ) :
    List ℕ → Bool :=
  P2LowerCapPlanIntegerRetention.retainEven
    (P2OriginalCanonicalPairTentBank.plan R mesh buffer seed)
    (R.epsilon : ℝ) (ceiling : ℝ) (seed : ℝ) N

def lowerRho (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  actualLowerSmallRoughRho (keep R mesh buffer seed N) N cap w z L

def activeModuli (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  P5S1OriginalLower.active (keep R mesh buffer seed N) N cap w z L

-- Reintroducing inactive moduli is exact for BOTH count and mean. This
-- is a coefficient identity, not a distribution estimate for arbitrary W.
theorem actual_lower_full_Q_eq_active (retainEven : List ℕ → Bool)
    (N cap r P : ℕ) (w z L : ℝ)
    (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L) W =
    Part3.primeProductSignedError r P N
      (P5S1OriginalLower.active retainEven N cap w z L)
      (actualLowerSmallRoughRho retainEven N cap w z L) W := by
  unfold Part3.primeProductSignedError
  exact P5S1OriginalLower.sum_eq_active retainEven N cap w z L _

theorem keep_cons_iff (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (N p : ℕ) (history : List ℕ) :
    keep R mesh buffer seed N (p :: history) = true ↔
      keep R mesh buffer seed N history = true ∧
      P2LowerCapPlanIntegerRetention.admission
        (P2LowerCapPlanIntegerRetention.integerTrace
          (P2OriginalCanonicalPairTentBank.plan R mesh buffer seed)
          (R.epsilon : ℝ) (ceiling : ℝ) (seed : ℝ) N history)
        (P2LowerCapPlanIntegerRetention.coordinate N p) :=
  P2LowerCapPlanIntegerRetention.retainEven_cons_iff _ _ _ _ _ _ _

-- The coefficient's causal plan is concrete, while the tested prime u
-- comes from the independently defined ORIGINAL Chen prime prefix.
theorem canonical_causal_original_receiver (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (N cap : ℕ) (w z L : ℝ) (hEven : Even N)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum
          (actualLowerSmallRoughModuli (keep R mesh buffer seed N) N cap w z)
          (lowerRho R mesh buffer seed N cap w z L) +
      Part3.primeProductSignedError 1 N N
        (activeModuli R mesh buffer seed N cap w z L)
        (lowerRho R mesh buffer seed N cap w z L)
        (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
      chenInitialCorrectionCost N (activeModuli R mesh buffer seed N cap w z L) ≤
        ((chenSiftedPrimeSource N z).card : ℝ) :=
  P5S1SingletonPP.causal_PP_lower (keep R mesh buffer seed N) N cap w z L
    hEven hL hwL hwz hzcap

def smoothNatural (beta : ℝ) (N p : ℕ) : ℝ :=
  P5Z.ActualSingletonPrimeTestFamily.profile beta N (fun _ : Fin 1 => (p : ℝ))

def fullSmoothWeight (beta : ℝ) (N : ℕ) : (Fin 1 → Fin (2*N+1)) → ℝ :=
  P5S1SingletonPP.singletonWeight (2*N) (smoothNatural beta N)

theorem fullSmoothWeight_eq_actual_profile (beta : ℝ) (N : ℕ)
    (u : Fin 1 → Fin (2*N+1)) :
    fullSmoothWeight beta N u =
      P5Z.ActualSingletonPrimeTestFamily.profile beta N (fun i => ((u i).val : ℝ)) := by
  rfl

theorem smoothNatural_range (beta : ℝ) (N p : ℕ) :
    0 ≤ smoothNatural beta N p ∧ smoothNatural beta N p ≤ 1 :=
  P5Z.ActualSingletonPrimeTestFamily.profile_bounds beta N _

theorem smoothNatural_original_plateau {N : ℕ} (hN : 2 ≤ N)
    (kappa : ℝ) (p : ℕ) (hp : p ∈ chenPrimePrefix N)
    (htrim : originalLowerCut kappa N < p) :
    smoothNatural (1-kappa) N p = 1 := by
  have hceil : 2 * (N : ℝ)^(1-kappa) ≤
      (originalLowerCut kappa N : ℝ) := Nat.le_ceil _
  have hlo : 2 * (N : ℝ)^(1-kappa) ≤ (p : ℝ) :=
    hceil.trans (by exact_mod_cast htrim.le)
  have hhi : (p : ℝ) ≤ N := by exact_mod_cast (mem_chenPrimePrefix.mp hp).1
  exact P5Z.ActualSingletonPrimeTestFamily.profile_one_on_original_range
    (1-kappa) hN _ hlo hhi

-- This is the actual independent rank-one licence and real Family
-- fields. No physical-prefix rank or missing independent rank is added.
theorem actual_singleton_family_fields (kappa : ℝ) (hkappa1 : kappa < 1) :
    P5Z.ActualSingletonPrimeTestFamily.SingletonFamilyFields (1-kappa) :=
  P5Z.ActualSingletonPrimeTestFamily.singleton_family_fields (by linarith)

def actual_singleton_licence (kappa : ℝ) (N : ℕ) :=
  P5Z.ActualSingletonPrimeTestFamily.singletonLicence (1-kappa) N

def upperCollar (beta : ℝ) (N p : ℕ) : ℝ :=
  if N < p then smoothNatural beta N p else 0

def upperPrimeSource (N : ℕ) : Finset ℕ :=
  (chenPrimePrefix (2*N)).filter (fun p => N < p)

theorem full_smooth_PP_prefix_split (beta : ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 (2*N) N Q rho (fullSmoothWeight beta N) =
      Part3.primeProductSignedError 1 N N Q rho
        (P5S1SingletonPP.singletonWeight N (smoothNatural beta N)) +
      Part3.primeProductSignedError 1 (2*N) N Q rho
        (P5S1SingletonPP.singletonWeight (2*N) (upperCollar beta N)) := by
  simp only [fullSmoothWeight, P5S1SingletonPP.primeProductSignedError_singleton_eq]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  apply congrArg (fun x : ℝ => rho q * x)
  let low : ℕ → ℝ := fun p => if p ≤ N then smoothNatural beta N p else 0
  have hsub : chenPrimePrefix N ⊆ chenPrimePrefix (2*N) := by
    intro p hp
    have hd := mem_chenPrimePrefix.mp hp
    exact mem_chenPrimePrefix.mpr ⟨by omega, hd.2⟩
  have hlow : finitePrimitiveDiscrepancy (chenPrimePrefix (2*N)) low N q =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (smoothNatural beta N) N q := by
    rw [finitePrimitiveDiscrepancy_eq_of_subset (chenPrimePrefix N)
      (chenPrimePrefix (2*N)) low N q hsub]
    · apply finitePrimitiveDiscrepancy_congr
      intro p hp
      simp only [low, if_pos (mem_chenPrimePrefix.mp hp).1]
    · intro p hp hn
      have hnot : ¬ p ≤ N := by
        intro h
        exact hn (mem_chenPrimePrefix.mpr ⟨h, (mem_chenPrimePrefix.mp hp).2⟩)
      exact if_neg hnot
  rw [← hlow, ← finitePrimitiveDiscrepancy_add]
  apply finitePrimitiveDiscrepancy_congr
  intro p hp
  by_cases h : p ≤ N
  · simp [low, upperCollar, h, Nat.not_lt.mpr h]
  · simp [low, upperCollar, h, Nat.lt_of_not_ge h]

theorem original_prime_source_exact_reserves {N : ℕ} (hN : 2 ≤ N)
    (kappa : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 N N Q rho
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) =
      Part3.primeProductSignedError 1 (2*N) N Q rho
        (fullSmoothWeight (1-kappa) N) +
      Part3.primeProductSignedError 1 N N Q rho
        (P5S1SingletonPP.singletonWeight N
          (lowerTrim N (originalLowerCut kappa N) (smoothNatural (1-kappa) N))) -
      Part3.primeProductSignedError 1 (2*N) N Q rho
        (P5S1SingletonPP.singletonWeight (2*N) (upperCollar (1-kappa) N)) := by
  have hlo := original_singleton_eq_smooth_add_lowerTrim N
    (originalLowerCut kappa N) Q rho (smoothNatural (1-kappa) N)
    (fun p hp ht => smoothNatural_original_plateau hN kappa p hp ht)
  have hhi := full_smooth_PP_prefix_split (1-kappa) N Q rho
  linarith

theorem upperCollar_PP_eq_source (beta : ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 (2*N) N Q rho
      (P5S1SingletonPP.singletonWeight (2*N) (upperCollar beta N)) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy
        (upperPrimeSource N) (smoothNatural beta N) N q := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq]
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun x : ℝ => rho q * x)
  rw [finitePrimitiveDiscrepancy_eq_of_subset (upperPrimeSource N)
    (chenPrimePrefix (2*N)) (upperCollar beta N) N q (Finset.filter_subset _ _)]
  · apply finitePrimitiveDiscrepancy_congr
    intro p hp
    exact if_pos (Finset.mem_filter.mp hp).2
  · intro p hp hn
    have hnot : ¬ N < p := fun h => hn (Finset.mem_filter.mpr ⟨hp, h⟩)
    exact if_neg hnot

-- The broad upper collar is visible in the REAL same-rho functional.
-- This explicit O(N log N) majorant is NOT called a negligible reserve.
theorem actual_upperCollar_arithmetic_bound (beta : ℝ)
    (retainEven : List ℕ → Bool) (N cap M : ℕ) (w z L : ℝ)
    (Q : Finset ℕ) (hQ : Q ⊆ Finset.Icc 1 M) :
    |Part3.primeProductSignedError 1 (2*N) N Q
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (P5S1SingletonPP.singletonWeight (2*N) (upperCollar beta N))| ≤
      2*(N : ℝ)*(1+Real.log (N : ℝ)) +
        8*(N : ℝ)*(1+Real.log (max 1 (M : ℝ))) := by
  have hsource : ∀ p ∈ upperPrimeSource N, p ≠ N ∧ distance N p ≤ N := by
    intro p hp
    obtain ⟨hp, hNp⟩ := Finset.mem_filter.mp hp
    have hp2N := (mem_chenPrimePrefix.mp hp).1
    refine ⟨hNp.ne', ?_⟩
    simp only [distance, if_neg (not_le.mpr hNp)]
    omega
  have hdelta : ∀ p ∈ upperPrimeSource N, |smoothNatural beta N p| ≤ 1 := by
    intro p hp
    have hr := smoothNatural_range beta N p
    simpa only [abs_of_nonneg hr.1] using hr.2
  have hrho : ∀ q ∈ Q, |actualLowerSmallRoughRho retainEven N cap w z L q| ≤ 1 :=
    fun q hq => actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q
  have hrec : (∑ q ∈ Q,
      |actualLowerSmallRoughRho retainEven N cap w z L q| / (Nat.totient q : ℝ)) ≤
      4*(1+Real.log (max 1 (M : ℝ))) := by
    refine le_trans ?_ (sum_reciprocal_totient_subset_le_log Q M hQ)
    apply Finset.sum_le_sum
    intro q hq
    exact div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _)
  rw [upperCollar_PP_eq_source]
  have hb := abs_signed_primitive_endpoint_le (upperPrimeSource N) Q
    (actualLowerSmallRoughRho retainEven N cap w z L) (smoothNatural beta N)
    N N hsource hrho hdelta
  have hc := endpoint_card_le (upperPrimeSource N) N N hsource
  have hrec0 : 0 ≤ ∑ q ∈ Q,
      |actualLowerSmallRoughRho retainEven N cap w z L q| / (Nat.totient q : ℝ) :=
    Finset.sum_nonneg (fun q hq => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hm := mul_le_mul hc hrec hrec0 (by positivity : 0 ≤ 2*(N : ℝ))
  have hd := mul_le_mul_of_nonneg_left (sum_divisors_card_le_log N)
    (by norm_num : (0 : ℝ) ≤ 2)
  exact hb.trans ((add_le_add hd hm).trans_eq (by ring))

theorem canonical_tent_lower_reserve_logAccuracy (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
      (cap M : ℕ) (w z L : ℝ), M ≤ N →
      (∀ q ∈ activeModuli R mesh buffer seed N cap w z L, q ≤ M) →
      |Part3.primeProductSignedError 1 N N
        (activeModuli R mesh buffer seed N cap w z L)
        (lowerRho R mesh buffer seed N cap w z L)
        (P5S1SingletonPP.singletonWeight N
          (lowerTrim N (originalLowerCut kappa N) (smoothNatural (1-kappa) N)))| ≤
        eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_actual_lowerTrim_logAccuracy
    kappa hkappa hkappa1 A eta heta] with N hN
  intro R mesh buffer seed cap M w z L hMN hcap
  have hQ : activeModuli R mesh buffer seed N cap w z L ⊆ Finset.Icc 1 M := by
    intro q hq
    have hd := P5S1SingletonPP.active_physical_data
      (keep R mesh buffer seed N) N cap w z L hq
    exact Finset.mem_Icc.mpr ⟨hd.1, hcap q hq⟩
  exact hN (keep R mesh buffer seed N) cap N M w z L
    (activeModuli R mesh buffer seed N cap w z L) (smoothNatural (1-kappa) N)
    le_rfl hMN hQ (fun p hp => smoothNatural_range _ _ _)

end
end ImbalancedChen.P5CanonicalTentIndependentSingletonCaller
