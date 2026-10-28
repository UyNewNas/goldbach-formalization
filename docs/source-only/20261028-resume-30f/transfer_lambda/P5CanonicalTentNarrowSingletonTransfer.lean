import ImbalancedChen.P5CanonicalTentIndependentSingletonCaller
import ImbalancedChen.P5ActualSingletonLogCollarFamily

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The actual independent original singleton caller has BOTH its source
smoothing reserves paid. The full smooth source has prime cap 2*N and a
proved inverse-polylog upper collar; it is never silently cut off at N.
The coefficient is the original lower rho, including the true computed
canonical tent subplan when specialized below. No smooth PP estimate is
assumed, and no complete adopted/all-independent-rank claim is made.
-/
namespace ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P2OriginalPairSourceReceiver
open P5OriginalSharpPrime P5OriginalPrimeEndpoint
open P5OriginalSingletonLowerTrimPaid
open P5CanonicalTentIndependentSingletonCaller (keep lowerRho activeModuli)

def smoothNatural (kappa : ℝ) (B N p : ℕ) : ℝ :=
  P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
    (fun _ : Fin 1 => (p : ℝ))

def fullSmoothWeight (kappa : ℝ) (B N : ℕ) : (Fin 1 → Fin (2*N+1)) → ℝ :=
  P5S1SingletonPP.singletonWeight (2*N) (smoothNatural kappa B N)

def actualLicence (kappa : ℝ) (B N : ℕ) :=
  P5Z.ActualSingletonLogCollarFamily.singletonLicence (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N

theorem actual_family_fields (kappa : ℝ) (hkappa1 : kappa < 1) (B : ℕ) :
    P5Z.ActualSingletonLogCollarFamily.LogCollarFamilyFields (1-kappa) B :=
  P5Z.ActualSingletonLogCollarFamily.logWidth_family_fields (by linarith) B

-- Lambda/proper-power comparison uses the REAL integer bank, rather
-- than obtaining a false finiteness claim by deleting composite inputs.
theorem actual_finite_integer_support (kappa : ℝ) (B N : ℕ) :
    Set.Finite {u : Fin 1 → ℕ |
      P5Z.ActualSingletonLogCollarFamily.integerWeight (1-kappa)
        (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N u ≠ 0} := by
  let bank : Finset (Fin 1 → ℕ) := Fintype.piFinset (fun _ => Finset.range (2*N+1))
  apply bank.finite_toSet.subset
  intro u hu
  have hN : 2 ≤ N := by
    by_contra h
    exact hu (by simp [P5Z.ActualSingletonLogCollarFamily.integerWeight,
      P5Z.ActualSingletonLogCollarFamily.profile, h])
  have hd := P5Z.ActualSingletonLogCollarFamily.logWidth_bounds B hN
  have hs := P5Z.ActualSingletonLogCollarFamily.profile_support_short
    (1-kappa) hd.1 hd.2 hu
  apply Finset.mem_piFinset.mpr
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  have htwo : (u 0 : ℝ) < 2*(N : ℝ) :=
    hs.2.2.trans_le (by nlinarith [show (0 : ℝ) ≤ N by positivity])
  have hcast : (u 0 : ℝ) < ((2*N+1 : ℕ) : ℝ) := by push_cast; linarith
  simpa [hi] using (Finset.mem_range.mpr (by exact_mod_cast hcast))

theorem fullSmoothWeight_eq_actual_profile (kappa : ℝ) (B N : ℕ)
    (u : Fin 1 → Fin (2*N+1)) :
    fullSmoothWeight kappa B N u =
      P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
        (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
        (fun i => ((u i).val : ℝ)) := by rfl

theorem original_count_mean_receiver (kappa : ℝ) (B N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 (2*N) N Q rho (fullSmoothWeight kappa B N) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix (2*N))
        (smoothNatural kappa B N) N q :=
  P5S1SingletonPP.primeProductSignedError_singleton_eq (2*N) N Q rho _

def upperWidth (B N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) * P5Z.ActualSingletonLogCollarFamily.logWidth B N)

theorem upperWidth_le_original_endpoint (B : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    upperWidth B N ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ)^B) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hlogle : Real.log (N : ℝ) ≤ Real.log ((N : ℝ)+2) :=
    Real.log_le_log (zero_lt_one.trans hNr) (by linarith)
  have hpow := pow_le_pow_left₀ hlog.le hlogle B
  have hinv : 1 / Real.log ((N : ℝ)+2)^B ≤ 1 / Real.log (N : ℝ)^B :=
    one_div_le_one_div_of_le (pow_pos hlog B) hpow
  have hw := (P5Z.ActualSingletonLogCollarFamily.logWidth_le_inverse_log B hN).trans hinv
  apply Nat.ceil_mono
  simpa only [upperWidth, div_eq_mul_inv, one_div] using
    mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg N)

theorem smooth_range (kappa : ℝ) (B N p : ℕ) :
    0 ≤ smoothNatural kappa B N p ∧ smoothNatural kappa B N p ≤ 1 :=
  P5Z.ActualSingletonLogCollarFamily.profile_bounds _ _ _ _

theorem original_middle {N : ℕ} (hN : 2 ≤ N) (kappa : ℝ) (B p : ℕ)
    (hp : originalLowerCut kappa N < p) (hpN : p ≤ N) :
    smoothNatural kappa B N p = 1 := by
  have hd := P5Z.ActualSingletonLogCollarFamily.logWidth_bounds B hN
  have hceil : 2*(N : ℝ)^(1-kappa) ≤ (originalLowerCut kappa N : ℝ) := Nat.le_ceil _
  have hlo : 2*(N : ℝ)^(1-kappa) ≤ (p : ℝ) :=
    hceil.trans (by exact_mod_cast hp.le)
  exact P5Z.ActualSingletonLogCollarFamily.profile_one_on_original_range
    (1-kappa) hd.1 hN _ hlo (by exact_mod_cast hpN)

theorem original_upper_tail {N : ℕ} (hN : 2 ≤ N) (kappa : ℝ) (B p : ℕ)
    (hp : N + upperWidth B N < p) : smoothNatural kappa B N p = 0 := by
  have hd := P5Z.ActualSingletonLogCollarFamily.logWidth_bounds B hN
  have hceil : (N : ℝ) * P5Z.ActualSingletonLogCollarFamily.logWidth B N ≤
      (upperWidth B N : ℝ) := Nat.le_ceil _
  have hpR : (N : ℝ) + (upperWidth B N : ℝ) < p := by exact_mod_cast hp
  have hu : (N : ℝ) * (1+P5Z.ActualSingletonLogCollarFamily.logWidth B N) ≤ p := by
    nlinarith
  exact P5Z.ActualSingletonLogCollarFamily.profile_zero_above
    (1-kappa) hd.1 hd.2 N _ hu

-- These are the ORIGINAL exact signed reserves at the SAME Q and rho.
-- upperReserve retains the p=N collision within the original difference;
-- the even-target endpoint theorem later excludes it on its prime carrier.
def lowerReserve (kappa : ℝ) (B N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  Part3.primeProductSignedError 1 (2*N) N Q rho
    (P5S1SingletonPP.singletonWeight (2*N)
      (lowerTrim N (originalLowerCut kappa N) (smoothNatural kappa B N)))

def upperReserve (kappa : ℝ) (B N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  Part3.primeProductSignedError 1 (2*N) N Q rho
    (P5S1SingletonPP.singletonWeight (2*N) (sharp N)) -
  Part3.primeProductSignedError 1 (2*N) N Q rho
    (P5S1SingletonPP.singletonWeight (2*N)
      (patched N (originalLowerCut kappa N) (smoothNatural kappa B N)))

theorem original_source_exact_reserves (kappa : ℝ) (B N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 N N Q rho
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) =
      Part3.primeProductSignedError 1 (2*N) N Q rho (fullSmoothWeight kappa B N) +
        lowerReserve kappa B N Q rho + upperReserve kappa B N Q rho := by
  have hs := singleton_sharp_eq_original (2*N) N (by omega) Q rho
  have hp := patched_PP_eq_smooth_add_lowerTrim (2*N) N
    (originalLowerCut kappa N) Q rho (smoothNatural kappa B N)
  change _ = _ + _ + (_ - _)
  change Part3.primeProductSignedError 1 (2*N) N Q rho
      (P5S1SingletonPP.singletonWeight (2*N)
        (patched N (originalLowerCut kappa N) (smoothNatural kappa B N))) =
    Part3.primeProductSignedError 1 (2*N) N Q rho (fullSmoothWeight kappa B N) +
      lowerReserve kappa B N Q rho at hp
  linarith

-- Both reserves are paid, without an estimate for the smooth PP term.
-- The threshold precedes the entire causal policy and all source labels.
theorem eventually_original_source_smoothing_paid (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool)
      (cap M : ℕ) (w z L : ℝ) (Q : Finset ℕ),
      Even N → M ≤ N → Q ⊆ Finset.Icc 1 M →
      |Part3.primeProductSignedError 1 N N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
        Part3.primeProductSignedError 1 (2*N) N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (fullSmoothWeight kappa (A+3) N)| ≤
        41*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_actual_lowerTrim_logAccuracy kappa hkappa hkappa1 A 1 (by norm_num),
    eventually_actual_causal_singleton_endpoint_log_saving A,
    eventually_ge_atTop (3 : ℕ)] with N hlow hupper hN
  intro retainEven cap M w z L Q hEven hMN hQ
  have hN2 : 2 ≤ N := by omega
  let B := A+3
  let D := upperWidth B N
  let S := endpointCarrier (2*N) N D
  let sm := smoothNatural kappa B N
  have hrange : ∀ p ∈ chenPrimePrefix (2*N), 0 ≤ sm p ∧ sm p ≤ 1 :=
    fun p hp => smooth_range kappa B N p
  have hm : ∀ p ∈ chenPrimePrefix (2*N), originalLowerCut kappa N < p →
      p+D ≤ N → sm p = 1 := by
    intro p hp ht hsmall
    exact original_middle hN2 kappa B p ht (by omega)
  have ht : ∀ p ∈ chenPrimePrefix (2*N), N+D < p → sm p = 0 := by
    intro p hp hbig
    exact original_upper_tail hN2 kappa B p hbig
  have hUP := hupper retainEven cap (2*N) D M w z L S Q
    (sharp N) (patched N (originalLowerCut kappa N) sm) hEven
    (Finset.filter_subset _ _) hQ hMN (upperWidth_le_original_endpoint B hN2)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (sharp_eq_patched_off_endpoint (2*N) N D (originalLowerCut kappa N) sm hm ht)
    (fun p hp => abs_sharp_sub_patched_le_one N (originalLowerCut kappa N) p sm
      (hrange p (Finset.mem_filter.mp hp).1))
  have hLO := hlow retainEven cap (2*N) M w z L Q sm (by omega) hMN hQ hrange
  have hid := original_source_exact_reserves kappa B N Q
    (actualLowerSmallRoughRho retainEven N cap w z L)
  have hdiff : Part3.primeProductSignedError 1 N N Q
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
      Part3.primeProductSignedError 1 (2*N) N Q
        (actualLowerSmallRoughRho retainEven N cap w z L) (fullSmoothWeight kappa B N) =
      lowerReserve kappa B N Q (actualLowerSmallRoughRho retainEven N cap w z L) +
        upperReserve kappa B N Q (actualLowerSmallRoughRho retainEven N cap w z L) := by
    linarith
  rw [hdiff]
  exact (abs_add _ _).trans ((add_le_add hLO hUP).trans_eq (by ring))

-- Actual receiver specialization for the COMPUTED canonical tent plan.
-- The true support gate is visible; no full adopted level is assumed.
theorem eventually_canonical_tent_receiver_smoothing_paid (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
      (cap M : ℕ) (w z L : ℝ),
      Even N → 1 < L → w ≤ L → w ≤ z → z ≤ (cap : ℝ) → M ≤ N →
      (∀ q ∈ activeModuli R mesh buffer seed N cap w z L, q ≤ M) →
      ((chenAdditivePrimeCarrier N).card : ℝ) *
          physicalDensitySum
            (actualLowerSmallRoughModuli (keep R mesh buffer seed N) N cap w z)
            (lowerRho R mesh buffer seed N cap w z L) +
        Part3.primeProductSignedError 1 (2*N) N
          (activeModuli R mesh buffer seed N cap w z L)
          (lowerRho R mesh buffer seed N cap w z L) (fullSmoothWeight kappa (A+3) N) -
        chenInitialCorrectionCost N (activeModuli R mesh buffer seed N cap w z L) -
        41*(N : ℝ)/Real.log (N : ℝ)^A ≤ ((chenSiftedPrimeSource N z).card : ℝ) := by
  filter_upwards [eventually_original_source_smoothing_paid kappa hkappa hkappa1 A] with N hN
  intro R mesh buffer seed cap M w z L hEven hL hwL hwz hzcap hMN hcap
  have hQ : activeModuli R mesh buffer seed N cap w z L ⊆ Finset.Icc 1 M := by
    intro q hq
    have hd := P5S1SingletonPP.active_physical_data
      (keep R mesh buffer seed N) N cap w z L hq
    exact Finset.mem_Icc.mpr ⟨hd.1, hcap q hq⟩
  have hpaid := hN (keep R mesh buffer seed N) cap M w z L
    (activeModuli R mesh buffer seed N cap w z L) hEven hMN hQ
  have horiginal := P5CanonicalTentIndependentSingletonCaller.canonical_causal_original_receiver
    R mesh buffer seed N cap w z L hEven hL hwL hwz hzcap
  have hdiff := (abs_le.mp hpaid).1
  dsimp only [lowerRho] at horiginal ⊢
  linarith

end
end ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
