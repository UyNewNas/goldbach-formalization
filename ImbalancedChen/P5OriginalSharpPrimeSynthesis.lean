import ImbalancedChen.P5OriginalPrimeEndpointLogPayment
import ImbalancedChen.P5PrimeDivisorMeanCorrection
import ImbalancedChen.BoundaryArbitraryLog

/-!
# Original sharp-prime endpoint from the permitted analytic primitives

The only analytic inputs in the final conditional theorem are the signed
smooth-singleton PP estimate and the signed actual lower-trim estimate.
Endpoint and full modulus-prime corrections are proved suppliers, not
premises. This does not assert either missing analytic input or AP441.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5OriginalSharpPrime

noncomputable section
open scoped BigOperators
open Classical Filter Topology
open P5OriginalPrimeEndpoint P5PrimeDivisorMean

def sharp (N p : ℕ) : ℝ := if p ≤ N then 1 else 0

def patched (N Y : ℕ) (smooth : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p ≤ Y then sharp N p else smooth p

def lowerTrim (N Y : ℕ) (smooth : ℕ → ℝ) (p : ℕ) : ℝ :=
  patched N Y smooth p - smooth p

/-- The literal permitted lower wall from the original manuscript. -/
def originalLowerCut (kappa : ℝ) (N : ℕ) : ℕ := Nat.ceil (2*(N : ℝ)^(1-kappa))

def endpointCarrier (P N D : ℕ) : Finset ℕ :=
  (chenPrimePrefix P).filter (fun p => distance N p ≤ D)

def totalPiError (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ S, rho q*(chenPrimeAPCount N N q -
    ((chenPrimePrefix N).card : ℝ)/(Nat.totient q : ℝ))

theorem sharp_range (N p : ℕ) : 0 ≤ sharp N p ∧ sharp N p ≤ 1 := by
  unfold sharp
  split_ifs <;> norm_num

theorem patched_range (N Y p : ℕ) (smooth : ℕ → ℝ)
    (hsmooth : 0 ≤ smooth p ∧ smooth p ≤ 1) :
    0 ≤ patched N Y smooth p ∧ patched N Y smooth p ≤ 1 := by
  unfold patched
  split_ifs
  · exact sharp_range N p
  · exact hsmooth

theorem lowerTrim_eq_zero_of_lt (N Y p : ℕ) (smooth : ℕ → ℝ) (hp : Y < p) :
    lowerTrim N Y smooth p = 0 := by simp [lowerTrim,patched,Nat.not_le.mpr hp]

theorem lowerTrim_range_of_le (N Y p : ℕ) (smooth : ℕ → ℝ)
    (hYN : Y ≤ N) (hsmooth : 0 ≤ smooth p ∧ smooth p ≤ 1) :
    0 ≤ lowerTrim N Y smooth p ∧ lowerTrim N Y smooth p ≤ 1 := by
  by_cases hp : p ≤ Y
  · have hpN : p ≤ N := hp.trans hYN
    simp only [lowerTrim,patched,if_pos hp,sharp,if_pos hpN]
    constructor <;> linarith [hsmooth.1,hsmooth.2]
  · simp [lowerTrim,patched,hp]

/-- The literal ceiling lower wall is eventually genuinely below N;
its harmless ceiling does not need an additional target assumption. -/
theorem eventually_originalLowerCut_le (kappa : ℝ) (hkappa : 0 < kappa) :
    ∀ᶠ N : ℕ in atTop, originalLowerCut kappa N ≤ N := by
  filter_upwards [eventually_powerLog_le_logAccuracy 2 (1-kappa) 0 0
    (by linarith) 1 (by norm_num)] with N hpaid
  apply Nat.ceil_le.mpr
  simpa only [pow_zero,mul_one,one_mul,div_one] using hpaid

theorem abs_sharp_sub_patched_le_one (N Y p : ℕ) (smooth : ℕ → ℝ)
    (hsmooth : 0 ≤ smooth p ∧ smooth p ≤ 1) :
    |sharp N p-patched N Y smooth p| ≤ 1 := by
  have hs := sharp_range N p
  have hp := patched_range N Y p smooth hsmooth
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Actual middle=1 and upper-tail=0 imply endpoint support. The low
region is patched to the sharp test and retained in lowerTrim separately. -/
theorem sharp_eq_patched_off_endpoint (P N D Y : ℕ) (smooth : ℕ → ℝ)
    (hmiddle : ∀ p ∈ chenPrimePrefix P, Y < p → p+D ≤ N → smooth p = 1)
    (htail : ∀ p ∈ chenPrimePrefix P, N+D < p → smooth p = 0) :
    ∀ p ∈ chenPrimePrefix P, p ∉ endpointCarrier P N D →
      sharp N p = patched N Y smooth p := by
  intro p hp hout
  have hdist : ¬distance N p ≤ D := by
    intro h
    exact hout (Finset.mem_filter.mpr ⟨hp,h⟩)
  by_cases hpY : p ≤ Y
  · simp [patched,hpY]
  · by_cases hpN : p ≤ N
    · have hsmall : p+D ≤ N := by
        simp only [distance,if_pos hpN] at hdist
        omega
      simp [patched,hpY,sharp,hpN,hmiddle p hp (by omega) hsmall]
    · have hlarge : N+D < p := by
        simp only [distance,if_neg hpN] at hdist
        omega
      simp [patched,hpY,sharp,hpN,htail p hp hlarge]

/-- Finite inclusive prefix transfer for the original sharp prime count. -/
theorem singleton_sharp_eq_original (P N : ℕ) (hNP : N ≤ P)
    (S : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P (sharp N)) =
      Part3.primeProductSignedError 1 N N S rho (P5S1SingletonPP.singletonWeight N (fun _ => 1)) := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq,
    P5S1SingletonPP.primeProductSignedError_singleton_eq]
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun x : ℝ => rho q*x)
  exact P5S1SingletonPP.prefix_truncation_discrepancy_eq P N N q hNP

/-- The lower trim is exactly the difference of these two tests, keeping
its own signed same-rho PP error rather than assuming a sharp estimate. -/
theorem patched_PP_eq_smooth_add_lowerTrim (P N Y : ℕ) (S : Finset ℕ)
    (rho smooth : ℕ → ℝ) :
    Part3.primeProductSignedError 1 P N S rho
        (P5S1SingletonPP.singletonWeight P (patched N Y smooth)) =
      Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P smooth) +
        Part3.primeProductSignedError 1 P N S rho
          (P5S1SingletonPP.singletonWeight P (lowerTrim N Y smooth)) := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq,
    P5S1SingletonPP.primeProductSignedError_singleton_eq,
    P5S1SingletonPP.primeProductSignedError_singleton_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add,← finitePrimitiveDiscrepancy_add]
  apply congrArg (fun x : ℝ => rho q*x)
  apply finitePrimitiveDiscrepancy_congr
  intro p hp
  unfold lowerTrim
  ring

/-- Exact three-part decomposition plus the proved full prime-divisor
correction. No endpoint or correction bound is an assumption. -/
theorem abs_totalPiError_le_three_parts (P N Y : ℕ) (hNP : N ≤ P)
    (S : Finset ℕ) (rho smooth : ℕ → ℝ) :
    |totalPiError N S rho| ≤
      |Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P (sharp N)) -
        Part3.primeProductSignedError 1 P N S rho
          (P5S1SingletonPP.singletonWeight P (patched N Y smooth))| +
      |Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P smooth)| +
      |Part3.primeProductSignedError 1 P N S rho
        (P5S1SingletonPP.singletonWeight P (lowerTrim N Y smooth))| +
      |correction N S rho (fun _ => 1)| := by
  have hdict : Part3.primeProductSignedError 1 N N S rho
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) =
      totalPiError N S rho + correction N S rho (fun _ => 1) := by
    simpa only [totalPiError,finiteCongruenceMass,chenPrimeAPCount,finiteSourceMass,
      Finset.sum_const,nsmul_eq_mul,mul_one] using
      singleton_PP_eq_total_prime_mean_add_correction N S rho (fun _ => 1)
  have hpatch := patched_PP_eq_smooth_add_lowerTrim P N Y S rho smooth
  have hsharp := singleton_sharp_eq_original P N hNP S rho
  have heq : totalPiError N S rho =
      ((Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P (sharp N)) -
        Part3.primeProductSignedError 1 P N S rho
          (P5S1SingletonPP.singletonWeight P (patched N Y smooth))) +
      Part3.primeProductSignedError 1 P N S rho (P5S1SingletonPP.singletonWeight P smooth) +
      Part3.primeProductSignedError 1 P N S rho
        (P5S1SingletonPP.singletonWeight P (lowerTrim N Y smooth))) -
      correction N S rho (fun _ => 1) := by linarith
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add_right
    ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)

/-- The full modulus-prime logarithmic square has arbitrary logarithmic
accuracy. Reuses the existing sublinear power-log theorem. -/
theorem eventually_log_square_cap_le_logAccuracy (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ N →
      4*(1+Real.log (max 1 (Q : ℝ)))^2 ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_powerLog_le_logAccuracy 16 0 2 A (by norm_num) 1 (by norm_num),
    eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)] with N hpaid hlog hN
  intro Q hQN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hNr (by exact_mod_cast hQN))
  have hL0 : 0 ≤ 1+Real.log (max 1 (Q : ℝ)) := by
    have hh := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith
  have hL : 1+Real.log (max 1 (Q : ℝ)) ≤ 2*Real.log (N : ℝ) := by linarith
  have hs := (sq_le_sq₀ hL0 (by positivity : 0 ≤ 2*Real.log (N : ℝ))).mpr hL
  have hbound : 4*(1+Real.log (max 1 (Q : ℝ)))^2 ≤ 16*Real.log (N : ℝ)^2 := by nlinarith
  exact hbound.trans (by simpa only [Real.rpow_zero,mul_one,one_mul] using hpaid)

/-- Conditional original sharp-prime lemma. Its two analytic premises are
at the actual smooth singleton and the explicit original lowerTrim test.
The endpoint, squarefree/coprime correction and all their logarithmic
payments are derived here. The analytic premises themselves remain OPEN. -/
theorem original_sharp_prime_logAccuracy_of_smooth_and_actual_lowerTrim
    (A j : ℕ) (theta kappa Cs Ct : ℝ)
    (htheta : theta < 1) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (hCs : 0 ≤ Cs) (hCt : 0 ≤ Ct)
    (retainEven : ℕ → List ℕ → Bool) (cap P Q D : ℕ → ℕ)
    (w z L : ℕ → ℝ) (smooth : ℕ → ℕ → ℝ)
    (hScope : ∀ᶠ N : ℕ in atTop, Even N →
      (Q N : ℝ) ≤ (N : ℝ)^theta ∧
      ∀ q ∈ P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N), q ≤ Q N)
    (hGeometry : ∀ᶠ N : ℕ in atTop, Even N →
      N ≤ P N ∧
      (∀ p ∈ chenPrimePrefix (P N), 0 ≤ smooth N p ∧ smooth N p ≤ 1) ∧
      (∀ p ∈ chenPrimePrefix (P N), originalLowerCut kappa N < p →
        p+D N ≤ N → smooth N p = 1) ∧
      (∀ p ∈ chenPrimePrefix (P N), N+D N < p → smooth N p = 0))
    (hWidth : ∀ᶠ N : ℕ in atTop,
      D N ≤ Nat.ceil ((N : ℝ)/Real.log (N : ℝ)^(A+3)))
    (hSmoothSignedPP : ∀ᶠ N : ℕ in atTop, Even N →
      |Part3.primeProductSignedError 1 (P N) N
        (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
        (actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N))
        (P5S1SingletonPP.singletonWeight (P N) (smooth N))| ≤
          Cs*(N : ℝ)/Real.log (N : ℝ)^A)
    (hActualLowerTrimSignedPP : ∀ᶠ N : ℕ in atTop, Even N →
      |Part3.primeProductSignedError 1 (P N) N
        (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
        (actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N))
        (P5S1SingletonPP.singletonWeight (P N)
          (lowerTrim N (originalLowerCut kappa N) (smooth N)))| ≤
          Ct*(N : ℝ)^(1-kappa)*Real.log (N : ℝ)^j) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |∑ q ∈ P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N),
        actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N) q *
          (chenPrimeAPCount N N q - ((chenPrimePrefix N).card : ℝ)/(Nat.totient q : ℝ))| ≤
        (Cs+42)*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [hScope,hGeometry,hWidth,hSmoothSignedPP,hActualLowerTrimSignedPP,
    eventually_actual_causal_singleton_endpoint_log_saving A,
    eventually_log_square_cap_le_logAccuracy A,
    eventually_powerLog_le_logAccuracy Ct (1-kappa) j A (by linarith) 1 (by norm_num),
    eventually_ge_atTop (3 : ℕ)] with N hscope hgeometry hwidth hsmooth htrim hendpoint hcorr htrimPaid hN
  intro hEven
  obtain ⟨hNP,hrange,hmiddle,htail⟩ := hgeometry hEven
  obtain ⟨hlevel,hactive⟩ := hscope hEven
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hQN : Q N ≤ N := by
    have hh : (Q N : ℝ) ≤ (N : ℝ) := hlevel.trans
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNr htheta.le)
    exact_mod_cast hh
  have hAQ : P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N) ⊆
      Finset.Icc 1 (Q N) := by
    intro q hq
    exact Finset.mem_Icc.mpr
      ⟨(P5S1SingletonPP.active_physical_data (retainEven N) N (cap N) (w N) (z N) (L N) hq).1,
        hactive q hq⟩
  have hEP := hendpoint (retainEven N) (cap N) (P N) (D N) (Q N) (w N) (z N) (L N)
    (endpointCarrier (P N) N (D N))
    (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
    (sharp N) (patched N (originalLowerCut kappa N) (smooth N)) hEven
    (Finset.filter_subset _ _) hAQ hQN hwidth
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (sharp_eq_patched_off_endpoint (P N) N (D N) (originalLowerCut kappa N) (smooth N) hmiddle htail)
    (fun p hp => abs_sharp_sub_patched_le_one N (originalLowerCut kappa N) p (smooth N)
      (hrange p (Finset.mem_filter.mp hp).1))
  have hC := abs_correction_le_log_square N (Q N)
    (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
    (actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N)) (fun _ => 1) hAQ
    (fun q hq => (P5S1SingletonPP.active_physical_data (retainEven N) N (cap N)
      (w N) (z N) (L N) hq).2.1)
    (fun q _ => actualLowerSmallRoughRho_abs_le_one (retainEven N) N (cap N) (w N) (z N) (L N) q)
    (fun _ _ => by norm_num)
  have hCPaid := hC.trans (hcorr (Q N) hQN)
  have hTPaid := (htrim hEven).trans htrimPaid
  have hfinite := abs_totalPiError_le_three_parts (P N) N (originalLowerCut kappa N) hNP
    (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
    (actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N)) (smooth N)
  change |totalPiError N
    (P5S1OriginalLower.active (retainEven N) N (cap N) (w N) (z N) (L N))
    (actualLowerSmallRoughRho (retainEven N) N (cap N) (w N) (z N) (L N))| ≤ _
  calc
    _ ≤ _ := hfinite
    _ ≤ 40*(N : ℝ)/Real.log (N : ℝ)^A + Cs*(N : ℝ)/Real.log (N : ℝ)^A +
        (N : ℝ)/Real.log (N : ℝ)^A + (N : ℝ)/Real.log (N : ℝ)^A :=
      add_le_add (add_le_add (add_le_add hEP (hsmooth hEven))
        (by simpa only [one_mul] using hTPaid)) hCPaid
    _ = _ := by ring

end
end ImbalancedChen.P5OriginalSharpPrime
