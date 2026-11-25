import ImbalancedChen.P5OriginalU5LogCollarBasic
import ImbalancedChen.P5OriginalSingletonLowerTrimPaid

/-! Source-only exact declaration extraction for the actual U5 count consumer.
No elaboration or kernel acceptance is claimed. -/
namespace ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
noncomputable section
open Classical Filter Topology
open P5OriginalSharpPrime P5OriginalPrimeEndpoint
open P5OriginalSingletonLowerTrimPaid
open scoped BigOperators

def smoothNatural (kappa : ℝ) (B N p : ℕ) : ℝ :=
  P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
    (fun _ : Fin 1 => (p : ℝ))

def fullSmoothWeight (kappa : ℝ) (B N : ℕ) : (Fin 1 → Fin (2*N+1)) → ℝ :=
  P5S1SingletonPP.singletonWeight (2*N) (smoothNatural kappa B N)

def actualLicence (kappa : ℝ) (B N : ℕ) :=
  P5Z.ActualSingletonLogCollarFamily.singletonLicence (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N

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

end
end ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer

