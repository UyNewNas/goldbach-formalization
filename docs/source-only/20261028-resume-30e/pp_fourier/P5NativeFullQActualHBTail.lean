import ImbalancedChen.P5ActualHBPostModulusLogCutoff
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.P5HBRightClosedDyadicRoles

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL all-prime, signed native FULL16 coefficient is used literally.
It is not the later NEW jointPresievedSigma. Its complete q support, unit
amplitude, squarefreeness and physical cap are proved upstream from the
actual static row compiler. No rho/mass/support/tail budget is a premise.

The integer occurrence carrier below is the actual finite Cartesian HB
block box, with the complete-product cap retained. Unit occurrences use
U=1/2 and nonunits use (2^j,2^(j+1)], so the actual Fourier atom bounds
hold also at n=1. Real Mobius cutoffs and signed rough roles stay in beta.
The independent geometric Family/caller coverage is a separate obligation.
-/
namespace ImbalancedChen.P5Z.NativeFullQActualHBTail
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open ActualCompleteModulusFourierTail CompleteProductTailDivisorBudgets
open ActualHBPostModulusLogCutoff ActualAllRankOccurrenceFourierBridge
open ActualEuclideanPhysicalFourier AdmissibleAllRankIntegerGeometricFamily
open HBRightClosedDyadicRoles


/-- The existing independently defined native signed coefficient, merely
embedded into C for the same finite count/mean Fourier functional. -/
def nativeRho (precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop) (q : ℕ) : ℂ :=
  (U1011OriginalSixteenJointNearCapModulusConvolution.sigma precision T eta mask q : ℂ)

def nativeQ (precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop) : Finset ℕ :=
  U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport precision T eta mask

def nativeCap (T : ℕ) : ℕ := ⌊(T : ℝ) ^ (153 / 256 : ℝ)⌋₊

theorem nativeRho_norm_le_one {precision T : ℕ} {eta : ℚ}
    (hT : 1 < T) (heta : 0 < eta) (mask : ℕ × ℕ → Prop) (q : ℕ) :
    ‖nativeRho precision T eta mask q‖ ≤ 1 := by
  simpa only [nativeRho, Complex.norm_real, Real.norm_eq_abs] using
    U1011OriginalSixteenJointNearCapModulusConvolution.sigma_abs_le_one hT heta mask q

/-- All gates come from the original physical full-q source. The floor
is below the actual exponent; there is no enlarged auxiliary envelope. -/
theorem native_support_profile {precision T : ℕ} {eta : ℚ}
    (hT : 1 < T) (heta : 0 < eta) (mask : ℕ × ℕ → Prop) :
    1 ≤ nativeCap T ∧ (nativeCap T : ℝ) ≤ (T : ℝ) ^ (153 / 256 : ℝ) ∧
      (nativeCap T : ℝ) ≤ T ∧
      effectiveModuli (nativeQ precision T eta mask) ⊆ Finset.Icc 1 (nativeCap T) ∧
      (∀ q ∈ effectiveModuli (nativeQ precision T eta mask), Squarefree q) ∧
      (∀ q ∈ effectiveModuli (nativeQ precision T eta mask), q.Coprime T) := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hpow0 : 0 ≤ (T : ℝ) ^ (153 / 256 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg T) _
  have hfloor : (nativeCap T : ℝ) ≤ (T : ℝ) ^ (153 / 256 : ℝ) := Nat.floor_le hpow0
  have hcap : (nativeCap T : ℝ) ≤ T := hfloor.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hTR (by norm_num : (153 / 256 : ℝ) ≤ 1))
  refine ⟨(Nat.le_floor_iff hpow0).mpr (by
    simpa using Real.one_le_rpow hTR (by norm_num : (0 : ℝ) ≤ 153 / 256)),
    hfloor, hcap, ?_, ?_, ?_⟩
  · intro q hq
    have hp := U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport_profile hT heta (Finset.mem_erase.mp hq).2
    exact Finset.mem_Icc.mpr ⟨hp.1, (Nat.le_floor_iff hpow0).mpr hp.2.2.2.le⟩
  · intro q hq
    exact (U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport_profile hT heta (Finset.mem_erase.mp hq).2).2.1
  · intro q hq
    exact (U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport_profile hT heta (Finset.mem_erase.mp hq).2).2.2.1

/-- The true same-rho reciprocal-totient mean is derived, with J=0 and
C_rho=1; a target-sized rhoMass premise never enters the application. -/
theorem native_mean_mass_le {precision T : ℕ} {eta : ℚ}
    (hT : 1 < T) (heta : 0 < eta) (mask : ℕ × ℕ → Prop) :
    rhoMeanMass (nativeQ precision T eta mask) (nativeRho precision T eta mask) ≤
      4 * (1 + Real.log (max 1 (nativeCap T : ℝ))) := by
  obtain ⟨hD, hDT, hDT', hQ, hsq, hcop⟩ := native_support_profile hT heta mask
  simpa only [pow_zero, pow_one, one_mul] using
    actual_rho_mean_budget (nativeQ precision T eta mask) (nativeRho precision T eta mask)
      (nativeCap T) 0 hQ hsq 1 (by norm_num)
      (fun q hq => by simpa using nativeRho_norm_le_one hT heta mask q)

theorem native_exact_product_mass_le {precision T : ℕ} {eta : ℚ}
    (hT : 1 < T) (heta : 0 < eta) (mask : ℕ × ℕ → Prop) :
    rhoMass (nativeQ precision T eta mask) (nativeRho precision T eta mask) ≤ nativeCap T := by
  obtain ⟨hD, hDT, hDT', hQ, hsq, hcop⟩ := native_support_profile hT heta mask
  simpa using
    actual_rho_total_budget (nativeQ precision T eta mask) (nativeRho precision T eta mask)
      (nativeCap T) 0 hD hQ 1 (by norm_num)
      (fun q hq => by simpa using nativeRho_norm_le_one hT heta mask q)

def blockU : Block → ℝ
  | .unit => 1 / 2
  | .dyadic j => (2 : ℝ) ^ j

theorem blockU_pos (b : Block) : 0 < blockU b := by
  cases b <;> simp only [blockU] <;> positivity

theorem owns_fourier_bounds {b : Block} {n : ℕ} (hn : Owns b n) :
    blockU b < (n : ℝ) ∧ (n : ℝ) ≤ 2 * blockU b := by
  cases b with
  | unit =>
    change n = 1 at hn
    subst n
    norm_num [blockU]
  | dyadic j =>
    change 2 ^ j < n ∧ n ≤ 2 ^ (j + 1) at hn
    refine ⟨by exact_mod_cast hn.1, ?_⟩
    simpa only [blockU, pow_succ, mul_comm] using (show (n : ℝ) ≤ 2 ^ (j + 1) by exact_mod_cast hn.2)

def actualTuples {m : ℕ} (cap : ℕ) (blocks : Fin m → Block) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset (fun a => (Finset.Icc 1 cap).filter (Owns (blocks a)))).filter
    (fun n => completeProduct n ≤ cap)

theorem actualTuples_spec {m cap : ℕ} {blocks : Fin m → Block} {n : Fin m → ℕ}
    (hn : n ∈ actualTuples cap blocks) :
    (∀ a, 0 < n a ∧ n a ≤ cap ∧ Owns (blocks a) (n a)) ∧ completeProduct n ≤ cap := by
  obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
  refine ⟨?_, hp⟩
  intro a
  obtain ⟨ha, ho⟩ := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn a)
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ha
  exact ⟨hlo, hhi, ho⟩

def actualNativeTail {kStar m : ℕ} (A : Family kStar) (precision T : ℕ)
    (eta : ℚ) (mask : ℕ × ℕ → Prop) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (blocks : Fin m → Block) (R : Fin k.val → ℝ)
    (κ₀ Z : ℝ) (y : Fin m → ℝ) (roles : Fin m → ActualRoughHeathBrownWords.Role)
    (cap : ℕ) (H : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (actualTuples cap blocks)
    (nativeQ precision T eta mask) (nativeRho precision T eta mask) completeProduct T
    (fun n => hbSlots Z y roles n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
  MellinInsertion20261028.exactDiscrepancy (actualTuples cap blocks)
    (nativeQ precision T eta mask) (nativeRho precision T eta mask) completeProduct T
    (fun n => hbSlots Z y roles n *
      truncatedPhysical m (actualEuclideanChart A T k owner (fun a => blockU (blocks a)) R κ₀)
        H (WithLp.toLp 2 (logOccurrence (fun a => blockU (blocks a)) n)))

/-- Actual native FULL16 q coefficient and actual ordered rough HB role
box. Every arithmetic budget (fibre, shifted moment, mean and exact T)
is supplied by proved sources; only the independent admissible geometric
Family and literal occurrence chart data remain as inputs. Constants are
selected before T, precision, mask, cutoff accuracy, rank and role pattern. -/
theorem exists_native_actual_role_tail {kStar : ℕ} (A : Family kStar) :
    ∃ CD CC : ℝ, ∃ E : ℕ, 0 ≤ CD ∧ 0 < CC ∧
      ∀ (precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop)
        (k : Fin (kStar + 1)) (m : ℕ) (owner : Fin m → Fin k.val)
        (blocks : Fin m → Block) (R : Fin k.val → ℝ) (κ₀ Z : ℝ)
        (y : Fin m → ℝ) (roles : Fin m → ActualRoughHeathBrownWords.Role)
        (cap : ℕ) (X : ℝ) (accuracy : ℕ),
        1 < T → 0 < eta → m ≤ 6 * kStar → (∀ i, 0 < R i) →
        1 ≤ X → (T : ℝ) ≤ X → (cap : ℝ) ≤ 6 * X →
        ‖MellinInsertion20261028.exactDiscrepancy (actualTuples cap blocks)
          (nativeQ precision T eta mask) (nativeRho precision T eta mask) completeProduct T
          (fun n => hbSlots Z y roles n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
         MellinInsertion20261028.exactDiscrepancy (actualTuples cap blocks)
          (nativeQ precision T eta mask) (nativeRho precision T eta mask) completeProduct T
          (fun n => hbSlots Z y roles n *
            truncatedPhysical m (actualEuclideanChart A T k owner (fun a => blockU (blocks a)) R κ₀)
              (selectedCutoff X accuracy E (paymentExponent m 0))
              (WithLp.toLp 2 (logOccurrence (fun a => blockU (blocks a)) n)))‖ ≤
          (6 * kStar : ℕ) * CD * (massConstant 0 + CC) * X /
            logScale X ^ (accuracy + 3) := by
  obtain ⟨CD, CC, E, hCD, hCC, htail⟩ :=
    exists_log_saving_actual_role_tail A (153 / 256) (by norm_num)
  refine ⟨CD, CC, E, hCD, hCC, ?_⟩
  intro precision T eta mask k m owner blocks R κ₀ Z y roles cap X accuracy hT heta hm hR hX hTX hcap
  obtain ⟨hD, hDθ, hDT, hQ, hsq, hcop⟩ := native_support_profile hT heta mask
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hDX : (nativeCap T : ℝ) ≤ 6 * X := by linarith
  have hlo (n) (hn : n ∈ actualTuples cap blocks) (a) :=
    (owns_fourier_bounds ((actualTuples_spec hn).1 a).2.2).1
  have hhi (n) (hn : n ∈ actualTuples cap blocks) (a) :=
    (owns_fourier_bounds ((actualTuples_spec hn).1 a).2.2).2
  have hprod (n) (hn : n ∈ actualTuples cap blocks) : (completeProduct n : ℝ) ≤ 6 * X := by
    exact (show (completeProduct n : ℝ) ≤ cap by exact_mod_cast (actualTuples_spec hn).2).trans hcap
  simpa only [mul_one] using htail T k m owner (fun a => blockU (blocks a)) R κ₀
    (actualTuples cap blocks) Z y roles (nativeQ precision T eta mask)
    (nativeRho precision T eta mask) (nativeCap T) 0 1 X accuracy
    (by omega) hm (fun a => blockU_pos _) hR hX hTX hD hDX hDθ (by norm_num)
    hQ hsq (fun q hq => by simpa using nativeRho_norm_le_one hT heta mask q) hlo hhi hprod

end
end ImbalancedChen.P5Z.NativeFullQActualHBTail
