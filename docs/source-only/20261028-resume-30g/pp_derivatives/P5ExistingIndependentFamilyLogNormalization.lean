import ImbalancedChen.P5ActualIndependentGroupLogNormalization
import ImbalancedChen.P5LicensedOriginalIntegerProfile
import ImbalancedChen.P5ActualSingletonPrimeTestFamily
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Normalize an EXISTING independent test by the exact group reciprocal logs.
The original test and integer normalization are independently specified;
no PP/centering/analytic conclusion is a premise. This operator preserves
actual endpoint/product fields and does not enumerate absent callers.
-/
namespace ImbalancedChen.P5Z.ExistingIndependentFamilyLogNormalization
noncomputable section
open Classical Set
open scoped BigOperators
open ActualIndependentGroupLogNormalization ActualEtaPsiOccurrenceBudget
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open NativeSelectedFourOrderedEuler AdmissibleAllRankIntegerGeometricFamily
open GroupedOccurrenceLogShift LicensedOriginalIntegerProfile

/-- One natural constant BEFORE genuine rank, arbitrary HB occurrence
count, original owner map, all targets/points and every repeated word. -/
theorem normalize_occurrence_bound (rMax q : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ r ≤ rMax, ∀ m (owner : Fin m → Fin r) (U : Fin m → ℝ)
      (f : (Fin r → ℝ) → ℝ), ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ (v : List (Fin r)) p, v.length ≤ q → |eulerWord v f p| ≤ M) →
      ∀ (w : List (Fin m)) z, w.length ≤ q →
      |occWord w (fun y => normalize f (fun i => groupProduct owner U i y)) z| ≤ (K : ℝ)*M := by
  obtain ⟨C, hC, hb⟩ := groupLogProduct_mixedEuler rMax q
  let H : ℝ := (4 : ℝ)^q*C
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨Nat.ceil H + 1, by omega, ?_⟩
  intro r hr m owner U f hf M hM bf w z hw
  let F : (Fin m → ℝ) → ℝ := fun y => f (fun i => groupProduct owner U i y)
  let G : (Fin m → ℝ) → ℝ := fun y => groupLogProduct (fun i => groupProduct owner U i y)
  have hmap : ContDiff ℝ ∞ (fun y => fun i => groupProduct owner U i y) :=
    contDiff_pi.mpr (fun i => groupProduct_smooth owner U i)
  have hF : ContDiff ℝ ∞ F := hf.comp hmap
  have hG : ContDiff ℝ ∞ G := (groupLogProduct_smooth r).comp hmap
  have bF (v : List (Fin m)) (hv : v.length ≤ w.length) : |occWord v F z| ≤ M := by
    rw [show F = (fun y => f (fun i => groupProduct owner U i y)) from rfl,
      occWord_ambient owner U f hf]
    exact bf (v.map owner) _ (by simpa using hv.trans hw)
  have bG (v : List (Fin m)) (hv : v.length ≤ w.length) : |occWord v G z| ≤ C := by
    rw [show G = (fun y => groupLogProduct (fun i => groupProduct owner U i y)) from rfl,
      occWord_ambient owner U groupLogProduct (groupLogProduct_smooth r)]
    exact hb r hr (v.map owner) _ (by simpa using hv.trans hw)
  have hraw := occWord_four_bound F G (fun _ => 1) (fun _ => 1)
    hF hG contDiff_const contDiff_const w z M C 1 1 hM (zero_le_one.trans hC)
    zero_le_one zero_le_one bF bG
    (fun v hv => ActualSingletonPrimeTestFamily.occurrence_one_bound v z)
    (fun v hv => ActualSingletonPrimeTestFamily.occurrence_one_bound v z)
  have heq : (fun y => F y*G y*(1 : ℝ)*1) =
      (fun y => normalize f (fun i => groupProduct owner U i y)) := by
    funext y
    simp [normalize, F, G]
  rw [heq] at hraw
  simp only [mul_one] at hraw
  have hceil : H ≤ ((Nat.ceil H + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil H
    push_cast
    linarith
  calc
    _ ≤ (4 : ℝ)^w.length*(M*C) := hraw
    _ ≤ (4 : ℝ)^q*(M*C) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hw) (mul_nonneg hM (zero_le_one.trans hC))
    _ = H*M := by dsimp [H]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hceil hM

theorem normalize_euler_bound (rMax q : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ r ≤ rMax, ∀ (f : (Fin r → ℝ) → ℝ), ContDiff ℝ ∞ f →
      ∀ M : ℝ, 0 ≤ M → (∀ (v : List (Fin r)) p,
        v.length ≤ q → |eulerWord v f p| ≤ M) →
      ∀ (w : List (Fin r)) p, w.length ≤ q → |eulerWord w (normalize f) p| ≤ (K : ℝ)*M := by
  obtain ⟨K, hK, hb⟩ := normalize_occurrence_bound rMax q
  refine ⟨K, hK, ?_⟩
  intro r hr f hf M hM bf w p hw
  have h := hb r hr r id p f hf M hM bf w 0 hw
  have hraw : |occWord w (fun y => normalize f (multiplicativeChart p y)) 0| ≤ (K : ℝ)*M := by
    simpa only [groupProduct_identity] using h
  rw [← orderedEuler_occurrence_dictionary (normalize f) (normalize_smooth f hf) w p 0] at hraw
  simpa only [multiplicativeChart_zero] using hraw

def normalizedPrimeWeight {r : ℕ} (Wprime : (Fin r → ℕ) → ℝ) (u : Fin r → ℕ) : ℝ :=
  Wprime u / ∏ i, Real.log (u i : ℝ)

def normalizedLicence {r : ℕ} {Wprime : (Fin r → ℕ) → ℝ} (L : Licence r Wprime) :
    Licence r (normalizedPrimeWeight Wprime) where
  ambient := normalize L.ambient
  smooth := normalize_smooth L.ambient L.smooth
  agrees_on_primes := by
    intro u hu
    rw [normalize_nat, L.agrees_on_primes u hu]
    rfl

/-- This retains the SAME original family data and indices; it neither
asserts caller exhaustion nor inserts profiles at absent original ranks. -/
def normalizeExistingFamily {rMax : ℕ} (A : Family rMax) : Family rMax where
  aStar := A.aStar
  aStar_pos := A.aStar_pos
  lower := A.lower
  lower_pos := A.lower_pos
  upper := A.upper
  upper_pos := A.upper_pos
  ambient := fun N r => normalize (A.ambient N r)
  smooth := fun N r => normalize_smooth _ (A.smooth N r)
  support := by
    intro N r u hu
    exact A.support N r u (normalize_nonzero hu)
  finitePrimeSupport := by
    intro N r
    apply (A.finitePrimeSupport N r).subset
    intro u hu
    exact ⟨hu.1, normalize_nonzero hu.2⟩
  mixedEuler := by
    intro q
    obtain ⟨K, hK, hb⟩ := normalize_euler_bound rMax q
    obtain ⟨C, B, hC, bf⟩ := A.mixedEuler q
    refine ⟨K*C, B, Nat.mul_pos hK hC, ?_⟩
    intro N r w p hw
    have hlog : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by positivity)
    have h := hb r.val (Nat.le_of_lt_succ r.isLt) (A.ambient N r) (A.smooth N r)
      ((C : ℝ)*Real.log ((N : ℝ)+2)^B) (by positivity) (fun v u hv => bf N r v u hv) w p hw
    simpa only [Nat.cast_mul, mul_assoc] using h

/-- The normalized integer profile is derived from the original test,
including the HB composite products, rather than defined to equal an atlas. -/
theorem normalized_existing_integer {rMax : ℕ} (A : Family rMax) (N : ℕ)
    (r : Fin (rMax+1)) (u : Fin r.val → ℕ) :
    (normalizeExistingFamily A).ambient N r (fun i => (u i : ℝ)) =
      A.ambient N r (fun i => (u i : ℝ)) / ∏ i, Real.log (u i : ℝ) :=
  normalize_nat (A.ambient N r) u

end
end ImbalancedChen.P5Z.ExistingIndependentFamilyLogNormalization
