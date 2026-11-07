import ImbalancedChen.P5ExistingIndependentFamilyLogNormalization
import ImbalancedChen.P5ActualIndependentUpperPairProfile
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Actual non-singleton independent prime-pair normalization. The numerator
is the production P4B smoothPhysicalPairOuterRamp at the width selected by
its real compact arithmetic mass constructor. This retains its original
attachedUpper rho model; no lower-tent coefficient substitution occurs.
-/
namespace ImbalancedChen.P5Z.ActualIndependentUpperPairLogFields
noncomputable section
open Classical Set
open scoped BigOperators
open ActualIndependentGroupLogNormalization ExistingIndependentFamilyLogNormalization
open AdmissibleAllRankIntegerGeometricFamily AllWordAmbientOccurrenceBound
open GroupedOccurrenceLogShift LicensedOriginalIntegerProfile
open P5ActualIndependentUpperPairProfile

/-- Normalize the actual independently supplied original pair function. -/
def profile (D : Parameters) (b : Band D) (N : ℕ) : (Fin 2 → ℝ) → ℝ :=
  normalize (P5ActualIndependentUpperPairProfile.profile D b N)

def integerWeight (D : Parameters) (b : Band D) (N : ℕ) (u : Fin 2 → ℕ) : ℝ :=
  P5ActualIndependentUpperPairProfile.integerWeight D b N u /
    ∏ i, Real.log (u i : ℝ)

/-- The original labelled caller is independently present in production. -/
def originalNormalizedCaller (D : Parameters) (b : Band D) (N : ℕ)
    (u : Fin 2 → Fin (N+1)) : ℝ :=
  P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
    (selected D).width u / ∏ i, Real.log ((u i).val : ℝ)

theorem profile_smooth (D : Parameters) (b : Band D) (N : ℕ) :
    ContDiff ℝ ∞ (profile D b N) :=
  normalize_smooth _ (P5ActualIndependentUpperPairProfile.profile_smooth D b N)

theorem exact_integer_normalization (D : Parameters) (b : Band D) (N : ℕ)
    (u : Fin 2 → ℕ) : profile D b N (fun i => (u i : ℝ)) = integerWeight D b N u :=
  normalize_nat (P5ActualIndependentUpperPairProfile.profile D b N) u

theorem exact_original_pair_caller (D : Parameters) (b : Band D) {N : ℕ}
    (hN : 2 ≤ N) (u : Fin 2 → Fin (N+1))
    (hu : u ∈ Part3.labelledPrimeTuples 2 N) :
    originalNormalizedCaller D b N u = profile D b N (P4B.primeTuplePoint N u) := by
  rw [show P4B.primeTuplePoint N u = (fun i => ((u i).val : ℝ)) from rfl]
  rw [show profile D b N = normalize (P5ActualIndependentUpperPairProfile.profile D b N) from rfl,
    normalize_nat]
  unfold originalNormalizedCaller
  rw [actual_original_caller D b hN u hu]
  rfl

/-- Original same-width endpoints, inherited from the actual source.
The complete product margin is retained rather than changed to a residual quotient. -/
theorem actual_endpoint_product_fields (D : Parameters) (b : Band D)
    {N : ℕ} {u : Fin 2 → ℝ} (hu : profile D b N u ≠ 0) :
    2 ≤ N ∧ (∀ i, (N : ℝ)^D.theta < u i) ∧
      (N : ℝ)^(1-D.kappaZero) < ∏ i, u i ∧
      (∏ i, u i) < Real.exp (selected D).width * (N : ℝ) := by
  have h := profile_nonzero_data D b (normalize_nonzero hu)
  refine ⟨h.1, h.2.2.1, ?_, ?_⟩
  · simpa only [Fin.prod_univ_two] using h.2.2.2.1
  · simpa only [Fin.prod_univ_two] using h.2.2.2.2

theorem finite_integer_support (D : Parameters) (b : Band D) (N : ℕ) :
    Set.Finite {u : Fin 2 → ℕ | integerWeight D b N u ≠ 0} := by
  apply (P5ActualIndependentUpperPairProfile.finite_integer_support D b N).subset
  intro u hu
  rw [← exact_integer_normalization] at hu
  exact normalize_nonzero hu

def licence (D : Parameters) (b : Band D) (N : ℕ) : Licence 2 (integerWeight D b N) where
  ambient := profile D b N
  smooth := profile_smooth D b N
  agrees_on_primes := by intro u hu; exact exact_integer_normalization D b N u

theorem actual_normalized_mixedEuler (D : Parameters) (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (b : Band D) N (w : List (Fin 2)) u,
      w.length ≤ q → |eulerWord w (profile D b N) u| ≤ (C : ℝ) := by
  obtain ⟨K, hK, hb⟩ := normalize_euler_bound 2 q
  obtain ⟨C0, hC0, hraw⟩ := mixedEuler D q
  refine ⟨K*C0, Nat.mul_pos hK hC0, ?_⟩
  intro b N w u hw
  have h := hb 2 le_rfl (P5ActualIndependentUpperPairProfile.profile D b N)
    (P5ActualIndependentUpperPairProfile.profile_smooth D b N) (C0 : ℝ) (Nat.cast_nonneg _)
    (fun v p hv => hraw b N v p hv) w u hw
  simpa only [Nat.cast_mul] using h

/-- The same actual pair constant precedes all HB role occurrences and
keeps every repeated original-owner letter in its original word order. -/
theorem actual_normalized_occurrence_budget (D : Parameters) (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (b : Band D) N m (owner : Fin m → Fin 2) (U : Fin m → ℝ)
      (w : List (Fin m)) z, w.length ≤ q →
      |occWord w (fun y => profile D b N (fun i => groupProduct owner U i y)) z| ≤ (C : ℝ) := by
  obtain ⟨K, hK, hb⟩ := normalize_occurrence_bound 2 q
  obtain ⟨C0, hC0, hraw⟩ := mixedEuler D q
  refine ⟨K*C0, Nat.mul_pos hK hC0, ?_⟩
  intro b N m owner U w z hw
  have h := hb 2 le_rfl m owner U (P5ActualIndependentUpperPairProfile.profile D b N)
    (P5ActualIndependentUpperPairProfile.profile_smooth D b N) (C0 : ℝ) (Nat.cast_nonneg _)
    (fun v p hv => hraw b N v p hv) w z hw
  simpa only [Nat.cast_mul] using h

structure ActualPairFields (D : Parameters) : Prop where
  exponent_pos : 0 < D.theta
  smooth : ∀ (b : Band D) N, ContDiff ℝ ∞ (profile D b N)
  support : ∀ (b : Band D) N u, profile D b N u ≠ 0 →
    (∀ i, (N : ℝ)^D.theta ≤ u i) ∧ (∏ i, u i) ≤ Real.exp (selected D).width * (N : ℝ)
  finiteIntegerSupport : ∀ (b : Band D) N, Set.Finite {u : Fin 2 → ℕ | integerWeight D b N u ≠ 0}
  mixedEuler : ∀ q, ∃ C B : ℕ, 0 < C ∧ ∀ (b : Band D) N (w : List (Fin 2)) u,
    w.length ≤ q → |eulerWord w (profile D b N) u| ≤
      (C : ℝ)*Real.log ((N : ℝ)+2)^B

theorem actual_pair_fields (D : Parameters) : ActualPairFields D := by
  constructor
  · exact D.theta_pos
  · exact profile_smooth D
  · intro b N u hu
    have h := actual_endpoint_product_fields D b hu
    exact ⟨fun i => (h.2.1 i).le, h.2.2.2.le⟩
  · exact finite_integer_support D
  · intro q
    obtain ⟨C, hC, hb⟩ := actual_normalized_mixedEuler D q
    refine ⟨C, 0, hC, ?_⟩
    intro b N w u hw
    simpa only [pow_zero, mul_one] using hb b N w u hw

end
end ImbalancedChen.P5Z.ActualIndependentUpperPairLogFields
