import ImbalancedChen.P2FiniteMarkedGamma5GeometricFamily
import ImbalancedChen.P2FiniteMarkedGamma5AtlasEulerBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL OR KERNEL CREDIT.

The original geometric Family is multiplied by the fixed causal atlas
readout. Its original rank and scale gates are reused as functions; no
second scale truncation or replacement support argument is defined.
The only new rank conditional transports the old coordinates along the
same rank equality. Outside that rank its multiplier is one.

The accepted atom set may vary with the natural target. The atlas and
width stay fixed, and the preceding all-order atlas budget chooses its
constant before the entire accept function. This supplies a geometric
Family instance, not a smooth realization of an arbitrary discrete B,
an ordinary-mass estimate, or a PP licence.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5AtlasFamily

noncomputable section
open Finset Real
open Part5OriginalCausalSmoothAtlas (Plan Code)
open Part5OriginalH430JointQueryEnclosure (readout)
open P2FiniteMarkedGamma5AtlasEulerBudget
open P2FiniteMarkedGamma5AllRankEulerBudget
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family eulerWord)
open scoped Classical BigOperators ContDiff

/-- Multiply the existing gated ambient. The new conditional only casts
coordinates at the active rank; the existing ambient owns every zero gate. -/
def atlasAmbient (P : Plan) (k r : ℕ) (a width : ℝ) (logQ : ℕ → ℝ)
    (accept : ℕ → (Fin k → Code P) → Prop) (T d : ℕ)
    (v : Fin d → ℝ) : ℝ :=
  P2FiniteMarkedGamma5GeometricFamily.ambient a width logQ k r T d v *
    if hd : d = k + (2 + r) then
      readout P (accept T)
        (safeOldLogCoordinates (k := k) (r := r) (T : ℝ) ((T : ℝ) ^ a)
          (fun i => v (Fin.cast hd.symm i)))
    else 1

theorem atlasAmbient_at_rank (P : Plan) (k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T : ℕ) (hT : scaleThreshold a ≤ (T : ℝ)) :
    atlasAmbient P k r a width logQ accept T (k + (2 + r)) =
      atlasProfile (r := r) P (accept T) (logQ T) (T : ℝ) width ((T : ℝ) ^ a) := by
  funext v
  simp only [atlasAmbient,
    P2FiniteMarkedGamma5GeometricFamily.ambient_at_rank a width logQ k r T hT,
    dif_pos True.intro, Fin.cast_eq_self, atlasProfile]

theorem atlasAmbient_zero_of_rank_ne (P : Plan) (k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T d : ℕ) (hd : d ≠ k + (2 + r)) :
    atlasAmbient P k r a width logQ accept T d = 0 := by
  funext v
  simp only [atlasAmbient,
    P2FiniteMarkedGamma5GeometricFamily.ambient_zero_of_rank_ne a width logQ k r T d hd,
    Pi.zero_apply, zero_mul]

theorem atlasAmbient_zero_below_threshold (P : Plan) (k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T d : ℕ) (hT : (T : ℝ) < scaleThreshold a) :
    atlasAmbient P k r a width logQ accept T d = 0 := by
  funext v
  simp only [atlasAmbient,
    P2FiniteMarkedGamma5GeometricFamily.ambient_zero_below_threshold
      a width logQ k r T d hT,
    Pi.zero_apply, zero_mul]

theorem atlasAmbient_nonzero_original (P : Plan) (k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T d : ℕ) (v : Fin d → ℝ)
    (hne : atlasAmbient P k r a width logQ accept T d v ≠ 0) :
    P2FiniteMarkedGamma5GeometricFamily.ambient a width logQ k r T d v ≠ 0 :=
  (mul_ne_zero_iff.mp hne).1

theorem atlasAmbient_smooth (P : Plan) (k r : ℕ) {a : ℝ} (ha : 0 < a)
    (width : ℝ) (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T d : ℕ) :
    ContDiff ℝ ∞ (atlasAmbient P k r a width logQ accept T d) := by
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [atlasAmbient_at_rank P k r a width logQ accept T hT]
      have hT0 : 0 < (T : ℝ) :=
        zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      exact contDiff_atlasProfile P (accept T) (logQ T) (T : ℝ) width
        (rpow_pos_of_pos hT0 a)
    · rw [atlasAmbient_zero_below_threshold P k r a width logQ accept T _
        (lt_of_not_ge hT)]
      exact contDiff_const
  · rw [atlasAmbient_zero_of_rank_ne P k r a width logQ accept T d hd]
    exact contDiff_const

theorem atlasAmbient_nonneg (P : Plan) (k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (T d : ℕ) (v : Fin d → ℝ) :
    0 ≤ atlasAmbient P k r a width logQ accept T d v := by
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [atlasAmbient_at_rank P k r a width logQ accept T hT]
      exact atlasProfile_nonneg P (accept T) (logQ T) (T : ℝ) width ((T : ℝ) ^ a) v
    · rw [atlasAmbient_zero_below_threshold P k r a width logQ accept T _
        (lt_of_not_ge hT)]
      exact le_rfl
  · rw [atlasAmbient_zero_of_rank_ne P k r a width logQ accept T d hd]
    exact le_rfl

/-- The previous uniform constant precedes the complete accept function.
At every active natural target, the old threshold gives T >= 2. All
other branches are the old zero ambient, including T = 0 and b = 0. -/
theorem atlasAmbient_mixedEuler_budget (P : Plan) (K : ℕ) (width : ℝ)
    (hw : 0 < width) (m : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (a : ℝ), 0 < a →
      ∀ (logQ : ℕ → ℝ) (k r : ℕ), k + 2 + r ≤ K →
      ∀ (accept : ℕ → (Fin k → Code P) → Prop)
        (T d : ℕ) (w : List (Fin d)) (v : Fin d → ℝ), w.length ≤ m →
        |eulerWord w (atlasAmbient P k r a width logQ accept T d) v| ≤ (C : ℝ) := by
  obtain ⟨C, B, hC, hB, H⟩ := atlasProfile_family_mixedEuler_budget P K width hw m
  subst B
  refine ⟨C, hC, ?_⟩
  intro a ha logQ k r hkr accept T d w v hwm
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [atlasAmbient_at_rank P k r a width logQ accept T hT]
      have hT1 : 1 < T := by exact_mod_cast (scaleThreshold_bounds ha hT).1
      have hT2 : 2 ≤ T := by omega
      have hT0 : 0 < (T : ℝ) :=
        zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      simpa only [pow_zero, mul_one] using
        H k r hkr T hT2 (logQ T) ((T : ℝ) ^ a)
          (rpow_pos_of_pos hT0 a) (accept T) w v hwm
    · rw [atlasAmbient_zero_below_threshold P k r a width logQ accept T _
        (lt_of_not_ge hT), eulerWord_zero_eq]
      simpa only [Pi.zero_apply, abs_zero] using (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  · rw [atlasAmbient_zero_of_rank_ne P k r a width logQ accept T d hd, eulerWord_zero_eq]
    simpa only [Pi.zero_apply, abs_zero] using (Nat.cast_nonneg C : (0 : ℝ) ≤ C)

/-- The original Family is updated only by the actual atlas multiplier.
Its floor, product constants and finite prime support are inherited
directly from the existing geometric Family via support inclusion. -/
def atlasFamily (P : Plan) (K k r : ℕ) (a width : ℝ) (logQ : ℕ → ℝ)
    (accept : ℕ → (Fin k → Code P) → Prop)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1)
    (hkr : k + 2 + r ≤ K) : Family K := by
  let A := P2FiniteMarkedGamma5GeometricFamily.geometricFamily
    K k r a width logQ ha hw hw1 hkr
  refine { A with
    ambient := fun T d => atlasAmbient P k r a width logQ accept T d.val
    smooth := fun T d => atlasAmbient_smooth P k r ha width logQ accept T d.val
    support := ?_
    finitePrimeSupport := ?_
    mixedEuler := ?_ }
  · intro T d v hne
    exact A.support T d v
      (atlasAmbient_nonzero_original P k r a width logQ accept T d.val v hne)
  · intro T d
    apply (A.finitePrimeSupport T d).subset
    intro u hu
    exact ⟨hu.1, atlasAmbient_nonzero_original P k r a width logQ accept
      T d.val (fun i => (u i : ℝ)) hu.2⟩
  · intro m
    obtain ⟨C, hC, H⟩ := atlasAmbient_mixedEuler_budget P K width hw m
    refine ⟨C, 0, hC, ?_⟩
    intro T d w v hwm
    simpa only [pow_zero, mul_one] using
      H a ha logQ k r hkr accept T d.val w v hwm

/-- Exact equality on the whole active-rank real space above the original
threshold, with the original individual old, fresh and tail coordinates. -/
theorem atlasFamily_at_rank (P : Plan) (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1) (hkr : k + 2 + r ≤ K)
    (T : ℕ) (hT : scaleThreshold a ≤ (T : ℝ)) :
    (atlasFamily P K k r a width logQ accept ha hw hw1 hkr).ambient T
        ⟨k + (2 + r), by omega⟩ =
      atlasProfile (r := r) P (accept T) (logQ T) (T : ℝ) width ((T : ℝ) ^ a) :=
  atlasAmbient_at_rank P k r a width logQ accept T hT

theorem atlasFamily_zero_below_threshold (P : Plan) (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1) (hkr : k + 2 + r ≤ K)
    (T : ℕ) (d : Fin (K + 1)) (hT : (T : ℝ) < scaleThreshold a) :
    (atlasFamily P K k r a width logQ accept ha hw hw1 hkr).ambient T d = 0 :=
  atlasAmbient_zero_below_threshold P k r a width logQ accept T d.val hT

theorem atlasFamily_zero_of_rank_ne (P : Plan) (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1) (hkr : k + 2 + r ≤ K)
    (T : ℕ) (d : Fin (K + 1)) (hd : d.val ≠ k + (2 + r)) :
    (atlasFamily P K k r a width logQ accept ha hw hw1 hkr).ambient T d = 0 :=
  atlasAmbient_zero_of_rank_ne P k r a width logQ accept T d.val hd

theorem atlasFamily_nonneg (P : Plan) (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (accept : ℕ → (Fin k → Code P) → Prop)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1) (hkr : k + 2 + r ≤ K)
    (T : ℕ) (d : Fin (K + 1)) (v : Fin d.val → ℝ) :
    0 ≤ (atlasFamily P K k r a width logQ accept ha hw hw1 hkr).ambient T d v :=
  atlasAmbient_nonneg P k r a width logQ accept T d.val v

end
end ImbalancedChen.P2FiniteMarkedGamma5AtlasFamily
