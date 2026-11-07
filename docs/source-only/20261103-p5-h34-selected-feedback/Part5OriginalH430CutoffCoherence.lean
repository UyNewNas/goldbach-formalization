import ImbalancedChen.Part5OriginalH430SameQHistoryCells
import ImbalancedChen.Part5OriginalBuchstabImmutable430Budget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Derive the actual cutoff/ceiling invariant along every production Member
from the original frozen U3/U4 root. This removes the extra clipping in
the local Buchstab integral. It does not identify selected count sources,
pay their bases or construct a simultaneous smooth realization.
-/
namespace ImbalancedChen.Part5OriginalH430CutoffCoherence

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430BuchstabPhysicalBudget

def CutoffFits (p : PhysicalNode) : Prop := residual p ≤ p.argument*p.ceiling

private theorem anchor_pos (j : Fin 10) : 0 < W1Anchor j := by
  have h : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
  dsimp [W1Anchor]
  linarith

private theorem W2_fixed_pos (j : Fin 36) (anchor : Bool) :
    0 < (if anchor then (originalW2At j).s0 else (originalW2At j).phi1) := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have h0 : 0 < a0 (originalW2At j) := (by norm_num : (0:ℝ)<1/5).trans_le hg.1
  have h1 : 0 < (originalW2At j).phi1 := one_div_pos.mp (h0.trans hg.2.1)
  cases anchor
  · exact h1
  · exact W2_anchor_positive hg

private theorem single_fit {L x s : ℝ} (hL : 0 < L) (hr : 0 ≤ L-x)
    (hs : 0 < s) (hx : 1/s < x/L) :
    L-x ≤ (s*(1-x/L))*x := by
  have hx' : L ≤ s*x := by
    have ht := (div_lt_div_iff₀ hs hL).mp hx
    nlinarith only [ht]
  have hp : 0 ≤ (L-x)*(s*x-L)/L :=
    div_nonneg (mul_nonneg hr (sub_nonneg.mpr hx')) hL.le
  have he : (s*(1-x/L))*x-(L-x) = (L-x)*(s*x-L)/L := by
    field_simp [hL.ne'] <;> ring
  linarith only [he, hp]

private theorem pair_fixed_fit {L x y s : ℝ} (hL : 0 < L)
    (hr : 0 ≤ L-y-x) (hs : 0 < s) (hx : 1/s < x/L) :
    L-y-x ≤ (s*(1-x/L-y/L))*x := by
  have hx' : L ≤ s*x := by
    have ht := (div_lt_div_iff₀ hs hL).mp hx
    nlinarith only [ht]
  have hp : 0 ≤ (L-y-x)*(s*x-L)/L :=
    div_nonneg (mul_nonneg hr (sub_nonneg.mpr hx')) hL.le
  have he : (s*(1-x/L-y/L))*x-(L-y-x) = (L-y-x)*(s*x-L)/L := by
    field_simp [hL.ne'] <;> ring
  linarith only [he, hp]

/-- All nine StepShape constructors, not just Buchstab. No target-
ceiling premise is added: fixed/singleton/pair tests are read literally. -/
theorem perform_cutoffFits {p : PhysicalNode} {s : StepShape} {z : Point}
    (hc : 0 < p.ceiling) (hf : CutoffFits p) (hz : LocalDomain p s z) :
    CutoffFits (perform p s z) := by
  have hL := hz.1
  have hr := perform_residual_pos hz
  cases s with
  | retain => exact hf
  | transport i =>
      change residual p ≤ gridArgument i*p.ceiling
      exact hf.trans (mul_le_mul_of_nonneg_right hz.2 hc.le)
  | buchstabUpper =>
      unfold CutoffFits
      change residual (appendOne p (z 0) (buchstabArgument p z)) ≤ _
      rw [residual_appendOne]
      change residual p-z 0 ≤ (residual p/z 0-1)*z 0
      have hx : z 0 ≠ 0 := hz.2.1.1.ne'
      apply le_of_eq
      field_simp [hx] <;> ring
  | buchstabLower =>
      unfold CutoffFits
      change residual (appendOne p (z 0) (buchstabArgument p z)) ≤ _
      rw [residual_appendOne]
      change residual p-z 0 ≤ (residual p/z 0-1)*z 0
      have hx : z 0 ≠ 0 := hz.2.2.1.1.ne'
      apply le_of_eq
      field_simp [hx] <;> ring
  | w1Fixed i j =>
      change residual p ≤ W1Anchor j*p.ceiling
      simpa only [mul_comm] using (div_le_iff₀ (anchor_pos j)).mp hz.2.2
  | w1Singleton i j =>
      unfold CutoffFits
      change residual (appendOne p (z 0) (singletonProfile (W1Anchor j) (normalized p z 0))) ≤ _
      rw [residual_appendOne]
      change residual p-z 0 ≤ (W1Anchor j*(1-z 0/residual p))*z 0
      apply single_fit hL _ (anchor_pos j) hz.2.2.1.1
      simpa only [perform, residual_appendOne] using hr.le
  | w2Fixed j anchor =>
      change residual p ≤ (if anchor then (originalW2At j).s0 else
        (originalW2At j).phi1)*p.ceiling
      simpa only [mul_comm] using (div_le_iff₀ (W2_fixed_pos j anchor)).mp hz.2.2
  | w2Singleton j piece =>
      unfold CutoffFits
      change residual (appendOne p (z 0)
        (singletonProfile (originalW2At j).s0 (normalized p z 0))) ≤ _
      rw [residual_appendOne]
      change residual p-z 0 ≤ ((originalW2At j).s0*(1-z 0/residual p))*z 0
      have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
      apply single_fit hL _ (W2_anchor_positive hg) (W2_singleton_left hz.2.2.1)
      simpa only [perform, residual_appendOne] using hr.le
  | w2Pair j piece =>
      have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
      have hleft := (W2PairDomain_gates hg piece hz.2.2.1).1
      unfold CutoffFits
      change residual (appendPair p (z 0) (z 1)
        (pairProfile (originalW2At j) piece (normalized p z))) ≤ _
      rw [residual_appendPair]
      change residual p-z 1-z 0 ≤ pairProfile (originalW2At j) piece (normalized p z)*z 0
      unfold pairProfile
      split_ifs
      · change residual p-z 1-z 0 ≤
          ((originalW2At j).s0*(1-z 0/residual p-z 1/residual p))*z 0
        apply pair_fixed_fit hL _ (W2_anchor_positive hg) hleft
        simpa only [perform, residual_appendPair] using hr.le
      · change residual p-z 1-z 0 ≤
          ((1-z 0/residual p-z 1/residual p)/(z 0/residual p))*z 0
        have hx : z 0 ≠ 0 := hz.2.1.1.ne'
        apply le_of_eq
        field_simp [hL.ne', hx] <;> ring

theorem realize_cutoffFits {lo hi : ℝ} {mesh depth : ℕ} {p : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hc : 0 < p.physical.ceiling) (hf : CutoffFits p.physical)
    (hz : Member lo hi depth p code z) :
    CutoffFits (realize depth p code z).physical := by
  induction depth generalizing p with
  | zero => exact hf
  | succ d ih =>
      exact ih (perform_ceiling_pos hc hz.2.2.1)
        (perform_cutoffFits hc hf hz.2.2.1) hz.2.2.2

/-- Even the actual max-two clamp obeys the cutoff invariant. No root
full-square test, enhanced-branch assumption or root count licence. -/
theorem frozenRoot_cutoffFits {k : Root} {t : ℝ} (n : ℕ) (tau : ℝ)
    (ht : t ∈ rootBand k) : CutoffFits (frozenRoot n k tau t).physical := by
  have ha : (0:ℝ) < Part5OriginalUpsilon5CausalDictionary.a := by
    norm_num [Part5OriginalUpsilon5CausalDictionary.a]
  have hat := (rootBand_subset k ht).1
  let L := frozenLevel n (sourceRoot k tau t).physical.total-t
  unfold CutoffFits
  rw [frozenRoot_residual]
  change L ≤ max 2 (L/Part5OriginalUpsilon5CausalDictionary.a)*t
  have hL : L ≤ max 2 (L/Part5OriginalUpsilon5CausalDictionary.a)*
      Part5OriginalUpsilon5CausalDictionary.a :=
    (div_le_iff₀ ha).mp (le_max_right 2 _)
  exact hL.trans (mul_le_mul_of_nonneg_left hat (by positivity))

theorem frozenMember_cutoffFits {n mesh depth : ℕ} {k : Root} {tau t lo hi : ℝ}
    {code : Program mesh depth} {z : Coordinates depth} (ht : t ∈ rootBand k)
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    CutoffFits (realize depth (frozenRoot n k tau t) code z).physical := by
  apply realize_cutoffFits _ (frozenRoot_cutoffFits n tau ht) hz
  change 0 < t
  exact (by norm_num [Part5OriginalUpsilon5CausalDictionary.a] :
    (0:ℝ) < Part5OriginalUpsilon5CausalDictionary.a).trans_le (rootBand_subset k ht).1

theorem valid_label_cutoffFits {N n mesh : ℕ} {tau : ℝ} {h : Label N mesh}
    (hv : Valid n tau h) : CutoffFits (labelNode n tau h).physical :=
  frozenMember_cutoffFits hv.2.1 hv.2.2.2.2

/-- Once the true query fits below the ceiling, any later allowed
comparison target also fits; no independent parent-ceiling licence. -/
theorem target_cutoff_le_ceiling {p : PhysicalNode} {target : ℝ}
    (hc : 0 < p.ceiling) (hf : CutoffFits p) (hs : 0 < target)
    (ht : p.argument ≤ target) : residual p/target ≤ p.ceiling := by
  apply (div_le_iff₀ hs).mpr
  exact (hf.trans (mul_le_mul_of_nonneg_right ht hc.le)).trans_eq (mul_comm _ _)

theorem physicalStart_eq_baseStart {up : Bool} {p : PhysicalNode}
    (hc : 0 < p.ceiling) (hf : CutoffFits p) :
    physicalStart up p = baseStart up p := by
  have hq : residual p/p.ceiling ≤ p.argument := (div_le_iff₀ hc).mpr hf
  apply max_eq_left
  cases up
  · change residual p/p.ceiling-1 ≤ p.argument-1
    linarith
  · change residual p/p.ceiling-1 ≤ max 2 (p.argument-1)
    exact (by linarith : residual p/p.ceiling-1 ≤ p.argument-1).trans (le_max_right _ _)

/-- These are the two original full interval profiles, without the extra
inherited-ceiling max. The old arrays remain arbitrary and unclamped. -/
def originalProfile (up : Bool) (s : ℝ) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∫ w in Icc (if up then max 2 (s-1) else s-1) 5,
    tableFunction up (if up then oldh else oldH) w / w

theorem idealProfile_eq_original {up : Bool} {p : PhysicalNode}
    (hc : 0 < p.ceiling) (hf : CutoffFits p) (hg : directionGuard up p)
    (oldH oldh : Fin 200 → ℤ) :
    Part5OriginalBuchstabImmutable430Budget.idealProfile up p oldH oldh =
      originalProfile up p.argument oldH oldh := by
  have hs : 1 ≤ baseStart up p := by
    rw [← physicalStart_eq_baseStart hc hf]
    exact physicalStart_ge_one hg
  unfold Part5OriginalBuchstabImmutable430Budget.idealProfile originalProfile
  rw [physicalStart_eq_baseStart hc hf]
  apply setIntegral_congr_fun measurableSet_Icc
  intro w hw
  have hw' : w ∈ buchstabAmbient := ⟨hs.trans hw.1, hw.2⟩
  rw [buchstabKernel_eq_raw hw']
  ring

end
end ImbalancedChen.Part5OriginalH430CutoffCoherence
