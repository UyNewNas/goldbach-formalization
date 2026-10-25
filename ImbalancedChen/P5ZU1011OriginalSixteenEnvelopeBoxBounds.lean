import ImbalancedChen.P5ZU1011OriginalSixteenSwitchedBoxBounds

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Correctly directed finite rational box bounds for the ORIGINAL nonlinear
sixteen-policy minimum. Lower bounds retain every uncertain policy;
upper bounds admit only whole-box certified eligible policies. All use
the true original caps, residuals, H248 lookup and switched fallback.
The coarse switched bounds do not assert mesh convergence or any saved
endpoint check. No desired kernel or envelope interval is an input.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenEnvelopeBoxBounds

noncomputable section

open Set U11Integral Part5UpperTables
open LiLiuPrereqBuchstab
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenSwitchedBoxBounds
open Classical

def possible (p : Policy) (B : Box) : Prop := wholeBoxIneligibleTest p B ≠ true
def certified (p : Policy) (B : Box) : Prop :=
  wholeBoxEligibleTest p B = true ∧ PositiveGuards p B

instance (p : Policy) (B : Box) : Decidable (possible p B) := by unfold possible; infer_instance
instance (p : Policy) (B : Box) : Decidable (certified p B) := by unfold certified; infer_instance

/-- Failed positive residual guards do not erase a possibly eligible
policy from the lower minimum. Its proved nonnegative cost supplies zero. -/
def candidateLower (p : Policy) (B : Box) : ℚ :=
  if PositiveGuards p B then ordinaryLower p B else 0

def lowerValues (B : Box) : Finset ℚ := insert (switchedLower B)
  ((Finset.univ.filter (fun p : Policy => possible p B)).image (fun p => candidateLower p B))

def upperValues (B : Box) : Finset ℚ := insert (switchedUpper B)
  ((Finset.univ.filter (fun p : Policy => certified p B)).image (fun p => ordinaryUpper p B))

theorem lowerValues_nonempty (B : Box) : (lowerValues B).Nonempty :=
  Finset.insert_nonempty _ _
theorem upperValues_nonempty (B : Box) : (upperValues B).Nonempty :=
  Finset.insert_nonempty _ _

def boxLower (B : Box) : ℚ := (lowerValues B).min' (lowerValues_nonempty B)
def boxUpper (B : Box) : ℚ := (upperValues B).min' (upperValues_nonempty B)

def actualEnvelope (v : LogFour) : ℝ := envelope bank
  (guarded eligible (switchedKernel currentK buchstab) (ordinaryKernel H248 residual)) v

theorem eligible_policy (p : Policy) (v : LogFour) :
    eligible p.val v ↔ TypedEligible p v := by
  simp only [eligible, dif_pos p.isLt]

theorem possible_of_eligible (p : Policy) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (he : TypedEligible p v) : possible p B := by
  intro htest
  exact wholeBoxIneligibleTest_sound p B htest v hv he

theorem candidateLower_le_actual (mask : Set (ℝ × ℝ)) (p : Policy) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask)
    (he : TypedEligible p v) :
    (candidateLower p B : ℝ) ≤ ordinaryKernel H248 residual p.val v := by
  by_cases hg : PositiveGuards p B
  · simpa only [candidateLower, if_pos hg] using (actual_ordinary_bounds p B hg hv).1
  · simp only [candidateLower, if_neg hg, Rat.cast_zero]
    exact (ordinary_actual_bounds mask p.val v hD ((eligible_policy p v).mpr he)).1

theorem boxLower_le_switched (mask : Set (ℝ × ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (boxLower B : ℝ) ≤ switchedKernel currentK buchstab v := by
  have hQ : boxLower B ≤ switchedLower B := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hR : (boxLower B : ℝ) ≤ (switchedLower B : ℝ) := by exact_mod_cast hQ
  exact hR.trans (switched_box_bounds mask B hv hD).1

theorem boxLower_le_eligible_ordinary (mask : Set (ℝ × ℝ)) (p : Policy) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask)
    (he : TypedEligible p v) :
    (boxLower B : ℝ) ≤ ordinaryKernel H248 residual p.val v := by
  have hp := possible_of_eligible p B hv he
  have hmem : candidateLower p B ∈ lowerValues B := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩)
  have hQ : boxLower B ≤ candidateLower p B := Finset.min'_le _ _ hmem
  have hR : (boxLower B : ℝ) ≤ (candidateLower p B : ℝ) := by exact_mod_cast hQ
  exact hR.trans (candidateLower_le_actual mask p B hv hD he)

/-- No eligibility/minimum exchange: each ACTUAL guarded candidate is
bounded first, using its actual eligibility at this same point. -/
theorem lower_bound_sound (mask : Set (ℝ × ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (boxLower B : ℝ) ≤ actualEnvelope v := by
  unfold actualEnvelope
  rw [envelope_eq_min]
  apply Finset.le_min'
  intro q hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simpa only [guarded, if_pos rfl] using boxLower_le_switched mask B hv hD
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hj16 : j < 16 := Finset.mem_range.mp hj
    let p : Policy := ⟨j, hj16⟩
    by_cases he : eligible j v
    · have heP : TypedEligible p v := (eligible_policy p v).mp he
      simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_pos he] using
        boxLower_le_eligible_ordinary mask p B hv hD heP
    · simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg he] using
        boxLower_le_switched mask B hv hD

theorem actualEnvelope_le_eligible (p : Policy) {v : LogFour}
    (he : TypedEligible p v) : actualEnvelope v ≤ ordinaryKernel H248 residual p.val v := by
  have heNat := (eligible_policy p v).mpr he
  have htag : p.val.succ ∈ tags bank := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨p.val, Finset.mem_range.mpr p.isLt, rfl⟩)
  have h := envelope_le bank
    (guarded eligible (switchedKernel currentK buchstab) (ordinaryKernel H248 residual))
    v p.val.succ htag
  simpa only [actualEnvelope, guarded, Nat.succ_ne_zero, if_false,
    Nat.pred_succ, if_pos heNat] using h

/-- Only candidates certified eligible on the WHOLE box enter the upper
minimum. Uncertain candidates are deliberately absent from that minimum. -/
theorem upper_bound_sound (mask : Set (ℝ × ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    actualEnvelope v ≤ (boxUpper B : ℝ) := by
  have hmem := Finset.min'_mem (upperValues B) (upperValues_nonempty B)
  change (boxUpper B) ∈ upperValues B at hmem
  rcases Finset.mem_insert.mp hmem with hs | hp
  · rw [hs]
    exact (guarded_envelope_le_switched bank eligible
      (switchedKernel currentK buchstab) (ordinaryKernel H248 residual) v).trans
      (switched_box_bounds mask B hv hD).2
  · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hp
    have hcert := (Finset.mem_filter.mp hp).2
    have he := wholeBoxEligibleTest_sound p B hcert.1 v hv
    rw [← heq]
    exact (actualEnvelope_le_eligible p he).trans (actual_ordinary_bounds p B hcert.2 hv).2

theorem actual_envelope_bounds (mask : Set (ℝ × ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (boxLower B : ℝ) ≤ actualEnvelope v ∧ actualEnvelope v ≤ (boxUpper B : ℝ) :=
  ⟨lower_bound_sound mask B hv hD, upper_bound_sound mask B hv hD⟩

end

end ImbalancedChen.P5Z.OriginalSixteenEnvelopeBoxBounds
