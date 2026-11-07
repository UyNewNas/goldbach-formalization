import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank
import ImbalancedChen.P5ZU1011H248CommonPartition
import Mathlib.Topology.Order.Lattice

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual nonlinear original sixteen-policy minimum on a common geometric
state. Each original policy keeps its own selected/W cap branch, complete
eligibility flag and actual H248 atom, including clamp knots and exterior.
Only the residual denominator is clipped away from zero outside the state.
On the original state the full-square gate proves residual>w>=417/5000,
so clipping is exactly inactive. The finite minimum is taken BEFORE the
prime test sum and BEFORE integration. No minimum-of-means step occurs.

The final PNT supplier consumes geometric affine sandwich data only.
It has no cell-mean, convergence, count-bound, AP or table-license premise.
-/
namespace ImbalancedChen.P5Z.U1011OriginalSixteenStateKernel

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical U11H248 U1011H248Partition
open U1011OriginalSixteenPolicyBank U1011AdaptivePrimeError

/-- State data are values of the actual original sixteen policy circuit. -/
structure State where
  branch : Policy → Bool
  active : Policy → Bool
  atom : Policy → AtomState

/-- A geometry-only state predicate. Atom data are required only for an
eligible policy, since every ineligible tag reads the switched fallback. -/
def stateCell (s : State) : Set LogFour :=
  {v | ∀ p : Policy,
    cap p v = affineCap p (s.branch p) v ∧
    (s.active p = true ↔ TypedEligible p v) ∧
    (s.active p = true → typedResidual p v / v 3 ∈ scalarCell (s.atom p))}

def affineResidual (s : State) (p : Policy) (v : LogFour) : ℝ :=
  affineCap p (s.branch p) v - U11SelectedLargest.prefixSum v

def frozenOrdinary (s : State) (p : Policy) (v : LogFour) : ℝ :=
  4 * (1 - stateValue (s.atom p)) / max (417 / 5000 : ℝ) (affineResidual s p v)

def actualSwitched (v : LogFour) : ℝ :=
  switchedKernel currentK LiLiuPrereqBuchstab.buchstab v

/-- Tag0 is switched. Tags1,...,16 are the original sixteen policies;
ineligible policies retain the same switched option, not an extra cost. -/
def frozenCandidate (s : State) (c : ℕ) (v : LogFour) : ℝ :=
  if c = 0 then actualSwitched v
  else if hj : c.pred < 16 then
    if s.active ⟨c.pred, hj⟩ = true then frozenOrdinary s ⟨c.pred, hj⟩ v
    else actualSwitched v
  else actualSwitched v

def frozenMinimum (s : State) : LogFour → ℝ :=
  envelope bank (frozenCandidate s)

def actualCandidate : ℕ → LogFour → ℝ :=
  guarded eligible actualSwitched (ordinaryKernel H248 residual)

def actualMinimum : LogFour → ℝ := envelope bank actualCandidate

theorem affineResidual_eq_original {s : State} {v : LogFour}
    (hv : v ∈ stateCell s) (p : Policy) :
    affineResidual s p v = typedResidual p v := by
  unfold affineResidual typedResidual
  rw [(hv p).1]

theorem continuous_affineResidual (s : State) (p : Policy) :
    Continuous (affineResidual s p) := by
  exact (((capLinear p (s.branch p)).continuous.add continuous_const).sub
    U11SelectedLargest.continuous_prefixSum)

theorem continuous_frozenOrdinary (s : State) (p : Policy) :
    Continuous (frozenOrdinary s p) := by
  apply continuous_const.div (continuous_const.max (continuous_affineResidual s p))
  intro v
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 417 / 5000)
    (le_max_left _ _)).ne'

theorem continuousOn_frozenCandidate (s : State) (c : ℕ) :
    ContinuousOn (frozenCandidate s c) compactBox := by
  have hs : ContinuousOn actualSwitched compactBox :=
    continuousOn_canonical_switched_compactBox currentK
  by_cases hc : c = 0
  · simpa only [frozenCandidate, if_pos hc] using hs
  · by_cases hj : c.pred < 16
    · by_cases ha : s.active ⟨c.pred, hj⟩ = true
      · simpa only [frozenCandidate, if_neg hc, dif_pos hj, if_pos ha] using
          (continuous_frozenOrdinary s ⟨c.pred, hj⟩).continuousOn
      · simpa only [frozenCandidate, if_neg hc, dif_pos hj, if_neg ha] using hs
    · simpa only [frozenCandidate, if_neg hc, dif_neg hj] using hs

/-- Continuity belongs to the TRUE finite nonlinear minimum on the state,
not merely to every separate policy's integral. -/
theorem continuousOn_frozenMinimum (s : State) :
    ContinuousOn (frozenMinimum s) compactBox := by
  have heq : frozenMinimum s = fun v : LogFour =>
      (tags bank).inf' (tags_nonempty bank) (fun c => frozenCandidate s c v) := by
    funext v
    exact (Finset.inf'_eq_csInf_image (tags bank) (tags_nonempty bank)
      (fun c => frozenCandidate s c v)).symm
  rw [heq]
  exact ContinuousOn.finset_inf'_apply (tags_nonempty bank)
    (fun c _ => continuousOn_frozenCandidate s c)

/-- Full-square eligibility supplies the clipping margin for every one
of the sixteen policies, using the actual original smallest coordinate. -/
theorem eligible_affineResidual_lower (s : State) (p : Policy)
    (mask : Set (ℝ × ℝ)) {v : LogFour} (hv : v ∈ originalDomain mask)
    (hs : v ∈ stateCell s) (ha : s.active p = true) :
    (417 / 5000 : ℝ) ≤ affineResidual s p v := by
  rw [affineResidual_eq_original hs p]
  exact hv.1.trans (typedEligible_residual_gt_smallest p v ((hs p).2.1.mp ha)).le

theorem frozenOrdinary_eq_actual (s : State) (p : Policy)
    (mask : Set (ℝ × ℝ)) {v : LogFour} (hv : v ∈ originalDomain mask)
    (hs : v ∈ stateCell s) (ha : s.active p = true) :
    frozenOrdinary s p v =
      4 * (1 - H248 (max 2 (typedResidual p v / v 3))) / typedResidual p v := by
  have hH := H248_eq_stateValue ((hs p).2.2 ha)
  rw [frozenOrdinary, max_eq_right (eligible_affineResidual_lower s p mask hv hs ha),
    affineResidual_eq_original hs p, hH]

theorem candidate_eq_on_state (s : State) (mask : Set (ℝ × ℝ))
    {v : LogFour} (hv : v ∈ originalDomain mask) (hs : v ∈ stateCell s)
    (c : ℕ) (hc : c ∈ tags bank) :
    actualCandidate c v = frozenCandidate s c v := by
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simp only [actualCandidate, guarded, frozenCandidate, if_pos rfl]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hj16 : j < 16 := Finset.mem_range.mp hj
    let p : Policy := ⟨j, hj16⟩
    have he : eligible j v ↔ s.active p = true := by
      simpa only [eligible, dif_pos hj16] using (hs p).2.1.symm
    by_cases ha : s.active p = true
    · have hjEligible : eligible j v := he.mpr ha
      have hordinary := frozenOrdinary_eq_actual s p mask hv hs ha
      simpa only [actualCandidate, guarded, Nat.succ_ne_zero, if_false,
        Nat.pred_succ, if_pos hjEligible, frozenCandidate, dif_pos hj16,
        if_pos ha, ordinaryKernel, residual, p] using hordinary.symm
    · have hjIneligible : ¬eligible j v := fun h => ha (he.mp h)
      simp only [actualCandidate, guarded, Nat.succ_ne_zero, if_false,
        Nat.pred_succ, if_neg hjIneligible, frozenCandidate, dif_pos hj16,
        if_neg ha, p]

/-- Exact identity for the complete nonlinear finite original bank. -/
theorem actualMinimum_eq_frozen (s : State) (mask : Set (ℝ × ℝ))
    {v : LogFour} (hv : v ∈ originalDomain mask) (hs : v ∈ stateCell s) :
    actualMinimum v = frozenMinimum s v := by
  have hb := envelope_abs_sub_le bank actualCandidate (frozenCandidate s) v 0
    (fun c hc => by rw [candidate_eq_on_state s mask hv hs c hc]; simp)
  have heq := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  exact sub_eq_zero.mp heq

theorem integrableOn_frozenMinimum (s : State) (mask : Set (ℝ × ℝ)) :
    IntegrableOn (frozenMinimum s) (originalDomain mask) :=
  ((continuousOn_frozenMinimum s).integrableOn_compact isCompact_compactBox).mono_set
    (originalDomain_subset_compactBox mask)

theorem integrableOn_weighted_frozenMinimum (s : State) (mask : Set (ℝ × ℝ)) :
    IntegrableOn (fun v => harmonicDensity v * frozenMinimum s v) (originalDomain mask) :=
  ((continuousOn_harmonicDensity_compactBox.mul (continuousOn_frozenMinimum s)).integrableOn_compact
    isCompact_compactBox).mono_set (originalDomain_subset_compactBox mask)

/-- A real four-prime PNT supplier for one true full-bank common state.
All hypotheses describe affine geometry and state membership; no mean
or convergence input is assumed. Sibling common-state geometry supplies
the proper forms and this geometric inclusion for each original cell. -/
theorem tendsto_actual_sixteen_state {r : ℕ} (s : State) (mask : Set (ℝ × ℝ))
    (G : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (hG : ∀ j, G j ≠ 0)
    (R : Set LogFour) (hR : MeasurableSet R)
    (hstrict : primeAffineGateRegion G c ⊆ R)
    (hweak : ∀ v ∈ R, ∀ j, G j v ≤ c j)
    (hstate : R ⊆ originalDomain mask ∩ stateCell s) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      (R.indicator actualMinimum)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ R, actualMinimum v * ∏ i, 1 / v i)) := by
  have hc : ContinuousOn (frozenMinimum s)
      (univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
    apply (continuousOn_frozenMinimum s).mono
    intro v hv
    exact ⟨fun j => (hv j (mem_univ j)).1, fun j => (hv j (mem_univ j)).2⟩
  have hpoint (v : LogFour) (hv : v ∈ R) : actualMinimum v = frozenMinimum s v :=
    actualMinimum_eq_frozen s mask (hstate hv).1 (hstate hv).2
  have hind : R.indicator actualMinimum = R.indicator (frozenMinimum s) := by
    funext v
    by_cases hv : v ∈ R
    · simp only [indicator_of_mem hv, hpoint v hv]
    · simp only [indicator_of_notMem hv]
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    G c hG R hR hstrict hweak (frozenMinimum s) hc
  have hint : (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) ∩ R, frozenMinimum s v * ∏ i, 1 / v i) =
      ∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ R, actualMinimum v * ∏ i, 1 / v i := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter hR)
    intro v hv
    rw [hpoint v hv.2]
  rw [hind, ← hint]
  exact hlim

end
end ImbalancedChen.P5Z.U1011OriginalSixteenStateKernel
