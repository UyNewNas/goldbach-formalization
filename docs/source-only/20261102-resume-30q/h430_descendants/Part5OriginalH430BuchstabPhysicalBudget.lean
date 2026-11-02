import ImbalancedChen.Part5OriginalH430DescendantLimits
import ImbalancedChen.Part5OriginalH430MovingBuchstabAtoms

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual parent ceiling changes the Buchstab lower endpoint.  This file
derives that endpoint from LocalDomain, keeps every closed table atom,
and includes the complete physical parent weight and the original
Jacobian.  P's already proved moving-start strip estimate is reused.

The final budget is the literal localBudget for ONE ordinary Buchstab
action, with its closed FloorAtom values.  It is not identified with a
selected immutable430 action, an arithmetic Theta_Q, or all graph paths.
No hypothesis is a coefficient-error or desired localBudget estimate.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabPhysicalBudget

noncomputable section
open Set MeasureTheory Filter Topology Classical
open scoped BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430DescendantLimits
open Part5OriginalH430MovingBuchstabAtoms

/-- true means the upper Buchstab action, whose child reads lower h. -/
def buchstabShape (upper : Bool) : StepShape :=
  if upper then .buchstabUpper else .buchstabLower

def directionGuard (upper : Bool) (p : PhysicalNode) : Prop :=
  if upper then True else 2 ≤ p.argument

def baseStart (upper : Bool) (p : PhysicalNode) : ℝ :=
  if upper then max 2 (p.argument-1) else p.argument-1

/-- The second term is the actual inherited physical prime ceiling.
No original 1/50 table grid is used to replace this moving endpoint. -/
def physicalStart (upper : Bool) (p : PhysicalNode) : ℝ :=
  max (baseStart upper p) (residual p/p.ceiling-1)

theorem physicalStart_ge_one {upper : Bool} {p : PhysicalNode}
    (hg : directionGuard upper p) : 1 ≤ physicalStart upper p := by
  apply le_trans _ (le_max_left _ _)
  cases upper
  · change 1 ≤ p.argument-1
    change 2 ≤ p.argument at hg
    linarith
  · exact (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)

/-- A singleton has one physical prime slot; the unused coordinate is zero. -/
def buchstabPoint (p : PhysicalNode) (w : ℝ) : Point :=
  fun i => if i = 0 then residual p/(w+1) else 0

@[simp] theorem buchstabPoint_zero (p : PhysicalNode) (w : ℝ) :
    buchstabPoint p w 0 = residual p/(w+1) := by simp [buchstabPoint]

theorem buchstabPoint_query {p : PhysicalNode} (hL : 0 < residual p)
    {w : ℝ} (hw : 1 ≤ w) : buchstabArgument p (buchstabPoint p w) = w := by
  have hw1 : w+1 ≠ 0 := by linarith
  simp only [buchstabArgument, buchstabPoint_zero]
  field_simp [hL.ne', hw1] <;> ring

/-- Full local admission, including the ceiling and the new square,
is exactly the moving interval below.  This is stronger than membership
in the unconstrained primitive Buchstab domain alone. -/
theorem actual_buchstab_domain {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling)
    (hg : directionGuard upper p) {w : ℝ} (hw : 1 ≤ w) :
    LocalDomain p (buchstabShape upper) (buchstabPoint p w) ↔
      w ∈ Icc (physicalStart upper p) 5 := by
  have hwpos : 0 < w+1 := by linarith
  have hx : 0 < residual p/(w+1) := div_pos hL hwpos
  have hsq : 2*(residual p/(w+1)) ≤ residual p := by
    have hmul : 2*residual p ≤ residual p*(w+1) := by nlinarith
    have hd := (div_le_iff₀ hwpos).mpr hmul
    simpa only [mul_div_assoc] using hd
  have hceil : residual p/(w+1) ≤ p.ceiling ↔ residual p/p.ceiling-1 ≤ w := by
    rw [div_le_iff₀ hwpos]
    have hr : residual p/p.ceiling-1 ≤ w ↔ residual p/p.ceiling ≤ w+1 := by
      constructor <;> intro h <;> linarith
    rw [hr, div_le_iff₀ hC]
    constructor <;> intro h <;> nlinarith
  have hq := buchstabPoint_query hL hw
  cases upper
  · change 2 ≤ p.argument at hg
    simp only [buchstabShape, Bool.false_eq_true, if_false, LocalDomain, hL, true_and,
      hg, OneGate, buchstabPoint_zero, hx, hsq, hq, buchstabLowerDomain,
      mem_Icc, physicalStart, baseStart, max_le_iff]
    tauto
  · simp only [buchstabShape, if_true, LocalDomain, hL, true_and,
      OneGate, buchstabPoint_zero, hx, hsq, hq, buchstabUpperDomain,
      mem_Icc, physicalStart, baseStart, max_le_iff]
    tauto

def physicalAtomPullback (upper : Bool) (p : PhysicalNode) (b : FloorAtom) : Set ℝ :=
  {w | w ∈ buchstabAmbient ∧
    LocalDomain p (buchstabShape upper) (buchstabPoint p w) ∧
    (perform p (buchstabShape upper) (buchstabPoint p w)).argument ∈ tableAtomSet upper b}

def physicalAtomDensity (upper : Bool) (p : PhysicalNode) (b : FloorAtom) : ℝ → ℝ :=
  (physicalAtomPullback upper p b).indicator (fun w =>
    (residual p/(w+1)^2) * physicalWeight (perform p (buchstabShape upper) (buchstabPoint p w)))

theorem physicalAtomPullback_eq {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) :
    physicalAtomPullback upper p b = Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b := by
  ext w
  have harg (hw : 1 ≤ w) :
      (perform p (buchstabShape upper) (buchstabPoint p w)).argument = w := by
    cases upper <;> exact buchstabPoint_query hL hw
  constructor
  · rintro ⟨hw, hd, hb⟩
    exact ⟨(actual_buchstab_domain hL hC hg hw.1).mp hd, (harg hw.1) ▸ hb⟩
  · rintro ⟨hw, hb⟩
    have hw1 := (physicalStart_ge_one hg).trans hw.1
    exact ⟨⟨hw1, hw.2⟩, (actual_buchstab_domain hL hC hg hw1).mpr hw,
      (harg hw1).symm ▸ hb⟩

/-- Includes the true parent word factor and the absolute Jacobian.
The factorization remains exact for a zero product under totalized
division; it does not divide by a selected cell's mass. -/
theorem actual_buchstab_Jacobian {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) {w : ℝ} (hw : w ∈ buchstabAmbient) :
    (residual p/(w+1)^2) *
      physicalWeight (perform p (buchstabShape upper) (buchstabPoint p w)) =
      physicalWeight p * buchstabKernel w := by
  have hperform : perform p (buchstabShape upper) (buchstabPoint p w) =
      appendOne p (residual p/(w+1)) w := by
    have hq := buchstabPoint_query hL hw.1
    cases upper <;> simp only [buchstabShape, if_true, if_false, Bool.false_eq_true,
      perform, buchstabPoint_zero, hq]
  rw [hperform]
  by_cases hP : (word p).prod = 0
  · simp [physicalWeight, word_appendOne, hP]
  · have hw0 : 0 < w := zero_lt_one.trans_le hw.1
    have hw1 : 0 < w+1 := by linarith
    have hx : residual p/(w+1) ≠ 0 := div_ne_zero hL.ne' hw1.ne'
    have hnew : residual p-residual p/(w+1) ≠ 0 := by
      have he : residual p-residual p/(w+1) = residual p*w/(w+1) := by
        field_simp [hw1.ne']
        ring
      rw [he]
      exact div_ne_zero (mul_ne_zero hL.ne' hw0.ne') hw1.ne'
    rw [physicalWeight_singleton p _ w hP hL.ne' hx hnew]
    calc
      _ = physicalWeight p * ((residual p/(w+1)^2) *
        physicalSingletonKernel (residual p) (residual p/(w+1))) := by ring
      _ = _ := by rw [buchstab_Jacobian hL hw]

theorem physicalAtomDensity_eq {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) (w : ℝ) :
    physicalAtomDensity upper p b w =
      physicalWeight p * startAtomDensity upper b (physicalStart upper p) w := by
  rw [physicalAtomDensity, physicalAtomPullback_eq hL hC hg]
  by_cases hw : w ∈ Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b
  · rw [indicator_of_mem hw, startAtomDensity, indicator_of_mem hw]
    exact actual_buchstab_Jacobian hL ⟨(physicalStart_ge_one hg).trans hw.1.1, hw.1.2⟩
  · simp only [indicator_of_notMem hw, startAtomDensity, mul_zero]

def atomMass (upper : Bool) (b : FloorAtom) (c : ℝ) : ℝ :=
  ∫ w, startAtomDensity upper b c w

theorem atomMass_nonneg (upper : Bool) (b : FloorAtom) (c : ℝ) :
    0 ≤ atomMass upper b c := by
  apply integral_nonneg
  intro w
  exact Set.indicator_nonneg (fun _ _ => buchstabKernel_nonneg _) _

theorem atomMass_le_four (upper : Bool) (b : FloorAtom) {c : ℝ} (hc : 1 ≤ c) :
    atomMass upper b c ≤ 4 := by
  have hb (w : ℝ) : startAtomDensity upper b c w ≤
      (Icc (1 : ℝ) 5).indicator (fun _ => (1 : ℝ)) w := by
    by_cases hw : w ∈ Icc c 5 ∩ tableAtomSet upper b
    · have hw1 : w ∈ Icc (1 : ℝ) 5 := ⟨hc.trans hw.1.1, hw.1.2⟩
      simpa only [startAtomDensity, indicator_of_mem hw, indicator_of_mem hw1]
        using buchstabKernel_le_one w
    · simp only [startAtomDensity, indicator_of_notMem hw]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hi : Integrable ((Icc (1 : ℝ) 5).indicator (fun _ => (1 : ℝ))) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have h := integral_mono (startAtomDensity_integrable upper b c) hi hb
  simpa only [atomMass, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc,
    show max (5-(1 : ℝ)) 0 = 4 by norm_num] using h

theorem atomMass_difference_le (upper : Bool) (b : FloorAtom) (c d : ℝ) :
    |atomMass upper b c-atomMass upper b d| ≤ |c-d| := by
  unfold atomMass
  rw [← integral_sub (startAtomDensity_integrable upper b c)
    (startAtomDensity_integrable upper b d)]
  exact abs_integral_le_integral_abs.trans (startAbsoluteError_bounds upper b c d).2

def coefficient (upper : Bool) (p : PhysicalNode) (b : FloorAtom) : ℝ :=
  physicalWeight p * atomMass upper b (physicalStart upper p)

theorem coefficient_eq_physicalIntegral {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) : coefficient upper p b = ∫ w, physicalAtomDensity upper p b w := by
  simp_rw [physicalAtomDensity_eq hL hC hg]
  rw [integral_const_mul]
  rfl

def weightedAtomError (upper : Bool) (p q : PhysicalNode) (b : FloorAtom) : ℝ :=
  ∫ w, |physicalWeight p*startAtomDensity upper b (physicalStart upper p) w-
    physicalWeight q*startAtomDensity upper b (physicalStart upper q) w|

theorem weightedAtomError_eq_physical {upper : Bool} {p q : PhysicalNode}
    (hLp : 0 < residual p) (hCp : 0 < p.ceiling) (hgp : directionGuard upper p)
    (hLq : 0 < residual q) (hCq : 0 < q.ceiling) (hgq : directionGuard upper q)
    (b : FloorAtom) : weightedAtomError upper p q b =
      ∫ w, |physicalAtomDensity upper p b w-physicalAtomDensity upper q b w| := by
  simp_rw [physicalAtomDensity_eq hLp hCp hgp, physicalAtomDensity_eq hLq hCq hgq]
  rfl

/-- Absolute L1 error is paid before any cancellation of atom masses.
Both factors are literal physical densities after the Buchstab Jacobian;
only the already proved P moving-start strip estimate is reused. -/
theorem weightedAtomError_bounds {upper : Bool} {p q : PhysicalNode}
    (hp : directionGuard upper p) (b : FloorAtom) :
    0 ≤ weightedAtomError upper p q b ∧
      weightedAtomError upper p q b ≤
        4*|physicalWeight p-physicalWeight q| +
          |physicalWeight q|*|physicalStart upper p-physicalStart upper q| := by
  let A := startAtomDensity upper b (physicalStart upper p)
  let B := startAtomDensity upper b (physicalStart upper q)
  have hA := startAtomDensity_integrable upper b (physicalStart upper p)
  have hB := startAtomDensity_integrable upper b (physicalStart upper q)
  have hAn (w : ℝ) : 0 ≤ A w :=
    Set.indicator_nonneg (fun _ _ => buchstabKernel_nonneg _) _
  have hpoint (w : ℝ) : |physicalWeight p*A w-physicalWeight q*B w| ≤
      |physicalWeight p-physicalWeight q|*A w+|physicalWeight q|*|A w-B w| := by
    have he : physicalWeight p*A w-physicalWeight q*B w =
        (physicalWeight p-physicalWeight q)*A w+physicalWeight q*(A w-B w) := by ring
    rw [he]
    simpa only [abs_mul, abs_of_nonneg (hAn w)] using
      abs_add_le ((physicalWeight p-physicalWeight q)*A w) (physicalWeight q*(A w-B w))
  have hi := integral_mono ((hA.const_mul _).sub (hB.const_mul _)).abs
    ((hA.const_mul _).add ((hA.sub hB).abs.const_mul _)) hpoint
  rw [integral_add (hA.const_mul _) ((hA.sub hB).abs.const_mul _),
    integral_const_mul, integral_const_mul] at hi
  change weightedAtomError upper p q b ≤
    |physicalWeight p-physicalWeight q|*atomMass upper b (physicalStart upper p)+
      |physicalWeight q|*startAbsoluteError upper b (physicalStart upper p) (physicalStart upper q) at hi
  refine ⟨integral_nonneg (fun _ => abs_nonneg _), hi.trans ?_⟩
  have hmass := mul_le_mul_of_nonneg_left
    (atomMass_le_four upper b (physicalStart_ge_one hp)) (abs_nonneg (physicalWeight p-physicalWeight q))
  have hstrip := mul_le_mul_of_nonneg_left
    (startAbsoluteError_bounds upper b (physicalStart upper p) (physicalStart upper q)).2
    (abs_nonneg (physicalWeight q))
  nlinarith only [hmass, hstrip]

theorem coefficient_difference_le {upper : Bool} {p q : PhysicalNode}
    (hp : directionGuard upper p) (b : FloorAtom) :
    |coefficient upper p b-coefficient upper q b| ≤
      4*|physicalWeight p-physicalWeight q| +
        |physicalWeight q|*|physicalStart upper p-physicalStart upper q| := by
  have he : coefficient upper p b-coefficient upper q b =
      ∫ w, (physicalWeight p*startAtomDensity upper b (physicalStart upper p) w-
        physicalWeight q*startAtomDensity upper b (physicalStart upper q) w) := by
    rw [integral_sub ((startAtomDensity_integrable upper b _).const_mul _)
      ((startAtomDensity_integrable upper b _).const_mul _), integral_const_mul, integral_const_mul]
    rfl
  rw [he]
  exact abs_integral_le_integral_abs.trans (weightedAtomError_bounds hp b).2

/-- One original ordinary Buchstab action and its actual closed atoms.
This specialization is NOT a serialization of the immutable producer. -/
def buchstabBudget (upper : Bool) (nums : Fin 200 → ℤ) (p q : PhysicalNode) : ℝ :=
  P5RenewalFiniteError.localBudget
    (fun _ : Unit => (Finset.univ : Finset FloorAtom)) (fun _ b => b)
    (fun _ => 0) (fun _ => 0)
    (fun _ => coefficient upper p) (fun _ => coefficient upper q)
    (floorAtomValue nums) ()

theorem buchstabBudget_eq (upper : Bool) (nums : Fin 200 → ℤ) (p q : PhysicalNode) :
    buchstabBudget upper nums p q =
      ∑ b : FloorAtom, |coefficient upper p b-coefficient upper q b| * |floorAtomValue nums b| := by
  simp [buchstabBudget, P5RenewalFiniteError.localBudget]

theorem buchstabBudget_bounds {upper : Bool} (nums : Fin 200 → ℤ) {p q : PhysicalNode}
    (hp : directionGuard upper p) :
    0 ≤ buchstabBudget upper nums p q ∧
      buchstabBudget upper nums p q ≤ floorBound nums *
        (4*|physicalWeight p-physicalWeight q| +
          |physicalWeight q|*|physicalStart upper p-physicalStart upper q|) := by
  rw [buchstabBudget_eq]
  refine ⟨Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)), ?_⟩
  calc
    _ ≤ ∑ b : FloorAtom,
        (4*|physicalWeight p-physicalWeight q| +
          |physicalWeight q|*|physicalStart upper p-physicalStart upper q|) * |floorAtomValue nums b| :=
      Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_right (coefficient_difference_le hp b) (abs_nonneg _))
    _ = _ := by simp only [← Finset.mul_sum, floorBound, Real.norm_eq_abs]; ring

theorem frozenDescendant_physicalStart_tendsto {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) (upper : Bool) :
    Tendsto (fun n => physicalStart upper (frozenDescendant n k t code z)) atTop
      (𝓝 (physicalStart upper (idealDescendant k t code z))) := by
  have hL := frozenDescendant_residual_tendsto ht code z
  have hs := frozenDescendant_argument_tendsto ht hz
  have hc := (hL.div_const (idealDescendant k t code z).ceiling).sub_const 1
  cases upper
  · simpa only [physicalStart, baseStart, Bool.false_eq_true, if_false,
      frozenDescendant_ceiling] using (hs.sub_const 1).max hc
  · simpa only [physicalStart, baseStart, if_true, frozenDescendant_ceiling]
      using (tendsto_const_nhds.max (hs.sub_const 1)).max hc

/-- A real descendant upper-Buchstab coefficient budget tends to zero.
The moving start converges to the moving start, not to a fixed gridpoint. -/
theorem actual_upper_buchstabBudget_tendsto (nums : Fin 200 → ℤ)
    {k : Root} {t lo hi : ℝ} (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => buchstabBudget true nums (frozenDescendant n k t code z)
      (idealDescendant k t code z)) atTop (𝓝 0) := by
  have hb (n : ℕ) := buchstabBudget_bounds nums
    (q := idealDescendant k t code z)
    (p := frozenDescendant n k t code z) (upper := true) trivial
  apply squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
  have hw := ((frozenDescendant_weight_tendsto ht hz).sub tendsto_const_nhds).abs
  have hs := ((frozenDescendant_physicalStart_tendsto ht hz true).sub tendsto_const_nhds).abs
  simpa using (tendsto_const_nhds (x := floorBound nums)).mul
    ((tendsto_const_nhds.mul hw).add (tendsto_const_nhds.mul hs))

theorem actual_upper_weightedAtomError_tendsto (b : FloorAtom)
    {k : Root} {t lo hi : ℝ} (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => weightedAtomError true (frozenDescendant n k t code z)
      (idealDescendant k t code z) b) atTop (𝓝 0) := by
  have hb (n : ℕ) := weightedAtomError_bounds
    (q := idealDescendant k t code z)
    (p := frozenDescendant n k t code z) (upper := true) trivial b
  apply squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
  have hw := ((frozenDescendant_weight_tendsto ht hz).sub tendsto_const_nhds).abs
  have hs := ((frozenDescendant_physicalStart_tendsto ht hz true).sub tendsto_const_nhds).abs
  simpa using (tendsto_const_nhds.mul hw).add (tendsto_const_nhds.mul hs)

/-- The preceding limit is an absolute error for the actual gate-filtered
Jacobian densities of this physical descendant, not merely their signed
integrals.  The outer physical-parent integral remains a separate task. -/
theorem actual_upper_physicalAtomError_tendsto (b : FloorAtom)
    {k : Root} {t lo hi : ℝ} (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => ∫ w,
      |physicalAtomDensity true (frozenDescendant n k t code z) b w-
        physicalAtomDensity true (idealDescendant k t code z) b w|) atTop (𝓝 0) := by
  have hL := idealDescendant_residual_pos ht hz
  have hC := idealDescendant_ceiling_pos ht hz
  have he := (frozenDescendant_residual_tendsto ht code z).eventually (eventually_gt_nhds hL)
  apply (actual_upper_weightedAtomError_tendsto b ht hz).congr'
  filter_upwards [he] with n hn
  exact weightedAtomError_eq_physical hn
    (by simpa only [frozenDescendant_ceiling] using hC) trivial hL hC trivial b

/-- Lower admission has the extra parent s>=2 test.  A strict actual
margin supplies it eventually; the equality stratum is intentionally
not discarded or silently assumed stable by this theorem. -/
theorem actual_lower_buchstabBudget_tendsto (nums : Fin 200 → ℤ)
    {k : Root} {t lo hi : ℝ} (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z)
    (hs2 : 2 < (idealDescendant k t code z).argument) :
    Tendsto (fun n => buchstabBudget false nums (frozenDescendant n k t code z)
      (idealDescendant k t code z)) atTop (𝓝 0) := by
  have hg : ∀ᶠ n : ℕ in atTop, directionGuard false (frozenDescendant n k t code z) :=
    ((frozenDescendant_argument_tendsto ht hz).eventually (eventually_gt_nhds hs2)).mono
      (fun _ h => h.le)
  apply squeeze_zero' (hg.mono (fun n hn =>
    (buchstabBudget_bounds nums (q := idealDescendant k t code z) hn).1))
    (hg.mono (fun n hn => (buchstabBudget_bounds nums (q := idealDescendant k t code z) hn).2))
  have hw := ((frozenDescendant_weight_tendsto ht hz).sub tendsto_const_nhds).abs
  have hs := ((frozenDescendant_physicalStart_tendsto ht hz false).sub tendsto_const_nhds).abs
  simpa using (tendsto_const_nhds (x := floorBound nums)).mul
    ((tendsto_const_nhds.mul hw).add (tendsto_const_nhds.mul hs))

end
end ImbalancedChen.Part5OriginalH430BuchstabPhysicalBudget
