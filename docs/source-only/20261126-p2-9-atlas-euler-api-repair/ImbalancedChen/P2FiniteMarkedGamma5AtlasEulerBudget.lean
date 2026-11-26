import ImbalancedChen.P2OriginalSmoothReadoutCore
import ImbalancedChen.P2OriginalChartDerivativeCore
import ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget
import ImbalancedChen.P2Gamma5AdmissibleFamilyCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL OR KERNEL CREDIT.

A fixed original causal atlas is evaluated on the individual OLD prime
logarithms, then multiplied by the unchanged Gamma5 physical profile.
The smooth positive argument is the existing clamp. Its removal is a
global product identity because the original profile vanishes whenever
a physical coordinate is at or below half the positive floor.

All derivative constants are chosen after the fixed atlas, rank ceiling,
width and order, but before the target, total level, floor, accepted atom
set, physical base or Euler word. The finite atom sum is bounded explicitly;
smoothness alone is not used as a global derivative bound.

This constructs no smooth realization of an arbitrary discrete selected
history. It proves no ordinary-mass, J, distribution or PP assertion.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5AtlasEulerBudget

noncomputable section
open Finset Set Real
open Part5OriginalCausalSmoothAtlas
open Part5OriginalH430JointQueryEnclosure (readout readout_smooth)
open Part5OriginalH430ClassicalSmoothEulerBounds
  (E ScalarBound BoundedDerivatives plateau_bound)
open Part5OriginalH430ClassicalSmoothEulerProfile (coord)
open Part5OriginalH430ClassicalSmoothEulerConjugacy (flow flow_smooth norm_bound_at_zero)
open Part5OriginalH430ClassicalSmoothRealProfile
  (positiveArg positiveArg_eq positiveArg_pos positiveArg_smooth)
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5EulerWordBudget
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerWord)
open scoped Classical BigOperators ContDiff

/-- The original separate old coordinates, without collapsing their product. -/
def oldLogCoordinates {k r : ℕ} (N : ℝ)
    (v : E (k + (2 + r))) : Fin k → ℝ :=
  fun i => log (v (Fin.castAdd (2 + r) i)) / log N

/-- The existing positive clamp makes every logarithm globally smooth. -/
def safeOldLogCoordinates {k r : ℕ} (N b : ℝ)
    (v : E (k + (2 + r))) : Fin k → ℝ :=
  fun i => log (positiveArg (b / 2) (v (Fin.castAdd (2 + r) i))) / log N

/-- Fixed atlas readout times the original Gamma5 profile. No primality,
coprimality, selected-history indicator or arithmetic filter is inserted. -/
def atlasProfile {k r : ℕ} (P : Plan) (accept : (Fin k → Code P) → Prop)
    (logQ N width b : ℝ) (v : E (k + (2 + r))) : ℝ :=
  finPhysicalProfile logQ N width b v *
    readout P accept (safeOldLogCoordinates N b v)

theorem contDiff_atlasProfile {k r : ℕ} (P : Plan)
    (accept : (Fin k → Code P) → Prop) (logQ N width : ℝ) {b : ℝ}
    (hb : 0 < b) :
    ContDiff ℝ ∞ (atlasProfile (r := r) P accept logQ N width b) := by
  have hsafe : ContDiff ℝ ∞
      (safeOldLogCoordinates (k := k) (r := r) N b) := by
    apply contDiff_pi.mpr
    intro i
    exact (((positiveArg_smooth (b / 2)).comp
      (contDiff_apply ℝ ℝ (Fin.castAdd (2 + r) i))).log
        (fun v => (positiveArg_pos (half_pos hb) (v _)).ne')).div_const (log N)
  exact (contDiff_finPhysicalProfile logQ N width hb).mul
    ((readout_smooth P accept).comp hsafe)

/-- This equality holds on the whole real coordinate space. The singular
unclamped logarithms are used only in an equal product, never to assert
smoothness of their factors at zero. -/
theorem atlasProfile_eq_original_weight {k r : ℕ} (P : Plan)
    (accept : (Fin k → Code P) → Prop) (logQ N width : ℝ) {b : ℝ}
    (hb : 0 < b) (v : E (k + (2 + r))) :
    atlasProfile P accept logQ N width b v =
      finPhysicalProfile logQ N width b v *
        readout P accept (oldLogCoordinates N v) := by
  unfold atlasProfile
  by_cases hz : finPhysicalProfile logQ N width b v = 0
  · simp only [hz, zero_mul]
  · congr 1
    apply congrArg (readout P accept)
    funext i
    have hi := physicalProfile_nonzero_lower hb hz (Sum.inl i)
    change b / 2 < v (Fin.castAdd (2 + r) i) at hi
    simp only [safeOldLogCoordinates, oldLogCoordinates,
      positiveArg_eq (half_pos hb) hi.le]

theorem atlasProfile_nonneg {k r : ℕ} (P : Plan)
    (accept : (Fin k → Code P) → Prop) (logQ N width b : ℝ)
    (v : E (k + (2 + r))) :
    0 ≤ atlasProfile P accept logQ N width b v := by
  apply mul_nonneg (physicalProfile_bounds logQ N width b (finToPhysical k r v)).1
  unfold readout
  apply sum_nonneg
  intro j _
  by_cases hj : accept j
  · simpa only [if_pos hj] using atom_nonneg P j (safeOldLogCoordinates N b v)
  · simp only [if_neg hj, le_refl]

/-- Only the original physical support can contribute. -/
theorem atlasProfile_nonzero_original {k r : ℕ} (P : Plan)
    (accept : (Fin k → Code P) → Prop) (logQ N width b : ℝ)
    (v : E (k + (2 + r)))
    (hne : atlasProfile P accept logQ N width b v ≠ 0) :
    finPhysicalProfile logQ N width b v ≠ 0 :=
  (mul_ne_zero_iff.mp hne).1

/-- Compactness of a fixed atlas mask supplies its global scalar bounds.
The existing plateau lemma is reused; no new derivative estimate is proved. -/
private theorem mask_scalar_bound (P : Plan) (j : Code P) :
    ScalarBound (mask P j) := by
  obtain ⟨B, hB⟩ := (mask_compact P j :
    IsCompact (tsupport (mask P j))).exists_bound_of_continuousOn
      (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) _)
  apply plateau_bound (mask_smooth P j)
    (fun x => by
      rw [abs_of_nonneg (mask_nonneg P j x)]
      exact mask_le_one P j x)
    (l := -(max 0 B + 1)) (u := max 0 B + 1) (v := 0) (w := 0)
  · intro x hx
    by_contra hn
    have hbound : |x| ≤ B := by
      simpa only [Real.norm_eq_abs, id] using hB x
        (subset_closure (show x ∈ Function.support (mask P j) from hn))
    have hleft := (abs_le.mp hbound).1
    linarith [le_max_right (0 : ℝ) B]
  · intro x hx
    by_contra hn
    have hbound : |x| ≤ B := by
      simpa only [Real.norm_eq_abs, id] using hB x
        (subset_closure (show x ∈ Function.support (mask P j) from hn))
    have hright := (abs_le.mp hbound).2
    linarith [le_max_right (0 : ℝ) B]

/-- Every parameter below varies after the atlas derivative constant. -/
private abbrev ChartParam (P : Plan) (k : ℕ) :=
  ((Fin k → Code P) → Prop) × {N : ℝ // 2 ≤ N} × (Fin k → ℝ)

private def readoutChart {k r : ℕ} (P : Plan) (a : ChartParam P k)
    (u : E (k + (2 + r))) : ℝ :=
  readout P a.1 (fun i =>
    (a.2.2 i + u (Fin.castAdd (2 + r) i)) / log a.2.1.val)

private theorem atom_chart_budget (P : Plan) (k r : ℕ) (j : Fin k → Code P) :
    BoundedDerivatives (fun (a : ChartParam P k) (u : E (k + (2 + r))) =>
      atom P j (fun i =>
        (a.2.2 i + u (Fin.castAdd (2 + r) i)) / log a.2.1.val)) := by
  have H (i : Fin k) : BoundedDerivatives
      (fun (a : ChartParam P k) (u : E (k + (2 + r))) =>
        mask P (j i) ((a.2.2 i + u (Fin.castAdd (2 + r) i)) / log a.2.1.val)) := by
    have h := Part5OriginalH430ClassicalSmoothEulerBounds.affine
      (mask_scalar_bound P (j i))
      (fun a : ChartParam P k => a.2.2 i / log a.2.1.val)
      (fun a : ChartParam P k => 1 / log a.2.1.val)
      (coord (Fin.castAdd (2 + r) i))
      (R := 1 / log 2)
      (one_div_pos.mpr (log_pos (by norm_num : (1 : ℝ) < 2))).le
      (fun a => by
        have hL := log_le_log (by norm_num : (0 : ℝ) < 2) a.2.1.property
        have hpos := log_pos (by norm_num : (1 : ℝ) < 2)
        rw [abs_of_nonneg (one_div_nonneg.mpr (hpos.le.trans hL))]
        exact one_div_le_one_div_of_le hpos hL)
    convert h using 1
    funext a u
    apply congrArg (mask P (j i))
    simp only [coord, ContinuousLinearMap.proj_apply]
    ring
  simpa only [atom] using
    (Part5OriginalH430ClassicalSmoothEulerBounds.prod
      (univ : Finset (Fin k)) _ H)

/-- Uniformity in accept is obtained by an explicit sum over the fixed
finite atlas, including the unique empty-coordinate atom when k = 0. -/
private theorem readout_chart_budget (P : Plan) (k r : ℕ) :
    BoundedDerivatives (readoutChart (k := k) (r := r) P) := by
  let F (j : Fin k → Code P) (a : ChartParam P k)
      (u : E (k + (2 + r))) : ℝ :=
    if a.1 j then atom P j (fun i =>
      (a.2.2 i + u (Fin.castAdd (2 + r) i)) / log a.2.1.val) else 0
  have H (j : Fin k → Code P) : BoundedDerivatives (F j) := by
    have hj := atom_chart_budget P k r j
    refine ⟨?_, ?_⟩
    · intro a
      by_cases ha : a.1 j
      · simpa only [F, if_pos ha] using hj.1 a
      · simpa only [F, if_neg ha] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : E (k + (2 + r)) => (0 : ℝ)))
    · intro q
      obtain ⟨C, hC, HC⟩ := hj.2 q
      refine ⟨C, hC, ?_⟩
      intro a u
      by_cases ha : a.1 j
      · simpa only [F, if_pos ha] using HC a u
      · simp only [F, if_neg ha]
        cases q with
        | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using hC
        | succ q =>
          simpa only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero q),
            Pi.zero_apply, norm_zero] using hC
  have Hsum (S : Finset (Fin k → Code P)) :
      BoundedDerivatives (fun a u => ∑ j ∈ S, F j a u) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa only [sum_empty, sub_self] using
          (Part5OriginalH430ClassicalSmoothEulerBounds.sub
            (Part5OriginalH430ClassicalSmoothEulerBounds.one
              (ι := ChartParam P k) (d := k + (2 + r)))
            Part5OriginalH430ClassicalSmoothEulerBounds.one)
    | @insert j S hj ih =>
        simpa only [sum_insert hj] using
          Part5OriginalH430ClassicalSmoothEulerBounds.add (H j) ih
  have hreadout : readoutChart (k := k) (r := r) P =
      (fun (a : ChartParam P k) (u : E (k + (2 + r))) =>
        ∑ j ∈ (univ : Finset (Fin k → Code P)), F j a u) := by
    funext a u
    unfold readoutChart readout
    apply Finset.sum_congr
    · ext j
      simp
    · intro j _
      rfl
  rw [hreadout]
  exact Hsum univ

private structure ProfileParam (P : Plan) (k r : ℕ) where
  accept : (Fin k → Code P) → Prop
  N : {N : ℝ // 2 ≤ N}
  logQ : ℝ
  b : {b : ℝ // 0 < b}
  base : E (k + (2 + r))

private theorem product_chart_budget (P : Plan) (k r : ℕ)
    (width : ℝ) (hw : 0 < width) :
    BoundedDerivatives (fun (a : ProfileParam P k r) (u : E (k + (2 + r))) =>
      finPhysicalProfile a.logQ a.N.val width a.b.val (flow a.base u) *
        readout P a.accept (fun i =>
          (log (a.base (Fin.castAdd (2 + r) i)) + u (Fin.castAdd (2 + r) i)) /
            log a.N.val)) := by
  let F := fun (a : ProfileParam P k r) (u : E (k + (2 + r))) =>
    finPhysicalProfile a.logQ a.N.val width a.b.val (flow a.base u)
  let G := fun (a : ProfileParam P k r) (u : E (k + (2 + r))) =>
    readoutChart P
      (a.accept, a.N, fun i => log (a.base (Fin.castAdd (2 + r) i))) u
  have hF : BoundedDerivatives F := by
    refine ⟨fun a => (contDiff_finPhysicalProfile a.logQ a.N.val width
      a.b.property).comp (flow_smooth a.base), ?_⟩
    intro q
    obtain ⟨C, hC, HC⟩ := finPhysicalProfile_chart_tensor_budget k r q
    refine ⟨C * (1 + width⁻¹) ^ q,
      mul_nonneg hC (pow_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hw.le)) _), ?_⟩
    intro a u
    exact HC a.logQ a.N.val a.b.val width a.b.property hw a.base u
  have hG : BoundedDerivatives G := by
    have H := readout_chart_budget P k r
    refine ⟨fun a => H.1
      (a.accept, a.N, fun i => log (a.base (Fin.castAdd (2 + r) i))), ?_⟩
    intro q
    obtain ⟨C, hC, HC⟩ := H.2 q
    exact ⟨C, hC, fun a u => HC
      (a.accept, a.N, fun i => log (a.base (Fin.castAdd (2 + r) i))) u⟩
  simpa only [F, G, readoutChart] using
    Part5OriginalH430ClassicalSmoothEulerBounds.mul hF hG

/-- Full chart bounds for the globally smooth product, including negative
and zero bases. The width is fixed before the constant. -/
theorem atlasProfile_chart_tensor_budget (P : Plan) (k r : ℕ)
    (width : ℝ) (hw : 0 < width) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (logQ b : ℝ), 0 < b →
      ∀ (accept : (Fin k → Code P) → Prop) (v u : E (k + (2 + r))),
        ‖iteratedFDeriv ℝ q
          (fun z => atlasProfile P accept logQ N width b (flow v z)) u‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := (product_chart_budget P k r width hw).2 q
  refine ⟨C, hC, ?_⟩
  intro N hN logQ b hb accept v u
  by_cases hv : ∀ i, 0 < v i
  · have heq : (fun z => atlasProfile P accept logQ N width b (flow v z)) =
        fun z => finPhysicalProfile logQ N width b (flow v z) *
          readout P accept (fun i =>
            (log (v (Fin.castAdd (2 + r) i)) + z (Fin.castAdd (2 + r) i)) / log N) := by
      funext z
      rw [atlasProfile_eq_original_weight P accept logQ N width hb]
      congr 1
      apply congrArg (readout P accept)
      funext i
      simp only [oldLogCoordinates, flow,
        log_mul (hv (Fin.castAdd (2 + r) i)).ne' (exp_pos _).ne', log_exp]
    rw [heq]
    exact H ⟨accept, ⟨N, hN⟩, logQ, ⟨b, hb⟩, v⟩ u
  · obtain ⟨i, hi⟩ := not_forall.mp hv
    have heq : (fun z => atlasProfile P accept logQ N width b (flow v z)) =
        fun _ => (0 : ℝ) := by
      funext z
      have hz : finPhysicalProfile logQ N width b (flow v z) = 0 := by
        apply physicalProfile_eq_zero_of_slot_le_half hb ((slotEquiv k r).symm i)
        change flow v z (slotEquiv k r ((slotEquiv k r).symm i)) ≤ b / 2
        rw [Equiv.apply_symm_apply]
        exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi)
          (exp_pos (z i)).le).trans (half_pos hb).le
      simp only [atlasProfile, hz, zero_mul]
    rw [heq]
    cases q with
    | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using hC
    | succ q =>
        simpa only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero q),
          Pi.zero_apply, norm_zero] using hC

/-- The exact original list-fold Euler operators are bounded at every
physical point; the fixed finite set of orders is summed before N. -/
theorem atlasProfile_mixedEuler_budget (P : Plan) (k r : ℕ)
    (width : ℝ) (hw : 0 < width) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (logQ b : ℝ), 0 < b →
      ∀ (accept : (Fin k → Code P) → Prop)
        (w : List (Fin (k + (2 + r)))) (v : E (k + (2 + r))),
        w.length ≤ m → |eulerWord w (atlasProfile P accept logQ N width b) v| ≤ C := by
  choose C hC HC using fun q : ℕ => atlasProfile_chart_tensor_budget P k r width hw q
  refine ⟨∑ q ∈ range (m + 1), C q, sum_nonneg (fun q _ => hC q), ?_⟩
  intro N hN logQ b hb accept w v hwm
  exact ((norm_bound_at_zero (contDiff_atlasProfile P accept logQ N width hb) w v).trans
    (HC w.length N hN logQ b hb accept v 0)).trans
      (single_le_sum (fun q _ => hC q) (mem_range.mpr (Nat.lt_succ_of_le hwm)))

/-- One constant works for every permitted old/tail split and every
accepted subset of its fixed atlas. The rank ceiling is fixed before N. -/
theorem atlasProfile_boundedRank_mixedEuler_budget (P : Plan) (K : ℕ)
    (width : ℝ) (hw : 0 < width) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k r : ℕ), k + 2 + r ≤ K →
      ∀ (N : ℝ), 2 ≤ N → ∀ (logQ b : ℝ), 0 < b →
      ∀ (accept : (Fin k → Code P) → Prop)
        (w : List (Fin (k + (2 + r)))) (v : E (k + (2 + r))),
        w.length ≤ m → |eulerWord w (atlasProfile P accept logQ N width b) v| ≤ C := by
  choose C hC HC using fun k r : ℕ => atlasProfile_mixedEuler_budget P k r width hw m
  have hrow (k : ℕ) : 0 ≤ ∑ r ∈ range (K + 1), C k r :=
    sum_nonneg (fun r _ => hC k r)
  refine ⟨∑ k ∈ range (K + 1), ∑ r ∈ range (K + 1), C k r,
    sum_nonneg (fun k _ => hrow k), ?_⟩
  intro k r hkr N hN logQ b hb accept w v hwm
  have hk : k ≤ K := by omega
  have hr : r ≤ K := by omega
  have hinner : C k r ≤ ∑ j ∈ range (K + 1), C k j :=
    single_le_sum (fun j _ => hC k j) (mem_range.mpr (Nat.lt_succ_of_le hr))
  have houter : (∑ j ∈ range (K + 1), C k j) ≤
      ∑ i ∈ range (K + 1), ∑ j ∈ range (K + 1), C i j :=
    single_le_sum (fun i _ => hrow i) (mem_range.mpr (Nat.lt_succ_of_le hk))
  exact (HC k r N hN logQ b hb accept w v hwm).trans (hinner.trans houter)

/-- Natural constants in the unchanged Family.mixedEuler format, with
logarithmic exponent zero. This is a derivative-field supplier on N >= 2,
not a replacement Family or a smooth realization of discrete B. -/
theorem atlasProfile_family_mixedEuler_budget (P : Plan) (K : ℕ)
    (width : ℝ) (hw : 0 < width) (m : ℕ) :
    ∃ C B : ℕ, 0 < C ∧ B = 0 ∧ ∀ (k r : ℕ), k + 2 + r ≤ K →
      ∀ (N : ℕ), 2 ≤ N → ∀ (logQ b : ℝ), 0 < b →
      ∀ (accept : (Fin k → Code P) → Prop)
        (w : List (Fin (k + (2 + r)))) (v : E (k + (2 + r))),
        w.length ≤ m →
        |eulerWord w (atlasProfile P accept logQ (N : ℝ) width b) v| ≤
          (C : ℝ) * (log ((N : ℝ) + 2)) ^ B := by
  obtain ⟨C0, _hC0, H⟩ := atlasProfile_boundedRank_mixedEuler_budget P K width hw m
  let C : ℕ := Nat.ceil C0 + 1
  have hC : 0 < C := by dsimp [C]; omega
  have hround : C0 ≤ (C : ℝ) := by
    calc
      _ ≤ (Nat.ceil C0 : ℝ) := Nat.le_ceil _
      _ ≤ (C : ℝ) := by
        dsimp [C]
        exact_mod_cast Nat.le_succ (Nat.ceil C0)
  refine ⟨C, 0, hC, rfl, ?_⟩
  intro k r hkr N hN logQ b hb accept w v hwm
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  simpa only [pow_zero, mul_one] using
    (H k r hkr (N : ℝ) hN' logQ b hb accept w v hwm).trans hround

end
end ImbalancedChen.P2FiniteMarkedGamma5AtlasEulerBudget
