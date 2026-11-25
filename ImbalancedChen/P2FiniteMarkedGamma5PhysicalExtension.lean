import ImbalancedChen.P2FiniteMarkedGamma5LogProfileCore
import ImbalancedChen.P2SmoothPositiveArgumentCore
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

A globally smooth physical extension of the exact original Gamma5 log
profile. Old-prefix primes, the two fresh primes, and every rough-tail
factor have separate tagged coordinates. Repeated values retain their
separate factors; either old-prefix or tail rank may be zero.

The accepted positiveArg and floorGate are reused under their original
fully qualified names. The safe logarithm changes no coordinate on the
nonzero floor support. Above the original positive cutoff b, every floor
is one and the exact original log profile is restored.

The original Gate.product gives exp(width)*N. Together with the derived
lower support b/2, this gives an explicit compact rectangular support.
No rank ceiling, fixed numerical cutoff, compactness premise, derivative
budget, prime-product estimate, or change of coefficient is introduced.
The original arithmetic plateau, collar payment, mixed-Euler budget and
complete physical Family/Licence remain separate obligations.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension

noncomputable section
open Finset Real Set
open P4B
open P2FiniteMarkedGamma5LogExtension
open Part5OriginalH430ClassicalSmoothOuterWeight (floorGate)
open Part5OriginalH430ClassicalSmoothRealProfile
  (positiveArg positiveArg_eq positiveArg_pos positiveArg_smooth)
open scoped Classical BigOperators ContDiff

/-- Disjoint tags retain every old, fresh and tail occurrence separately. -/
abbrev Slot (k r : ℕ) := Fin k ⊕ (Fin 2 ⊕ Fin r)

abbrev PhysicalPoint (k r : ℕ) := Slot k r → ℝ

def physicalProduct {k r : ℕ} (x : PhysicalPoint k r) : ℝ := ∏ i, x i

/-- The prefix is the sum of all old physical logarithms, not a frozen
parameter and not a single old-prime slot. -/
def logPoint {k r : ℕ} (x : PhysicalPoint k r) : Point r :=
  (∑ i, log (x (.inl i)),
    fun i => log (x (.inr (.inl i))),
    fun i => log (x (.inr (.inr i))))

def safeLogPoint {k r : ℕ} (b : ℝ) (x : PhysicalPoint k r) : Point r :=
  (∑ i, log (positiveArg (b / 2) (x (.inl i))),
    fun i => log (positiveArg (b / 2) (x (.inr (.inl i)))),
    fun i => log (positiveArg (b / 2) (x (.inr (.inr i)))))

def floorWeight {k r : ℕ} (b : ℝ) (x : PhysicalPoint k r) : ℝ :=
  ∏ i, floorGate (x i / b)

def physicalProfile {k r : ℕ} (logQ N width b : ℝ) (x : PhysicalPoint k r) : ℝ :=
  floorWeight b x * profile logQ (log N) width (safeLogPoint b x)

theorem physicalProduct_eq {k r : ℕ} (x : PhysicalPoint k r) :
    physicalProduct x = (∏ i, x (.inl i)) *
      x (.inr (.inl 0)) * x (.inr (.inl 1)) *
        (∏ i, x (.inr (.inr i))) := by
  simp only [physicalProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  ring

theorem physicalProduct_pos {k r : ℕ} {x : PhysicalPoint k r}
    (hx : ∀ i, 0 < x i) : 0 < physicalProduct x :=
  prod_pos (fun i _ => hx i)

theorem logPoint_prefix_eq_log_product {k r : ℕ} {x : PhysicalPoint k r}
    (hx : ∀ i : Fin k, 0 < x (.inl i)) :
    (logPoint x).1 = log (∏ i, x (.inl i)) := by
  change (∑ i : Fin k, log (x (.inl i))) = log (∏ i : Fin k, x (.inl i))
  exact (log_prod (s := (univ : Finset (Fin k))) (fun i _ => (hx i).ne')).symm

theorem log_physicalProduct {k r : ℕ} {x : PhysicalPoint k r}
    (hx : ∀ i, 0 < x i) :
    log (physicalProduct x) = (logPoint x).1 + (logPoint x).2.1 0 +
      (logPoint x).2.1 1 + ∑ i, (logPoint x).2.2 i := by
  rw [physicalProduct, log_prod (fun i _ => (hx i).ne')]
  simp only [Fintype.sum_sum_type, logPoint, Fin.sum_univ_two]
  ring

theorem floorWeight_bounds {k r : ℕ} (b : ℝ) (x : PhysicalPoint k r) :
    0 ≤ floorWeight b x ∧ floorWeight b x ≤ 1 :=
  ⟨prod_nonneg (fun _ _ => smoothGateUpperStep_nonneg _ _),
    prod_le_one (fun _ _ => smoothGateUpperStep_nonneg _ _)
      (fun _ _ => smoothGateUpperStep_le_one _ _)⟩

theorem floorWeight_one {k r : ℕ} {b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hx : ∀ i, b ≤ x i) : floorWeight b x = 1 := by
  unfold floorWeight
  apply prod_eq_one
  intro i _
  apply smoothGateUpperStep_eq_one (by norm_num : (0 : ℝ) < 1 / 2)
  exact sub_nonneg.mpr ((one_le_div hb).mpr (hx i))

theorem floorWeight_nonzero_lower {k r : ℕ} {b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hne : floorWeight b x ≠ 0) (i : Slot k r) : b / 2 < x i := by
  have hf := (prod_ne_zero_iff.mp hne) i (mem_univ i)
  have hm := smoothGateUpperStep_nonzero_support (by norm_num : (0 : ℝ) < 1 / 2) hf
  have hratio : 1 / 2 < x i / b := by
    change -(1 / 2 : ℝ) < x i / b - 1 at hm
    linarith only [hm]
  have h := (lt_div_iff₀ hb).mp hratio
  linarith only [h]

theorem safeLogPoint_eq_logPoint {k r : ℕ} {b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hx : ∀ i, b / 2 ≤ x i) : safeLogPoint b x = logPoint x := by
  have harg (i : Slot k r) : positiveArg (b / 2) (x i) = x i :=
    positiveArg_eq (half_pos hb) (hx i)
  simp only [safeLogPoint, logPoint, harg]

theorem contDiff_floorWeight {k r : ℕ} (b : ℝ) :
    ContDiff ℝ ∞ (floorWeight (k := k) (r := r) b) := by
  unfold floorWeight floorGate
  apply contDiff_prod
  intro i _
  exact (contDiff_smoothGateUpperStep _).comp
    (((contDiff_apply ℝ ℝ i).div_const b).sub contDiff_const)

theorem contDiff_safeLogPoint {k r : ℕ} {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (safeLogPoint (k := k) (r := r) b) := by
  have h (i : Slot k r) : ContDiff ℝ ∞
      (fun x : PhysicalPoint k r => log (positiveArg (b / 2) (x i))) :=
    ((positiveArg_smooth (b / 2)).comp (contDiff_apply ℝ ℝ i)).log
      (fun x => (positiveArg_pos (half_pos hb) (x i)).ne')
  exact (ContDiff.sum (fun i _ => h (.inl i))).prodMk
    ((contDiff_pi.mpr (fun i => h (.inr (.inl i)))).prodMk
      (contDiff_pi.mpr (fun i => h (.inr (.inr i)))))

/-- Genuine global smoothness, including every zero and negative physical
coordinate. Positivity of the original cutoff is the only hypothesis. -/
theorem contDiff_physicalProfile {k r : ℕ} (logQ N width : ℝ) {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (physicalProfile (k := k) (r := r) logQ N width b) := by
  exact (contDiff_floorWeight b).mul
    ((contDiff_profile logQ (log N) width).comp (contDiff_safeLogPoint hb))

theorem physicalProfile_bounds {k r : ℕ} (logQ N width b : ℝ)
    (x : PhysicalPoint k r) :
    0 ≤ physicalProfile logQ N width b x ∧ physicalProfile logQ N width b x ≤ 1 := by
  have hF := floorWeight_bounds b x
  have hG := profile_bounds logQ (log N) width (safeLogPoint b x)
  exact ⟨mul_nonneg hF.1 hG.1, mul_le_one₀ hF.2 hG.1 hG.2⟩

/-- The safe formula is globally equal to the original physical-log
formula times the same floor factors. At a zero floor both sides vanish;
on nonzero floor support every original logarithm is exact. -/
theorem physicalProfile_eq_floor_mul_original {k r : ℕ} (logQ N width : ℝ)
    {b : ℝ} (hb : 0 < b) (x : PhysicalPoint k r) :
    physicalProfile logQ N width b x =
      floorWeight b x * profile logQ (log N) width (logPoint x) := by
  unfold physicalProfile
  by_cases hF : floorWeight b x = 0
  · simp only [hF, zero_mul]
  · rw [safeLogPoint_eq_logPoint hb (fun i => (floorWeight_nonzero_lower hb hF i).le)]

/-- Exact agreement on the original positive-cutoff domain. Neither the
original profile nor any old/fresh/tail label is replaced. -/
theorem physicalProfile_eq_original {k r : ℕ} (logQ N width : ℝ)
    {b : ℝ} {x : PhysicalPoint k r} (hb : 0 < b) (hx : ∀ i, b ≤ x i) :
    physicalProfile logQ N width b x = profile logQ (log N) width (logPoint x) := by
  rw [physicalProfile_eq_floor_mul_original logQ N width hb x,
    floorWeight_one hb hx, one_mul]

theorem physicalProfile_nonzero_lower {k r : ℕ} {logQ N width b : ℝ}
    {x : PhysicalPoint k r} (hb : 0 < b)
    (hne : physicalProfile logQ N width b x ≠ 0) (i : Slot k r) : b / 2 < x i := by
  exact floorWeight_nonzero_lower hb (mul_ne_zero_iff.mp hne).1 i

theorem physicalProfile_eq_zero_of_slot_le_half {k r : ℕ} {logQ N width b : ℝ}
    {x : PhysicalPoint k r} (hb : 0 < b) (i : Slot k r) (hx : x i ≤ b / 2) :
    physicalProfile logQ N width b x = 0 := by
  by_contra hne
  exact (not_lt_of_ge hx) (physicalProfile_nonzero_lower hb hne i)

/-- The actual original product gate, in physical logarithmic width,
supplies the complete-product cap. No extra coordinate cap is inserted. -/
theorem physicalProfile_nonzero_product_lt {k r : ℕ} {logQ N width b : ℝ}
    {x : PhysicalPoint k r} (hb : 0 < b) (hN : 0 < N) (hw : 0 < width)
    (hne : physicalProfile logQ N width b x ≠ 0) :
    physicalProduct x < exp width * N := by
  have hx (i : Slot k r) : 0 < x i :=
    (half_pos hb).trans (physicalProfile_nonzero_lower hb hne i)
  have hraw := hne
  rw [physicalProfile_eq_floor_mul_original logQ N width hb x] at hraw
  have hp := (mul_ne_zero_iff.mp hraw).2
  have hm := profile_nonzero_margin hw hp Gate.product (mem_program.mpr trivial)
  change -width < log N - ((logPoint x).1 + (logPoint x).2.1 0 +
    (logPoint x).2.1 1 + ∑ i, (logPoint x).2.2 i) at hm
  rw [← log_physicalProduct hx] at hm
  have hl : log (physicalProduct x) < width + log N := by linarith only [hm]
  have he := exp_lt_exp.mpr hl
  simpa only [exp_log (physicalProduct_pos hx), exp_add, exp_log hN] using he

/-- A derived coordinate upper bound. The finite slot count is the actual
sum-type cardinality; no global rank ceiling is assumed. -/
def supportUpper (k r : ℕ) (N width b : ℝ) : ℝ :=
  (exp width * N) * (b / 2) / (b / 2) ^ Fintype.card (Slot k r)

theorem physicalProfile_nonzero_upper {k r : ℕ} {logQ N width b : ℝ}
    {x : PhysicalPoint k r} (hb : 0 < b) (hN : 0 < N) (hw : 0 < width)
    (hne : physicalProfile logQ N width b x ≠ 0) (i : Slot k r) :
    x i < supportUpper k r N width b := by
  let a := b / 2
  have ha : 0 < a := half_pos hb
  have hy (j : Slot k r) : 1 ≤ x j / a :=
    (one_le_div ha).mpr (physicalProfile_nonzero_lower hb hne j).le
  have hsingle : x i / a ≤ ∏ j, x j / a := by
    have he : 1 ≤ ∏ j ∈ (univ : Finset (Slot k r)).erase i, x j / a :=
      one_le_prod (fun j _ => hy j)
    calc
      x i / a = 1 * (x i / a) := (one_mul _).symm
      _ ≤ (∏ j ∈ (univ : Finset (Slot k r)).erase i, x j / a) * (x i / a) :=
        mul_le_mul_of_nonneg_right he (zero_le_one.trans (hy i))
      _ = ∏ j, x j / a := prod_erase_mul _ _ (mem_univ i)
  have hquot : (∏ j, x j / a) = physicalProduct x / a ^ Fintype.card (Slot k r) := by
    simp only [physicalProduct, prod_div_distrib, prod_const, card_univ]
  calc
    x i = (x i / a) * a := (div_mul_cancel₀ _ ha.ne').symm
    _ ≤ (∏ j, x j / a) * a := mul_le_mul_of_nonneg_right hsingle ha.le
    _ = physicalProduct x * a / a ^ Fintype.card (Slot k r) := by rw [hquot]; ring
    _ < (exp width * N) * a / a ^ Fintype.card (Slot k r) :=
      div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_right (physicalProfile_nonzero_product_lt hb hN hw hne) ha)
        (pow_pos ha _)
    _ = supportUpper k r N width b := rfl

/-- This rectangle is independent of logQ and contains the support for
every original gate endpoint with the fixed physical N, width and cutoff. -/
def supportBox (k r : ℕ) (N width b : ℝ) : Set (PhysicalPoint k r) :=
  Icc (fun _ => b / 2) (fun _ => supportUpper k r N width b)

theorem isCompact_supportBox (k r : ℕ) (N width b : ℝ) :
    IsCompact (supportBox k r N width b) := isCompact_Icc

theorem support_physicalProfile_subset_box {k r : ℕ} (logQ : ℝ) {N width b : ℝ}
    (hb : 0 < b) (hN : 0 < N) (hw : 0 < width) :
    Function.support (physicalProfile (k := k) (r := r) logQ N width b) ⊆
      supportBox k r N width b := by
  intro x hx
  exact ⟨fun i => (physicalProfile_nonzero_lower hb hx i).le,
    fun i => (physicalProfile_nonzero_upper hb hN hw hx i).le⟩

theorem tsupport_physicalProfile_subset_box {k r : ℕ} (logQ : ℝ) {N width b : ℝ}
    (hb : 0 < b) (hN : 0 < N) (hw : 0 < width) :
    tsupport (physicalProfile (k := k) (r := r) logQ N width b) ⊆
      supportBox k r N width b :=
  closure_minimal (support_physicalProfile_subset_box logQ hb hN hw)
    (isCompact_supportBox k r N width b).isClosed

/-- Compact support is derived from the original product wall and the
positive physical floor. The interval may be empty; no artificial
nonemptiness or lower bound on either old/tail rank is imposed. -/
theorem hasCompactSupport_physicalProfile {k r : ℕ} (logQ : ℝ) {N width b : ℝ}
    (hb : 0 < b) (hN : 0 < N) (hw : 0 < width) :
    HasCompactSupport (physicalProfile (k := k) (r := r) logQ N width b) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_supportBox k r N width b)
    (support_physicalProfile_subset_box logQ hb hN hw)

end
end ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension
