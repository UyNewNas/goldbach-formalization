import ImbalancedChen.Part3CommonPoisson
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / PROPOSED MODULE:
  ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
Only this ONE new module candidate is assembled. Every import already exists.
Source24674ef8 L34-L67 and L318-L670 are copied byte-for-byte below.
The main/physical namespace and section wrappers are explicitly closed.
The affine progression Poisson/summability proofs are REUSED from actual
Part3CommonPoisson, not copied and not supplied as target-shaped hypotheses.
No M1/M2, six-cover, tail, Ramanujan, count, spectral or actual integral
prefix is copied or imported. No source-bound private name crosses files.
Mathematical declaration types/bodies in the two selected segments are unchanged.
ROOT alone controls later actual installation and the compilation queue.
-/
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail
open Classical
open scoped BigOperators SchwartzMap FourierTransform
open CommonSmoothCutoff

/-- The inverse residue used by the complete Kloosterman sum. -/
def inverseResidue (c : ℕ) (u : ℤ) : ℤ :=
  (((u : ZMod c)⁻¹).val : ℤ)

/-- Complete Kloosterman sum with the positive linear-frequency sign.
The unit condition is retained inside the complete residue sum. -/
def kloosterman (c : ℕ) (m n : ℤ) : ℂ :=
  ∑ u ∈ Finset.range c,
    if Nat.Coprime u c then
      fourier 1 (((m * (u : ℤ) + n * inverseResidue c u : ℤ) : ℝ) /
        (c : ℝ) : UnitAddCircle)
    else 0

theorem kloosterman_norm_le (c : ℕ) (m n : ℤ) :
    ‖kloosterman c m n‖ ≤ (c : ℝ) := by
  unfold kloosterman
  calc
    _ ≤ ∑ u ∈ Finset.range c,
        ‖if Nat.Coprime u c then
          fourier 1 (((m * (u : ℤ) + n * inverseResidue c u : ℤ) : ℝ) /
            (c : ℝ) : UnitAddCircle) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ Finset.range c, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      split_ifs <;> simp only [fourier_apply, Circle.norm_coe, norm_zero,
        le_refl, zero_le_one]
    _ = _ := by simp

/-- Exactly the original completed nonzero-frequency summand, including
the inverse(z) frequency and all complex phases. -/
def frequency (B : ℝ) (c : ℕ) (a y z m : ℤ) : ℂ :=
  (B / (c : ℝ)) •
      (𝓕 dyadicCutoffSchwartz) ((B / (c : ℝ)) * (m : ℝ)) *
    kloosterman c (m * inverseResidue c z) (a * y)

end ImbalancedChen.Part3.OriginalSmoothPoissonTail

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

noncomputable section

open Classical
open scoped BigOperators SchwartzMap FourierTransform
open CommonSmoothCutoff

variable {c : ℕ} [NeZero c]

private theorem inverseResidue_cast (u : ℤ) :
    (inverseResidue c u : ZMod c) = (u : ZMod c)⁻¹ := by
  simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem stdAddChar_int_fourier (k : ℤ) :
    ZMod.stdAddChar (k : ZMod c) =
      fourier 1 (((k : ℝ) / (c : ℝ)) : UnitAddCircle) := by
  rw [ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

private theorem fourier_residue (m : ℤ) (u : ZMod c) :
    fourier m (((u.val : ℝ) / (c : ℝ)) : UnitAddCircle) =
      ZMod.stdAddChar ((m : ZMod c) * u) := by
  have hu : ((m * (u.val : ℤ) : ℤ) : ZMod c) = (m : ZMod c) * u := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hu, ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Complete residues are exactly the least natural representatives. -/
private theorem sum_zmod_eq_range (f : ZMod c → ℂ) :
    (∑ u : ZMod c, f u) = ∑ n ∈ Finset.range c, f (n : ZMod c) := by
  apply Finset.sum_bij (fun u _ ↦ u.val)
  · intro u hu
    exact Finset.mem_range.mpr u.val_lt
  · intro u hu v hv he
    have h := congrArg (fun n : ℕ ↦ (n : ZMod c)) he
    simpa only [ZMod.natCast_zmod_val] using h
  · intro n hn
    refine ⟨(n : ZMod c), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro u hu
    simp only [ZMod.natCast_zmod_val]

/-- Dictionary with the earlier literal range-c complete sum, including
the original unit filter and positive linear-frequency sign. -/
theorem kloosterman_eq_zmod (m n : ℤ) :
    kloosterman c m n = ∑ u : ZMod c,
      if IsUnit u then
        ZMod.stdAddChar ((m : ZMod c) * u + (n : ZMod c) * u⁻¹)
      else 0 := by
  rw [sum_zmod_eq_range]
  unfold kloosterman
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [ZMod.isUnit_iff_coprime]
  by_cases hc : Nat.Coprime u c
  · simp only [if_pos hc]
    rw [← stdAddChar_int_fourier]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, inverseResidue_cast]
  · simp only [if_neg hc]

/-- The unit gate belongs to b, while the inverse is that of b*z.  For
unit z these are exactly the original physical admissibility conditions. -/
def residuePhase (a y z : ℤ) (u : ZMod c) : ℂ :=
  if IsUnit u then
    ZMod.stdAddChar (((a * y : ℤ) : ZMod c) * (u * (z : ZMod c))⁻¹)
  else 0

theorem residuePhase_nat (a y z : ℤ) (b : ℕ) :
    residuePhase a y z (b : ZMod c) =
      if Nat.Coprime b c then
        ZMod.stdAddChar (((a * y : ℤ) : ZMod c) *
          ((b : ZMod c) * (z : ZMod c))⁻¹)
      else 0 := by
  simp only [residuePhase, ZMod.isUnit_iff_coprime]

omit [NeZero c] in
theorem isUnit_intCast_iff_natAbs_coprime (b : ℤ) :
    IsUnit (b : ZMod c) ↔ Nat.Coprime b.natAbs c := by
  cases b with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] using
        ZMod.isUnit_iff_coprime n c
  | negSucc n =>
      rw [Int.cast_negSucc, IsUnit.neg_iff, Int.natAbs_negSucc]
      exact ZMod.isUnit_iff_coprime (n + 1) c

omit [NeZero c] in
theorem physical_inverse_isUnit (b z : ℤ)
    (hb : Nat.Coprime b.natAbs c) (hz : Nat.Coprime z.natAbs c) :
    IsUnit ((b * z : ℤ) : ZMod c) := by
  rw [Int.cast_mul]
  exact ((isUnit_intCast_iff_natAbs_coprime (c := c) b).mpr hb).mul
    ((isUnit_intCast_iff_natAbs_coprime (c := c) z).mpr hz)

/-- Literal original e(a*y*inverse(b*z)/c) on the unit b classes. -/
theorem residuePhase_integer_fourier (a y z b : ℤ) :
    residuePhase a y z (b : ZMod c) =
      if Nat.Coprime b.natAbs c then
        fourier 1 (((a * y * inverseResidue c (b * z) : ℤ) : ℝ) /
          (c : ℝ) : UnitAddCircle)
      else 0 := by
  unfold residuePhase
  simp_rw [isUnit_intCast_iff_natAbs_coprime (c := c) b]
  by_cases hb : Nat.Coprime b.natAbs c
  · simp only [if_pos hb]
    rw [← stdAddChar_int_fourier]
    congr 1
    simp only [Int.cast_mul, inverseResidue_cast]
  · simp only [if_neg hb]

/-- Exact finite change of variables v=b*z.  Since z is a unit, the
map is bijective on ALL residues.  No masks or frequencies are deleted. -/
theorem residue_frequency_eq_kloosterman (a y z m : ℤ)
    (hz : IsUnit (z : ZMod c)) :
    (∑ u : ZMod c, residuePhase a y z u *
      ZMod.stdAddChar ((m : ZMod c) * u)) =
      kloosterman c (m * inverseResidue c z) (a * y) := by
  rw [kloosterman_eq_zmod]
  let g : ZMod c → ℂ := fun v ↦
    if IsUnit v then
      ZMod.stdAddChar ((((m * inverseResidue c z : ℤ) : ZMod c) * v) +
        ((a * y : ℤ) : ZMod c) * v⁻¹)
    else 0
  change (∑ u : ZMod c, residuePhase a y z u *
    ZMod.stdAddChar ((m : ZMod c) * u)) = ∑ v : ZMod c, g v
  apply Fintype.sum_bijective (fun u : ZMod c ↦ u * (z : ZMod c))
    ((IsUnit.isUnit_iff_mulRight_bijective (a := (z : ZMod c))).mp hz)
  intro u
  have hgate : IsUnit (u * (z : ZMod c)) ↔ IsUnit u := by
    constructor
    · intro h
      exact isUnit_of_mul_isUnit_left h
    · intro h
      exact h.mul hz
  have hlinear : (((m * inverseResidue c z : ℤ) : ZMod c) *
      (u * (z : ZMod c))) = (m : ZMod c) * u := by
    rw [Int.cast_mul, inverseResidue_cast]
    calc
      _ = ((m : ZMod c) * u) * ((z : ZMod c)⁻¹ * (z : ZMod c)) := by ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hz, mul_one]
  by_cases hu : IsUnit u
  · have huz := hgate.mpr hu
    simp only [residuePhase, if_pos hu, g, if_pos huz, hlinear,
      AddChar.map_add_eq_mul]
    ring
  · have huz : ¬ IsUnit (u * (z : ZMod c)) := fun h ↦ hu (hgate.mp h)
    simp only [residuePhase, if_neg hu, zero_mul, g, if_neg huz]

/-- Actual physical finite natural sum.  The positive compact support
below identifies it with the full integer-b sum. -/
def finiteKernel (B : ℝ) (S : Finset ℕ) (a y z : ℤ) : ℂ :=
  ∑ b ∈ S, (scaledDyadicCutoff B b : ℂ) * residuePhase a y z (b : ZMod c)

def integerKernel (B : ℝ) (a y z : ℤ) : ℂ :=
  ∑' b : ℤ, (scaledDyadicCutoff B (b : ℝ) : ℂ) *
    residuePhase a y z (b : ZMod c)

theorem integerKernel_eq_original (B : ℝ) (a y z : ℤ) :
    integerKernel (c := c) B a y z =
      ∑' b : ℤ, if Nat.Coprime b.natAbs c then
        (scaledDyadicCutoff B (b : ℝ) : ℂ) *
          fourier 1 (((a * y * inverseResidue c (b * z) : ℤ) : ℝ) /
            (c : ℝ) : UnitAddCircle)
      else 0 := by
  unfold integerKernel
  apply tsum_congr
  intro b
  rw [residuePhase_integer_fourier]
  split_ifs <;> simp only [mul_zero]

def naturalSupport (B : ℝ) : Finset ℕ := Finset.Icc 0 (Nat.ceil (3 * B))

theorem mem_naturalSupport {B : ℝ} (hB : 0 < B) (b : ℕ)
    (hb : scaledDyadicCutoff B b ≠ 0) : b ∈ naturalSupport B := by
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.zero_le _, ?_⟩
  have hu := (scaledDyadicCutoff_mem_Icc_of_ne_zero hB hb).2
  exact_mod_cast hu.trans (Nat.le_ceil (3 * B))

private theorem class_iff (b : ℕ) (u : ZMod c) :
    Int.ModEq c (b : ℤ) (u.val : ℤ) ↔ (b : ZMod c) = u := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    (ZMod.intCast_eq_intCast_iff (b : ℤ) (u.val : ℤ) c).symm

/-- Finite partition into every residue class, without replacing a signed
sum by a majorant or enlarging its arithmetic support. -/
theorem finiteKernel_eq_residues (B : ℝ) (S : Finset ℕ) (a y z : ℤ) :
    finiteKernel (c := c) B S a y z = ∑ u : ZMod c, residuePhase a y z u *
      (∑ b ∈ S, if Int.ModEq c (b : ℤ) (u.val : ℤ)
        then (scaledDyadicCutoff B b : ℂ) else 0) := by
  symm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold finiteKernel
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [class_iff]
  rw [Finset.sum_eq_single (b : ZMod c)]
  · simp only [if_true]
    exact mul_comm _ _
  · intro u hu hne
    have hn : (b : ZMod c) ≠ u := Ne.symm hne
    simp only [if_neg hn, mul_zero]
  · simp

/-- The actual integer-b source equals the finite natural compact-support
source.  This proof uses a support bijection, not an assumed periodicity
or a convergence convention for an unsigned divergent sum. -/
theorem finiteKernel_eq_integerKernel {B : ℝ} (hB : 0 < B) (S : Finset ℕ)
    (hS : ∀ b : ℕ, scaledDyadicCutoff B b ≠ 0 → b ∈ S) (a y z : ℤ) :
    finiteKernel (c := c) B S a y z = integerKernel (c := c) B a y z := by
  let f : ℕ → ℂ := fun b ↦ (scaledDyadicCutoff B b : ℂ) *
    residuePhase a y z (b : ZMod c)
  let g : ℤ → ℂ := fun b ↦ (scaledDyadicCutoff B (b : ℝ) : ℂ) *
    residuePhase a y z (b : ZMod c)
  have hnonneg (b : Function.support g) : 0 ≤ b.val := by
    have hp : scaledDyadicCutoff B (b.val : ℝ) ≠ 0 := by
      intro hp
      exact b.property (by simp only [g, hp, Complex.ofReal_zero, zero_mul])
    have hh := (scaledDyadicCutoff_mem_Icc_of_ne_zero hB hp).1
    have hhR : (0 : ℝ) ≤ (b.val : ℝ) := by linarith
    exact_mod_cast hhR
  let i : Function.support g → ℕ := fun b ↦ b.val.toNat
  have hcast (b : Function.support g) : (i b : ℤ) = b.val :=
    Int.toNat_of_nonneg (hnonneg b)
  have hi : Function.Injective i := by
    intro b b' he
    have he' := congrArg (fun n : ℕ ↦ (n : ℤ)) he
    rw [hcast, hcast] at he'
    exact Subtype.ext he'
  have hf : Function.support f ⊆ Set.range i := by
    intro b hb
    have hg : (b : ℤ) ∈ Function.support g := by
      simpa only [Function.mem_support, f, g, Int.cast_natCast] using hb
    refine ⟨⟨(b : ℤ), hg⟩, ?_⟩
    simp only [i, Int.toNat_natCast]
  have hfg (b : Function.support g) : f (i b) = g b.val := by
    have hr : (i b : ℝ) = (b.val : ℝ) := by exact_mod_cast hcast b
    have hc : (i b : ZMod c) = (b.val : ZMod c) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun k : ℤ ↦ (k : ZMod c)) (hcast b)
    simp only [f, g, hr, hc]
  calc
    _ = ∑' b : ℕ, f b := by
      symm
      apply tsum_eq_sum
      intro b hb
      have hp : scaledDyadicCutoff B b = 0 := by
        by_contra hp
        exact hb (hS b hp)
      simp only [f, hp, Complex.ofReal_zero, zero_mul]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

private def residueFrequency (B : ℝ) (a y z : ℤ) (u : ZMod c) (m : ℤ) : ℂ :=
  residuePhase a y z u *
    ((B / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) ((B / (c : ℝ)) * (m : ℝ)) *
      fourier m (((u.val : ℝ) / (c : ℝ)) : UnitAddCircle))

private theorem residueFrequency_summable_norm {B : ℝ} (hB : 0 < B)
    (a y z : ℤ) (u : ZMod c) :
    Summable (fun m : ℤ ↦ ‖residueFrequency B a y z u m‖) := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have ht : 0 < B / (c : ℝ) := div_pos hB hc
  have h := (poissonFrequency_summable_norm ht ((u.val : ℝ) / (c : ℝ))).mul_left
    ‖residuePhase a y z u‖
  simpa only [residueFrequency, norm_mul] using h

private theorem frequency_eq_residue_sum (B : ℝ) (a y z m : ℤ)
    (hz : IsUnit (z : ZMod c)) :
    frequency B c a y z m = ∑ u : ZMod c, residueFrequency B a y z u m := by
  unfold residueFrequency
  simp_rw [fourier_residue]
  calc
    _ = ((B / (c : ℝ)) •
        (𝓕 dyadicCutoffSchwartz) ((B / (c : ℝ)) * (m : ℝ))) *
          (∑ u : ZMod c, residuePhase a y z u *
            ZMod.stdAddChar ((m : ZMod c) * u)) := by
      rw [residue_frequency_eq_kloosterman a y z m hz]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Absolute convergence of the full completed Kloosterman series is
proved before the finite-residue/tsum interchange is used. -/
theorem completed_summable_norm {B : ℝ} (hB : 0 < B) (a y z : ℤ)
    (hz : IsUnit (z : ZMod c)) :
    Summable (fun m : ℤ ↦ ‖frequency B c a y z m‖) := by
  have hmajor : Summable (fun m : ℤ ↦ ∑ u : ZMod c,
      ‖residueFrequency B a y z u m‖) :=
    summable_sum (fun u hu ↦ residueFrequency_summable_norm hB a y z u)
  apply hmajor.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro m
  rw [frequency_eq_residue_sum B a y z m hz]
  exact norm_sum_le _ _

/-- Exact physical finite smooth-b Poisson identity.  The plus m sign
comes directly from the owned affine Poisson formula; multiplying all
residue classes by z gives S(m*inv(z),a*y;c). -/
theorem finiteKernel_poisson {B : ℝ} (hB : 0 < B) (S : Finset ℕ)
    (hS : ∀ b : ℕ, scaledDyadicCutoff B b ≠ 0 → b ∈ S)
    (a y z : ℤ) (hz : IsUnit (z : ZMod c)) :
    finiteKernel (c := c) B S a y z = ∑' m : ℤ, frequency B c a y z m := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hrow (u : ZMod c) :
      residuePhase a y z u *
        (∑ b ∈ S, if Int.ModEq c (b : ℤ) (u.val : ℤ)
          then (scaledDyadicCutoff B b : ℂ) else 0) =
        ∑' m : ℤ, residueFrequency B a y z u m := by
    rw [scaledDyadicCutoff_finset_progression_eq_tsum hB S hS (NeZero.pos c)]
    rw [scaledDyadicCutoff_poisson_rescaled hB hc]
    simp only [residueFrequency, Int.cast_natCast, tsum_mul_left]
  have hs (u : ZMod c) : Summable (residueFrequency B a y z u) :=
    (residueFrequency_summable_norm hB a y z u).of_norm
  calc
    _ = ∑ u : ZMod c, residuePhase a y z u *
        (∑ b ∈ S, if Int.ModEq c (b : ℤ) (u.val : ℤ)
          then (scaledDyadicCutoff B b : ℂ) else 0) := finiteKernel_eq_residues (c := c) B S a y z
    _ = ∑ u : ZMod c, ∑' m : ℤ, residueFrequency B a y z u m :=
      Finset.sum_congr rfl (fun u hu ↦ hrow u)
    _ = ∑' m : ℤ, ∑ u : ZMod c, residueFrequency B a y z u m :=
      (Summable.tsum_finsetSum (fun u hu ↦ hs u)).symm
    _ = _ := tsum_congr (fun m ↦ (frequency_eq_residue_sum B a y z m hz).symm)

/-- The actual complete integer-b source, not a free completed-kernel
adapter.  Every negative b has zero cutoff by its proved positive support. -/
theorem integerKernel_poisson {B : ℝ} (hB : 0 < B) (a y z : ℤ)
    (hz : IsUnit (z : ZMod c)) :
    integerKernel (c := c) B a y z = ∑' m : ℤ, frequency B c a y z m := by
  rw [← finiteKernel_eq_integerKernel (c := c) hB (naturalSupport B)
    (mem_naturalSupport hB) a y z]
  exact finiteKernel_poisson (c := c) hB (naturalSupport B) (mem_naturalSupport hB) a y z hz

/-- The literal original physical smooth-b Poisson formula.  Both sums
run through all integers.  The completed frequency has the PLUS sign. -/
theorem original_physical_poisson {B : ℝ} (hB : 0 < B) (a y z : ℤ)
    (hz : Nat.Coprime z.natAbs c) :
    (∑' b : ℤ, if Nat.Coprime b.natAbs c then
      (scaledDyadicCutoff B (b : ℝ) : ℂ) *
        fourier 1 (((a * y * inverseResidue c (b * z) : ℤ) : ℝ) /
          (c : ℝ) : UnitAddCircle)
      else 0) =
    ∑' m : ℤ, (B / (c : ℝ)) •
        (𝓕 dyadicCutoffSchwartz) ((B / (c : ℝ)) * (m : ℝ)) *
      kloosterman c (m * inverseResidue c z) (a * y) := by
  rw [← integerKernel_eq_original (c := c) B a y z]
  exact integerKernel_poisson (c := c) hB a y z
    ((isUnit_intCast_iff_natAbs_coprime (c := c) z).mpr hz)

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

end
