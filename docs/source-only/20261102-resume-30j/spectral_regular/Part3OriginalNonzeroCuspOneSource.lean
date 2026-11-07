import ImbalancedChen.Part3CuspKloostermanMatrix
import ImbalancedChen.Part3ActualCuspWidthNormalization
import ImbalancedChen.Part3InfinityZeroArithmetic
import ImbalancedChen.Part3ActualZeroPoissonKernel
import Mathlib.Tactic

/-!
Source-only candidate, uncompiled, zero formal credit.

The original physical completed frequency is converted to a sum of
literal Gamma0(z) infinity/cusp-one matrix phases.  The matrix has
normalized positive lower-left entry sqrt(z)*c.  Reversing the old-chart
phase contributes exactly e(-a*y/z), before any ABL operation.  The
original c-unit gate, signed m,y, smooth cutoff and all nonzero m remain.

This is an arithmetic source dictionary, not a trace formula.  In
particular, no radial KL measure is called an automorphic spectral measure.
-/

namespace ImbalancedChen.Part3.OriginalNonzeroCuspOneSource20261102
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Matrix Matrix.SpecialLinearGroup MatrixGroups
open CuspKloostermanMatrixSourceOnly
open Gamma0ActualCuspsSourceOnly ActualCuspWidthNormalizationSourceOnly
open InfinityZeroArithmetic20261025a
open OriginalSmoothPoissonTail OriginalSmoothPoissonTail.Physical
open ActualZeroPoissonKernel20261102 CommonSmoothCutoff
open P3Period64NativeReconstructionSourceOnly (e e_add norm_e)
open scoped BigOperators SchwartzMap FourierTransform

/-- The physical residue carrier; no residue is removed or duplicated. -/
abbrev PhysicalUnit (c : ℕ) := {u : ZMod c // IsUnit u}

def physicalAlpha (z c : ℕ) (u : ZMod c) : ℤ :=
  ((((z : ZMod c)⁻¹ * u).val : ℕ) : ℤ)

def physicalK (c : ℕ) (u : ZMod c) : ℤ := -((u⁻¹).val : ℤ)

theorem physicalAlpha_cast (z c : ℕ) [NeZero c] (u : ZMod c) :
    (physicalAlpha z c u : ZMod c) = (z : ZMod c)⁻¹ * u := by
  simp only [physicalAlpha, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem physicalK_cast (c : ℕ) [NeZero c] (u : ZMod c) :
    (physicalK c u : ZMod c) = -u⁻¹ := by
  simp only [physicalK, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem physical_bezout_exists (z c : ℕ) [NeZero c]
    (hzc : z.Coprime c) (u : PhysicalUnit c) :
    ∃ a : ℤ, a * (c : ℤ) - (z : ℤ) * physicalK c u.1 *
      physicalAlpha z c u.1 = 1 := by
  have hz : IsUnit (z : ZMod c) := (ZMod.isUnit_iff_coprime z c).mpr hzc
  have hp : (z : ZMod c) * (physicalK c u.1 : ZMod c) *
      (physicalAlpha z c u.1 : ZMod c) = -1 := by
    rw [physicalK_cast, physicalAlpha_cast]
    calc
      (z : ZMod c) * -u.1⁻¹ * ((z : ZMod c)⁻¹ * u.1) =
          -(((z : ZMod c) * (z : ZMod c)⁻¹) * (u.1⁻¹ * u.1)) := by ring
      _ = -1 := by
        rw [ZMod.mul_inv_of_unit _ hz, ZMod.inv_mul_of_unit _ u.2]
        simp
  have hd : (c : ℤ) ∣ 1 + (z : ℤ) * physicalK c u.1 * physicalAlpha z c u.1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp
    push_cast
    rw [hp]
    ring
  obtain ⟨a, ha⟩ := hd
  refine ⟨a, ?_⟩
  nlinarith [ha]

def physicalA (z c : ℕ) [NeZero c] (hzc : z.Coprime c)
    (u : PhysicalUnit c) : ℤ := Classical.choose (physical_bezout_exists z c hzc u)

theorem physical_bezout (z c : ℕ) [NeZero c] (hzc : z.Coprime c)
    (u : PhysicalUnit c) :
    physicalA z c hzc u * (c : ℤ) - (z : ℤ) * physicalK c u.1 *
      physicalAlpha z c u.1 = 1 := Classical.choose_spec (physical_bezout_exists z c hzc u)

/-- A genuine integral determinant-one matrix, not a stipulated cusp sum. -/
def physicalRepresentative (z c : ℕ) [NeZero c] (hzc : z.Coprime c)
    (u : PhysicalUnit c) : SL(2, ℤ) :=
  matrixOfCuspParameters z c (physicalK c u.1) (physicalAlpha z c u.1)
    (physicalA z c hzc u) (physical_bezout z c hzc u)

theorem physicalRepresentative_mem_gamma0 (z c : ℕ) [NeZero c]
    (hzc : z.Coprime c) (u : PhysicalUnit c) :
    physicalRepresentative z c hzc u ∈ CongruenceSubgroup.Gamma0 z :=
  matrixOfCuspParameters_mem_gamma0 _ _ _ _ _ _

theorem physicalRepresentative_rows (z c : ℕ) [NeZero c]
    (hzc : z.Coprime c) (u : PhysicalUnit c) :
    physicalRepresentative z c hzc u 1 0 + physicalRepresentative z c hzc u 1 1 = c ∧
      physicalRepresentative z c hzc u 0 0 + physicalRepresentative z c hzc u 0 1 =
        physicalAlpha z c u.1 := matrixOfCuspParameters_rows _ _ _ _ _ _

theorem physicalRepresentative_positive_modulus (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (u : PhysicalUnit c) :
    oldCuspProduct z (physicalRepresentative z c hzc u) 1 0 =
      Real.sqrt (z : ℝ) * (c : ℝ) ∧
      0 < oldCuspProduct z (physicalRepresentative z c hzc u) 1 0 := by
  have hr := (physicalRepresentative_rows z c hzc u).1
  have hrR : (physicalRepresentative z c hzc u 1 0 : ℝ) +
      (physicalRepresentative z c hzc u 1 1 : ℝ) = (c : ℝ) := by exact_mod_cast hr
  have hc : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  rw [(oldCuspProduct_entries z (physicalRepresentative z c hzc u)).2.1, hrR]
  exact ⟨rfl, mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hz)) hc⟩

/-- Conjugating the actual cusp-zero stabilizer by the integral T gives
the actual cusp-one stabilizer.  Its width remains exactly z. -/
def oneParabolic (z : ℕ) (v : ℤ) : SL(2, ℤ) :=
  ModularGroup.T * zeroParabolic z v * ModularGroup.T⁻¹

theorem oneParabolic_eq_actual_width (z : ℕ) (v : ℤ) :
    oneParabolic z v = cuspOneMatrix * ModularGroup.T ^ ((z : ℤ)*v) *
      cuspOneMatrix⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneParabolic, zeroParabolic, cuspOneMatrix, ModularGroup.coe_T,
      ModularGroup.coe_T_zpow, SL2_inv_expl, coe_mul, Matrix.mul_fin_two] <;> ring

theorem oneParabolic_mem_gamma0 (z : ℕ) (hz : 0 < z) (v : ℤ) :
    oneParabolic z v ∈ CongruenceSubgroup.Gamma0 z := by
  rw [oneParabolic_eq_actual_width]
  exact normalized_period_integral_mem_gamma0 z hz v

def oneTranslateBoth (z : ℕ) (u v : ℤ) (g : SL(2, ℤ)) : SL(2, ℤ) :=
  ModularGroup.T ^ u * g * oneParabolic z v

theorem oneTranslateBoth_mul_T (z : ℕ) (u v : ℤ) (g : SL(2, ℤ)) :
    oneTranslateBoth z u v g * ModularGroup.T =
      zeroTranslateBoth z u v (g * ModularGroup.T) := by
  unfold oneTranslateBoth oneParabolic zeroTranslateBoth
  group

private theorem right_T_bottom (g : SL(2, ℤ)) :
    (g * ModularGroup.T) 1 0 = g 1 0 ∧
      (g * ModularGroup.T) 1 1 = g 1 0 + g 1 1 := by
  simp [coe_mul, Matrix.mul_fin_two, ModularGroup.coe_T]

theorem one_double_coset_iff (z : ℕ) (hz : 0 < z) (g h : SL(2, ℤ))
    (k l : ℤ) (hg : g 1 0 = (z : ℤ) * k) (hh : h 1 0 = (z : ℤ) * l) :
    (∃ u v : ℤ, h = oneTranslateBoth z u v g) ↔
      h 1 0 + h 1 1 = g 1 0 + g 1 1 ∧ (g 1 0 + g 1 1) ∣ l - k := by
  have hd := zero_double_coset_iff z hz (g * ModularGroup.T) (h * ModularGroup.T)
    k l ((right_T_bottom g).1.trans hg) ((right_T_bottom h).1.trans hh)
  rw [(right_T_bottom g).2, (right_T_bottom h).2] at hd
  constructor
  · rintro ⟨u,v,rfl⟩
    apply hd.mp
    exact ⟨u,v,oneTranslateBoth_mul_T z u v g⟩
  · intro hc
    obtain ⟨u,v,huv⟩ := hd.mpr hc
    refine ⟨u,v,?_⟩
    exact mul_right_cancel (huv.trans (oneTranslateBoth_mul_T z u v g).symm)

/-- Every actual positive-modulus Gamma0 matrix occurs in the double
orbit of a constructed physical-unit representative.  Thus this is not
an arbitrary subfamily of normalized cusp-one phases. -/
theorem physicalRepresentative_surjective_double_cosets (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 z) (hc : g 1 0 + g 1 1 = (c : ℤ)) :
    ∃ r : PhysicalUnit c, ∃ u v : ℤ, physicalRepresentative z c hzc r =
      oneTranslateBoth z u v g := by
  obtain ⟨k,hk,hbez⟩ := cusp_parameters_bezout z g hg
  let u : ZMod c := (z : ZMod c) * ((g 0 0 + g 0 1 : ℤ) : ZMod c)
  have hprod : u * (-(k : ZMod c)) = 1 := by
    have hb := congrArg (fun a : ℤ => (a : ZMod c)) hbez
    rw [hc] at hb
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      Int.cast_one, mul_zero, zero_sub] at hb
    change (z : ZMod c) * ((g 0 0 + g 0 1 : ℤ) : ZMod c) * -(k : ZMod c) = 1
    convert hb using 1 <;> ring
  have hu : IsUnit u := isUnit_iff_exists_inv.mpr ⟨-(k : ZMod c), hprod⟩
  let r : PhysicalUnit c := ⟨u,hu⟩
  have hinv : u⁻¹ = -(k : ZMod c) := by
    calc
      u⁻¹ = u⁻¹ * (u * -(k : ZMod c)) := by rw [hprod, mul_one]
      _ = (u⁻¹ * u) * -(k : ZMod c) := by ring
      _ = -(k : ZMod c) := by rw [ZMod.inv_mul_of_unit _ hu, one_mul]
  have hdiv : (c : ℤ) ∣ physicalK c r.1 - k := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp
    simp only [Int.cast_sub, physicalK_cast]
    change -u⁻¹ - (k : ZMod c) = 0
    rw [hinv]
    ring
  refine ⟨r, (one_double_coset_iff z hz g (physicalRepresentative z c hzc r)
    k (physicalK c r.1) hk rfl).mpr ?_⟩
  exact ⟨(physicalRepresentative_rows z c hzc r).1.trans hc.symm, by simpa only [hc] using hdiv⟩

theorem physicalRepresentative_injective_double_cosets (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (r s : PhysicalUnit c)
    (horbit : ∃ u v : ℤ, physicalRepresentative z c hzc s =
      oneTranslateBoth z u v (physicalRepresentative z c hzc r)) : r = s := by
  have hd := ((one_double_coset_iff z hz (physicalRepresentative z c hzc r)
    (physicalRepresentative z c hzc s) (physicalK c r.1) (physicalK c s.1)
      rfl rfl).mp horbit).2
  rw [(physicalRepresentative_rows z c hzc r).1] at hd
  have heq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mpr hd
  simp only [Int.cast_sub, physicalK_cast] at heq
  have hi : r.1⁻¹ = s.1⁻¹ := by linear_combination heq
  apply Subtype.ext
  calc
    r.1 = (s.1 * s.1⁻¹) * r.1 := by rw [ZMod.mul_inv_of_unit _ s.2, one_mul]
    _ = s.1 * (r.1⁻¹ * r.1) := by rw [hi]; ring
    _ = s.1 := by rw [ZMod.inv_mul_of_unit _ r.2, mul_one]

def newMatrixPhase (z c : ℕ) [NeZero c] (hzc : z.Coprime c)
    (m n : ℤ) (u : PhysicalUnit c) : ℂ :=
  e ((m : ℝ) * (newCuspProduct z (physicalRepresentative z c hzc u) 0 0 /
        newCuspProduct z (physicalRepresentative z c hzc u) 1 0) +
     (n : ℝ) * (newCuspProduct z (physicalRepresentative z c hzc u) 1 1 /
        newCuspProduct z (physicalRepresentative z c hzc u) 1 0))

def oldMatrixPhase (z c : ℕ) [NeZero c] (hzc : z.Coprime c)
    (m n : ℤ) (u : PhysicalUnit c) : ℂ :=
  e ((m : ℝ) * (oldCuspProduct z (physicalRepresentative z c hzc u) 0 0 /
        oldCuspProduct z (physicalRepresentative z c hzc u) 1 0) +
     (n : ℝ) * (oldCuspProduct z (physicalRepresentative z c hzc u) 1 1 /
        oldCuspProduct z (physicalRepresentative z c hzc u) 1 0))

private theorem e_int_div (c : ℕ) [NeZero c] (k : ℤ) :
    e ((k : ℝ) / (c : ℝ)) = ZMod.stdAddChar (k : ZMod c) := by
  rw [ZMod.stdAddChar_coe]
  simp only [e]
  push_cast
  congr 1
  ring

theorem newMatrixPhase_eq_physical (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (m n : ℤ) (u : PhysicalUnit c) :
    newMatrixPhase z c hzc m n u =
      ZMod.stdAddChar (((m * inverseResidue c z : ℤ) : ZMod c) * u.1 +
        (n : ZMod c) * u.1⁻¹) := by
  have hr := physicalRepresentative_rows z c hzc u
  have ht : physicalRepresentative z c hzc u 1 0 +
      physicalRepresentative z c hzc u 1 1 ≠ 0 := by
    rw [hr.1]
    exact_mod_cast NeZero.ne c
  have hcoords := new_normalized_coordinates z hz (physicalRepresentative z c hzc u)
    (physicalK c u.1) rfl ht
  unfold newMatrixPhase
  rw [hcoords.1, hcoords.2, hr.1, hr.2]
  have harg : (m : ℝ) * ((physicalAlpha z c u.1 : ℤ) : ℝ) / (c : ℝ) +
      (n : ℝ) * (-((physicalK c u.1 : ℤ) : ℝ) / (c : ℝ)) =
      (((m * physicalAlpha z c u.1 - n * physicalK c u.1 : ℤ) : ℝ) / (c : ℝ)) := by
    push_cast
    ring
  rw [← mul_div_assoc, harg, e_int_div]
  congr 1
  simp only [Int.cast_sub, Int.cast_mul, physicalAlpha_cast, physicalK_cast,
    inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
  ring

theorem oldMatrixPhase_eq_phase_mul_physical (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (m n : ℤ) (u : PhysicalUnit c) :
    oldMatrixPhase z c hzc m n u = e ((n : ℝ) / (z : ℝ)) *
      ZMod.stdAddChar (((m * inverseResidue c z : ℤ) : ZMod c) * u.1 +
        (n : ZMod c) * u.1⁻¹) := by
  have ht : physicalRepresentative z c hzc u 1 0 +
      physicalRepresentative z c hzc u 1 1 ≠ 0 := by
    rw [(physicalRepresentative_rows z c hzc u).1]
    exact_mod_cast NeZero.ne c
  change oldMatrixPhase z c hzc m n u = _
  rw [oldMatrixPhase, old_kloosterman_phase_eq_level_phase_mul_new z hz _ ht m n]
  change e ((n : ℝ) / (z : ℝ)) * newMatrixPhase z c hzc m n u = _
  rw [newMatrixPhase_eq_physical z c hz hzc m n u]

/-- Finite sum of the actual normalized cusp-one matrix phases. -/
def cuspOneMatrixSum (z c : ℕ) [NeZero c] (hzc : z.Coprime c) (m n : ℤ) : ℂ :=
  ∑ u : PhysicalUnit c, oldMatrixPhase z c hzc m n u

theorem cuspOneMatrixSum_eq_phase_mul_kloosterman (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (m n : ℤ) :
    cuspOneMatrixSum z c hzc m n =
      e ((n : ℝ) / (z : ℝ)) * kloosterman c (m * inverseResidue c z) n := by
  let f : ZMod c → ℂ := fun u =>
    ZMod.stdAddChar (((m * inverseResidue c z : ℤ) : ZMod c) * u + (n : ZMod c) * u⁻¹)
  have hsum : (∑ u : PhysicalUnit c, f u.1) =
      ∑ u ∈ (Finset.univ : Finset (ZMod c)).filter IsUnit, f u := by
    apply Finset.sum_bij (fun u _ => u.1)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩
    · intro u hu v hv huv
      exact Subtype.ext huv
    · intro u hu
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
    · intro u hu
      rfl
  unfold cuspOneMatrixSum
  simp_rw [oldMatrixPhase_eq_phase_mul_physical z c hz hzc m n]
  rw [← Finset.mul_sum]
  congr 1
  rw [kloosterman_eq_zmod]
  simpa only [Finset.sum_filter, f] using hsum

/-- The sign of the returned phase is fixed by actual matrix arithmetic. -/
theorem physical_kloosterman_eq_cuspOne (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (m n : ℤ) :
    kloosterman c (m * inverseResidue c z) n =
      e (-((n : ℝ) / (z : ℝ))) * cuspOneMatrixSum z c hzc m n := by
  rw [cuspOneMatrixSum_eq_phase_mul_kloosterman z c hz hzc m n, ← mul_assoc,
    ← e_add]
  simp only [neg_add_cancel, e, mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul]

/-- The actual frequency is the consumer; D/c and the Fourier argument
are kept verbatim, with no small-residue approximation. -/
theorem physical_frequency_eq_cuspOne (D : ℝ) (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (a y m : ℤ) :
    frequency D c a y z m =
      (D / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) ((D / (c : ℝ)) * (m : ℝ)) *
        (e (-(((a * y : ℤ) : ℝ) / (z : ℝ))) * cuspOneMatrixSum z c hzc m (a * y)) := by
  unfold frequency
  rw [physical_kloosterman_eq_cuspOne z c hz hzc m (a*y)]

theorem physical_frequency_norm_eq_cuspOne (D : ℝ) (z c : ℕ) [NeZero c]
    (hz : 0 < z) (hzc : z.Coprime c) (a y m : ℤ) :
    ‖frequency D c a y z m‖ = |D / (c : ℝ)| *
      ‖(𝓕 dyadicCutoffSchwartz) ((D / (c : ℝ)) * (m : ℝ))‖ *
        ‖cuspOneMatrixSum z c hzc m (a*y)‖ := by
  rw [physical_frequency_eq_cuspOne D z c hz hzc a y m]
  simp only [norm_mul, norm_smul, Real.norm_eq_abs, norm_e, one_mul]

def cuspOneFrequency (D : ℝ) (z c : ℕ) (a y m : ℤ) : ℂ :=
  if hc : 0 < c then
    letI : NeZero c := ⟨hc.ne'⟩
    if hzc : z.Coprime c then
      (D / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) ((D / (c : ℝ)) * (m : ℝ)) *
        (e (-(((a*y : ℤ) : ℝ) / (z : ℝ))) * cuspOneMatrixSum z c hzc m (a*y))
    else 0
  else 0

theorem cuspOneFrequency_eq_gated_physical (D : ℝ) (z c : ℕ)
    (hz : 0 < z) (hc : 0 < c) (a y m : ℤ) :
    cuspOneFrequency D z c a y m = if c.Coprime z then frequency D c a y z m else 0 := by
  letI : NeZero c := ⟨hc.ne'⟩
  by_cases hzc : z.Coprime c
  · simp only [cuspOneFrequency, dif_pos hc, dif_pos hzc, if_pos hzc.symm]
    exact (physical_frequency_eq_cuspOne D z c hz hzc a y m).symm
  · have hcz : ¬ c.Coprime z := fun h => hzc h.symm
    simp only [cuspOneFrequency, dif_pos hc, dif_neg hzc, if_neg hcz]

/-- Exact full nonzero-m I-source identity, without a truncation or
summability premise: the series is transformed term by term. -/
theorem original_nonzeroKernel_eq_cuspOne (C D : ℝ) (a y : ℤ)
    (z : ℕ) (hz : 0 < z) :
    nonzeroKernel C D a (z,y) =
      ∑ c ∈ smoothModuli C, (scaledDyadicCutoff C c : ℂ) *
        ∑' m : ℤ, if m = 0 then 0 else cuspOneFrequency D z c a y m := by
  unfold nonzeroKernel
  apply Finset.sum_congr rfl
  intro c hc
  have hcpos : 0 < c := (Finset.mem_Ioc.mp hc).1
  congr 1
  by_cases hcz : c.Coprime z
  · simp only [if_pos hcz]
    apply tsum_congr
    intro m
    rw [cuspOneFrequency_eq_gated_physical D z c hz hcpos a y m, if_pos hcz]
  · simp only [if_neg hcz]
    have heq : (fun m : ℤ => if m = 0 then 0 else cuspOneFrequency D z c a y m) =
        fun _ => 0 := by
      funext m
      rw [cuspOneFrequency_eq_gated_physical D z c hz hcpos a y m, if_neg hcz]
      split_ifs <;> rfl
    rw [heq, tsum_zero]

end
end ImbalancedChen.Part3.OriginalNonzeroCuspOneSource20261102
