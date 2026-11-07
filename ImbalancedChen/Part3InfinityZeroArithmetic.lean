import ImbalancedChen.Part3Gamma0ParabolicBottomRow
import ImbalancedChen.Part3CuspKloostermanMatrix
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual infinity-to-ZERO cusp arithmetic. The normalized scaling is
sigma0=[[0,-1/sqrt(N)],[sqrt(N),0]]. For gamma=[[a,b],[N*k,d]],
gamma*sigma0 has A/C=b/d and D/C=-k/d, with normalized positive
modulus sqrt(N)*d. This is distinct from the prior infinity-to-ONE
modulus c+d and its top-row sum. The actual cusp-zero right stabilizer,
double-orbit classification, canonical matrix representatives and finite
generalized Kloosterman sum are derived here from actual matrices.
No spectral, Kuznetsov, or desired-sum identity is a premise.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroArithmetic20261025a

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup BigOperators UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.CuspKloostermanMatrixSourceOnly (gammaReal)

/-- The width-normalized actual scaling matrix for cusp zero. -/
def zeroScaling (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -(1 / Real.sqrt (N : ℝ)); Real.sqrt (N : ℝ), 0]

theorem zeroScaling_det (N : ℕ) (hN : 0 < N) : Matrix.det (zeroScaling N) = 1 := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  simp [zeroScaling, Matrix.det_fin_two_of, hs]

def zeroSL (N : ℕ) (hN : 0 < N) : SL(2, ℝ) :=
  ⟨zeroScaling N, zeroScaling_det N hN⟩

theorem zeroSL_smul_infty (N : ℕ) (hN : 0 < N) :
    mapGL ℝ (zeroSL N hN) • (∞ : OnePoint ℝ) = (0 : ℝ) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  simp [smul_infty_eq_ite, zeroSL, zeroScaling, mapGL_coe_matrix, hs]

/-- The actual integral right parabolic at the normalized zero cusp. -/
def zeroParabolic (N : ℕ) (v : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; -(N : ℤ) * v, 1], by simp [Matrix.det_fin_two_of]⟩

theorem zeroParabolic_eq_conjugate (N : ℕ) (v : ℤ) :
    zeroParabolic N v = ModularGroup.S * ModularGroup.T ^ ((N : ℤ) * v) * ModularGroup.S⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroParabolic, ModularGroup.S, ModularGroup.coe_T_zpow,
      SL2_inv_expl, coe_mul, Matrix.mul_fin_two] <;> ring

/-- Integer stabilizer periods at cusp zero are EXACTLY the level multiples. -/
theorem zero_cusp_period_mem_iff (N : ℕ) (j : ℤ) :
    ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ j := by
  rw [gamma0_mem_iff_level_dvd_c]
  simp [ModularGroup.S, ModularGroup.coe_T_zpow, SL2_inv_expl,
    coe_mul, Matrix.mul_fin_two]

theorem zeroParabolic_mem_gamma0 (N : ℕ) (v : ℤ) :
    zeroParabolic N v ∈ CongruenceSubgroup.Gamma0 N := by
  rw [zeroParabolic_eq_conjugate, zero_cusp_period_mem_iff]
  exact ⟨v, rfl⟩

/-- This proves the actual positive integer width N, rather than merely
exhibiting one admissible period. -/
theorem zero_cusp_minimal_positive_period (N : ℕ) (hN : 0 < N)
    (j : ℤ) (hj : 0 < j)
    (hmem : ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈
      CongruenceSubgroup.Gamma0 N) : (N : ℤ) ≤ j := by
  exact Int.le_of_dvd hj ((zero_cusp_period_mem_iff N j).mp hmem)

/-- Normalized real unit translation is exactly the actual integral
zero-cusp translation with width N. -/
theorem zeroSL_conj_translation (N : ℕ) (hN : 0 < N) (v : ℤ) :
    zeroSL N hN * SpecialLinearGroup.map (Int.castRingHom ℝ) (ModularGroup.T ^ v) *
        (zeroSL N hN)⁻¹ =
      SpecialLinearGroup.map (Int.castRingHom ℝ) (zeroParabolic N v) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hsqr_v : Real.sqrt (N : ℝ) ^ 2 * (v : ℝ) = (N : ℝ) * (v : ℝ) :=
    congrArg (fun x : ℝ => x * (v : ℝ)) hsqr
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroSL, zeroScaling, zeroParabolic, SpecialLinearGroup.map,
      ModularGroup.coe_T_zpow, SL2_inv_expl, coe_mul, Matrix.mul_fin_two, hs] <;>
    field_simp [hs] <;> nlinarith [hsqr, hsqr_v]

def zeroCuspProduct (N : ℕ) (g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  gammaReal g * zeroScaling N

theorem zeroCuspProduct_entries (N : ℕ) (g : SL(2, ℤ)) :
    zeroCuspProduct N g 0 0 = Real.sqrt (N : ℝ) * (g 0 1 : ℝ) ∧
    zeroCuspProduct N g 1 0 = Real.sqrt (N : ℝ) * (g 1 1 : ℝ) ∧
    zeroCuspProduct N g 1 1 = -(g 1 0 : ℝ) / Real.sqrt (N : ℝ) := by
  simp [zeroCuspProduct, zeroScaling, gammaReal, Matrix.mul_fin_two] <;> ring

/-- The actual positive normalized lower-left modulus is sqrt(N)*d. -/
theorem zeroCuspProduct_positive_modulus (N : ℕ) (hN : 0 < N)
    (g : SL(2, ℤ)) (d : ℤ) (hd : g 1 1 = d) (hdpos : 0 < d) :
    zeroCuspProduct N g 1 0 = Real.sqrt (N : ℝ) * (d : ℝ) ∧
      0 < zeroCuspProduct N g 1 0 := by
  have hentry := (zeroCuspProduct_entries N g).2.1
  rw [hd] at hentry
  refine ⟨hentry, ?_⟩
  rw [hentry]
  exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (by exact_mod_cast hdpos)
/-- The true infinity-to-zero normalized coordinates, with the actual
level factor canceled using sqrt(N)^2=N. -/
theorem zero_normalized_coordinates (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ))
    (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 ≠ 0) :
    zeroCuspProduct N g 0 0 / zeroCuspProduct N g 1 0 =
      (g 0 1 : ℝ) / (g 1 1 : ℝ) ∧
    zeroCuspProduct N g 1 1 / zeroCuspProduct N g 1 0 =
      -(k : ℝ) / (g 1 1 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hdr : (g 1 1 : ℝ) ≠ 0 := by exact_mod_cast hd
  have hcr : (g 1 0 : ℝ) = (N : ℝ) * (k : ℝ) := by exact_mod_cast hc
  have hsqr_k : Real.sqrt (N : ℝ) ^ 2 * (k : ℝ) = (N : ℝ) * (k : ℝ) :=
    congrArg (fun x : ℝ => x * (k : ℝ)) hsqr
  obtain ⟨hA, hC, hD⟩ := zeroCuspProduct_entries N g
  constructor
  · rw [hA, hC]
    field_simp [hs, hdr]
  · rw [hD, hC, hcr]
    field_simp [hs, hdr]
    nlinarith [hsqr, hsqr_k]

/-- The determinant supplies the exact inverse congruence at denominator d. -/
theorem zero_denominator_inverse_congruence (N : ℕ) (g : SL(2, ℤ))
    (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) :
    g 1 1 ∣ (-(N : ℤ) * k) * g 0 1 - 1 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  rw [hc] at hdet
  refine ⟨-(g 0 0), ?_⟩
  nlinarith [hdet]

/-- The actual zero-cusp two-sided parabolic action. -/
def zeroTranslateBoth (N : ℕ) (u v : ℤ) (g : SL(2, ℤ)) : SL(2, ℤ) :=
  ModularGroup.T ^ u * g * zeroParabolic N v

theorem zeroTranslateBoth_lower (N : ℕ) (u v : ℤ) (g : SL(2, ℤ)) :
    zeroTranslateBoth N u v g 1 0 = g 1 0 - (N : ℤ) * v * g 1 1 ∧
    zeroTranslateBoth N u v g 1 1 = g 1 1 := by
  simp [zeroTranslateBoth, zeroParabolic, ModularGroup.coe_T_zpow,
    coe_mul, Matrix.mul_fin_two] <;> ring

theorem zeroTranslateBoth_mem_gamma0 (N : ℕ) (u v : ℤ) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    zeroTranslateBoth N u v g ∈ CongruenceSubgroup.Gamma0 N :=
  mul_mem (mul_mem (translation_mem_gamma0 N u) hg) (zeroParabolic_mem_gamma0 N v)

/-- The actual infinity-to-zero double cosets at nonzero denominator d
are exactly d together with k modulo d. Sufficiency uses the genuine
actual equal-bottom-row theorem after the derived right parabolic action. -/
theorem zero_double_coset_iff (N : ℕ) (hN : 0 < N) (g h : SL(2, ℤ))
    (k l : ℤ) (hg : g 1 0 = (N : ℤ) * k) (hh : h 1 0 = (N : ℤ) * l) :
    (∃ u v : ℤ, h = zeroTranslateBoth N u v g) ↔
      h 1 1 = g 1 1 ∧ g 1 1 ∣ l - k := by
  constructor
  · rintro ⟨u, v, rfl⟩
    have hlow := zeroTranslateBoth_lower N u v g
    refine ⟨hlow.2, ?_⟩
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hmul : (N : ℤ) * (l - (k - v * g 1 1)) = 0 := by
      rw [hg] at hlow
      nlinarith [hlow.1, hh]
    have hl : l = k - v * g 1 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hN0)
    refine ⟨-v, ?_⟩
    nlinarith [hl]
  · rintro ⟨hd, ⟨w, hw⟩⟩
    let v : ℤ := -w
    have hrows : bottomRow h = bottomRow (g * zeroParabolic N v) := by
      funext j
      fin_cases j
      · simp [bottomRow, zeroParabolic, coe_mul, Matrix.mul_fin_two, hg, hh, v]
        linear_combination (N : ℤ) * hw
      · simp [bottomRow, zeroParabolic, coe_mul, Matrix.mul_fin_two, hd]
    obtain ⟨u, hu⟩ := (bottomRow_eq_iff_left_translation (g * zeroParabolic N v) h).mp hrows
    exact ⟨u, v, by simpa only [zeroTranslateBoth, mul_assoc] using hu⟩

/-- The finite admissible zero-cusp residue, with its actual determinant gate. -/
abbrev ZeroResidue (N d : ℕ) := {u : ZMod d // IsUnit ((N : ZMod d) * u)}

def canonicalB (N d : ℕ) (u : ZMod d) : ℤ := -((((N : ZMod d) * u)⁻¹).val : ℤ)

theorem canonicalB_cast (N d : ℕ) [NeZero d] (u : ZMod d) :
    (canonicalB N d u : ZMod d) = -((N : ZMod d) * u)⁻¹ := by
  simp only [canonicalB, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem canonicalA_exists (N d : ℕ) [NeZero d] (r : ZeroResidue N d) :
    ∃ a : ℤ, a * (d : ℤ) - (N : ℤ) * (r.1.val : ℤ) * canonicalB N d r.1 = 1 := by
  have hzero : ((1 + (N : ℤ) * (r.1.val : ℤ) * canonicalB N d r.1 : ℤ) : ZMod d) = 0 := by
    simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val, canonicalB_cast, mul_neg]
    rw [ZMod.mul_inv_of_unit ((N : ZMod d) * r.1) r.2]
    ring
  obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hzero
  refine ⟨a, ?_⟩
  nlinarith [ha]

def canonicalA (N d : ℕ) [NeZero d] (r : ZeroResidue N d) : ℤ :=
  Classical.choose (canonicalA_exists N d r)

def zeroCanonicalMatrix (N d : ℕ) [NeZero d] (r : ZeroResidue N d) : SL(2, ℤ) :=
  ⟨!![canonicalA N d r, canonicalB N d r.1; (N : ℤ) * (r.1.val : ℤ), (d : ℤ)], by
    rw [Matrix.det_fin_two_of]
    have ha := Classical.choose_spec (canonicalA_exists N d r)
    change canonicalA N d r * (d : ℤ) -
      canonicalB N d r.1 * ((N : ℤ) * (r.1.val : ℤ)) = 1
    dsimp [canonicalA]
    nlinarith [ha]⟩

theorem zeroCanonicalMatrix_mem_gamma0 (N d : ℕ) [NeZero d] (r : ZeroResidue N d) :
    zeroCanonicalMatrix N d r ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_iff_level_dvd_c]
  exact ⟨(r.1.val : ℤ), rfl⟩

/-- Necessity of the finite determinant gate for every actual matrix. -/
theorem zero_actual_residue_isUnit (N d : ℕ) [NeZero d] (g : SL(2, ℤ))
    (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 = (d : ℤ)) :
    IsUnit ((N : ZMod d) * (k : ZMod d)) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  rw [hc, hd] at hdet
  have hcast := congrArg (fun a : ℤ => (a : ZMod d)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
    ZMod.natCast_self, mul_zero, zero_sub] at hcast
  apply isUnit_iff_exists_inv.mpr
  refine ⟨-(g 0 1 : ZMod d), ?_⟩
  convert hcast using 1 <;> ring

/-- The actual determinant forces the denominator to be coprime to the
level; this is derived from its actual finite unit gate. -/
theorem zero_actual_denominator_coprime (N d : ℕ) [NeZero d] (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hd : g 1 1 = (d : ℤ)) :
    N.Coprime d := by
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c N g).mp hg
  have hu := zero_actual_residue_isUnit N d g k hk hd
  exact (ZMod.isUnit_iff_coprime N d).mp (isUnit_of_mul_isUnit_left hu)
/-- Every actual positive-denominator Gamma0 matrix is in the double
orbit of one of the constructed actual finite representatives. -/
theorem zeroCanonicalMatrix_surjective_on_double_cosets (N d : ℕ) [NeZero d]
    (hN : 0 < N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (hd : g 1 1 = (d : ℤ)) :
    ∃ r : ZeroResidue N d, ∃ u v : ℤ, zeroCanonicalMatrix N d r = zeroTranslateBoth N u v g := by
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c N g).mp hg
  let r : ZeroResidue N d := ⟨(k : ZMod d), zero_actual_residue_isUnit N d g k hk hd⟩
  have hdiv : (d : ℤ) ∣ (r.1.val : ℤ) - k := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
    simp [r]
  refine ⟨r, (zero_double_coset_iff N hN g (zeroCanonicalMatrix N d r) k
    (r.1.val : ℤ) hk rfl).mpr ?_⟩
  exact ⟨by simpa [zeroCanonicalMatrix] using hd.symm, by simpa only [hd] using hdiv⟩

theorem zeroCanonicalMatrix_double_coset_injective (N d : ℕ) [NeZero d] (hN : 0 < N)
    (r s : ZeroResidue N d)
    (horbit : ∃ u v : ℤ, zeroCanonicalMatrix N d s = zeroTranslateBoth N u v (zeroCanonicalMatrix N d r)) :
    r = s := by
  have hdiv := ((zero_double_coset_iff N hN (zeroCanonicalMatrix N d r)
    (zeroCanonicalMatrix N d s) (r.1.val : ℤ) (s.1.val : ℤ) rfl rfl).mp horbit).2
  change (d : ℤ) ∣ (s.1.val : ℤ) - (r.1.val : ℤ) at hdiv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr hdiv
  simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] at hz
  exact Subtype.ext (sub_eq_zero.mp hz).symm

/-- Literal canonical zero-cusp matrix phase, using its actual top-right
entry and its actual normalized lower coordinate -k. -/
def zeroMatrixPhase (N d : ℕ) [NeZero d] (m n : ℤ) (r : ZeroResidue N d) : ℂ :=
  ZMod.stdAddChar ((m : ZMod d) * (zeroCanonicalMatrix N d r 0 1 : ZMod d) -
    (n : ZMod d) * (r.1.val : ZMod d))

theorem zeroMatrixPhase_eq_residuePhase (N d : ℕ) [NeZero d]
    (m n : ℤ) (r : ZeroResidue N d) :
    zeroMatrixPhase N d m n r =
      ZMod.stdAddChar (-(m : ZMod d) * (((N : ZMod d) * r.1)⁻¹) - (n : ZMod d) * r.1) := by
  simp only [zeroMatrixPhase, zeroCanonicalMatrix, canonicalB_cast, ZMod.natCast_zmod_val]
  congr 1
  ring

def zeroMatrixKloosterman (N d : ℕ) [NeZero d] (m n : ℤ) : ℂ :=
  ∑ r : ZeroResidue N d, zeroMatrixPhase N d m n r

def zeroGeneralizedKloosterman (N d : ℕ) [NeZero d] (m n : ℤ) : ℂ :=
  ∑ u : ZMod d, if IsUnit ((N : ZMod d) * u) then
    ZMod.stdAddChar (-(m : ZMod d) * (((N : ZMod d) * u)⁻¹) - (n : ZMod d) * u)
  else 0

/-- Exact finite generalized Kloosterman dictionary from actual canonical
zero-cusp matrix double cosets, without assuming the desired sum identity. -/
theorem zeroMatrixKloosterman_eq_generalized (N d : ℕ) [NeZero d] (m n : ℤ) :
    zeroMatrixKloosterman N d m n = zeroGeneralizedKloosterman N d m n := by
  let f : ZMod d → ℂ := fun u =>
    ZMod.stdAddChar (-(m : ZMod d) * (((N : ZMod d) * u)⁻¹) - (n : ZMod d) * u)
  have hsum : (∑ r : ZeroResidue N d, zeroMatrixPhase N d m n r) =
      ∑ u ∈ (Finset.univ : Finset (ZMod d)).filter (fun u => IsUnit ((N : ZMod d) * u)), f u := by
    apply Finset.sum_bij (fun r _ => r.1)
    · intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩
    · intro r hr s hs hrs
      exact Subtype.ext hrs
    · intro u hu
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
    · intro r hr
      exact zeroMatrixPhase_eq_residuePhase N d m n r
  simpa only [zeroMatrixKloosterman, zeroGeneralizedKloosterman, Finset.sum_filter, f] using hsum

private theorem stdAddChar_int_fourier (d : ℕ) [NeZero d] (A : ℤ) :
    ZMod.stdAddChar (A : ZMod d) =
      AddCircle.fourier 1 (((A : ℝ) / (d : ℝ)) : UnitAddCircle) := by
  rw [ZMod.stdAddChar_coe, AddCircle.fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Literal normalized real phase in gamma*sigma0, rather than an
arithmetic phase supplied as its definition. -/
def zeroNormalizedPhase (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (m n : ℤ) (r : ZeroResidue N d) : ℂ :=
  AddCircle.fourier 1
    (((m : ℝ) * (zeroCuspProduct N (zeroCanonicalMatrix N d r) 0 0 /
        zeroCuspProduct N (zeroCanonicalMatrix N d r) 1 0) +
      (n : ℝ) * (zeroCuspProduct N (zeroCanonicalMatrix N d r) 1 1 /
        zeroCuspProduct N (zeroCanonicalMatrix N d r) 1 0)) : UnitAddCircle)

theorem zeroNormalizedPhase_eq_matrixPhase (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) (r : ZeroResidue N d) :
    zeroNormalizedPhase N hN d m n r = zeroMatrixPhase N d m n r := by
  have hd : zeroCanonicalMatrix N d r 1 1 ≠ 0 := by
    change (d : ℤ) ≠ 0
    exact_mod_cast NeZero.ne d
  have hcoords := zero_normalized_coordinates N hN (zeroCanonicalMatrix N d r)
    (r.1.val : ℤ) rfl hd
  unfold zeroNormalizedPhase
  rw [hcoords.1, hcoords.2]
  have harg :
      (m : ℝ) * (((zeroCanonicalMatrix N d r 0 1 : ℤ) : ℝ) / (d : ℝ)) +
      (n : ℝ) * (-((r.1.val : ℤ) : ℝ) / (d : ℝ)) =
      ((m * zeroCanonicalMatrix N d r 0 1 - n * (r.1.val : ℤ) : ℤ) : ℝ) / (d : ℝ) := by
    push_cast
    ring
  change AddCircle.fourier 1
    (((m : ℝ) * (((zeroCanonicalMatrix N d r 0 1 : ℤ) : ℝ) / (d : ℝ)) +
      (n : ℝ) * (-((r.1.val : ℤ) : ℝ) / (d : ℝ))) : UnitAddCircle) = _
  rw [harg, ← stdAddChar_int_fourier]
  simp only [zeroMatrixPhase, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

/-- The finite sum of the actual normalized matrix phases is the derived
generalized zero-cusp Kloosterman sum, with the genuine sqrt(N)*d modulus. -/
theorem sum_zeroNormalizedPhase_eq_generalized (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) :
    (∑ r : ZeroResidue N d, zeroNormalizedPhase N hN d m n r) =
      zeroGeneralizedKloosterman N d m n := by
  simp_rw [zeroNormalizedPhase_eq_matrixPhase]
  exact zeroMatrixKloosterman_eq_generalized N d m n
end ImbalancedChen.Part3.InfinityZeroArithmetic20261025a



