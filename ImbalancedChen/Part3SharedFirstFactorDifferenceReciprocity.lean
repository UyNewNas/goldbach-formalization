import ImbalancedChen.Part3CanonicalReciprocalPhase
import ImbalancedChen.Part3SharedFirstFactorDispersion
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Exact difference reciprocity on the original shared first factor

All arithmetic data are constructed from the original positive tuple and its
actual CRT compatibility. The proof combines the two divisibilities with common
`w₀`, then those with common `delta`; it allows `delta` and `w₀` to overlap.
The resulting three phases retain the signed difference quotient, the complete
root modulo `g*d₁`, and the slow denominator `N₁*L`.

The six public statements are finite identities. They include arbitrary signed
`a,h`, zero difference, and modulus one, and specialize to the literal original
shared rows and original `V` Poisson frequency. No spectral or distribution
estimate, large-supported-part payment, or unconditional main theorem is claimed.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical
open scoped FourierTransform

namespace SharedDifferenceReciprocity

private theorem nat_lcm_dvd_int {m n : ℕ} {E : ℤ}
    (hm : (m : ℤ) ∣ E) (hn : (n : ℤ) ∣ E) :
    ((m.lcm n : ℕ) : ℤ) ∣ E := by
  have h := Int.coe_lcm_dvd_iff.mpr ⟨hm, hn⟩
  simpa only [Int.lcm, Int.natAbs_natCast] using h

/-- The signed polynomial proof precedes both common-factor lcm merges. -/
private theorem differenceE_dvd
    {g d₁ delta v₀ w₀ n₁ n₂ N₁ N₂ L : ℕ} {a b f t : ℤ}
    (hN₁ : N₁ = g * d₁ * n₁) (hN₂ : N₂ = g * n₂)
    (hL : L = delta * v₀ * w₀)
    (hnδ : n₁.Coprime delta) (hv : v₀.Coprime (n₁ * w₀))
    (hf : (delta : ℤ) * f = (d₁ : ℤ) * n₁ - n₂)
    (ht : Int.ModEq (n₁ * w₀ : ℕ)
      (((g * d₁ * n₂ * v₀ : ℕ) : ℤ) * t) 1)
    (hb₁ : Int.ModEq (delta * v₀ : ℕ) (b * N₁) a)
    (hb₂ : Int.ModEq (delta * w₀ : ℕ) (b * N₂) a) :
    ((n₁ * L : ℕ) : ℤ) ∣
      ((N₁ : ℤ) * b - a - a * f * (g * d₁ : ℕ) * delta * v₀ * t) := by
  let E : ℤ := (N₁ : ℤ) * b - a - a * f * (g * d₁ : ℕ) * delta * v₀ * t
  have hN₁Z : (N₁ : ℤ) = (g : ℤ) * d₁ * n₁ := by exact_mod_cast hN₁
  have hN₂Z : (N₂ : ℤ) = (g : ℤ) * n₂ := by exact_mod_cast hN₂
  have hb₂w : Int.ModEq (w₀ : ℤ) (b * N₂) a := hb₂.of_dvd
    (by exact_mod_cast (dvd_mul_left w₀ delta : w₀ ∣ delta * w₀))
  obtain ⟨s, hs⟩ := ht.dvd
  obtain ⟨r, hr⟩ := hb₂w.dvd
  push_cast at hs
  rw [hN₂Z] at hr
  have hK : (w₀ : ℤ) ∣ b - a * d₁ * v₀ * t := by
    refine ⟨(n₁ : ℤ) * b * s - (d₁ : ℤ) * v₀ * t * r, ?_⟩
    linear_combination b * hs - (d₁ : ℤ) * v₀ * t * hr
  obtain ⟨k, hk⟩ := hK
  have hδv : ((delta * v₀ : ℕ) : ℤ) ∣ E := by
    obtain ⟨j, hj⟩ := hb₁.dvd
    refine ⟨-j - a * f * (g : ℤ) * d₁ * t, ?_⟩
    dsimp only [E]
    push_cast at hj ⊢
    linear_combination -hj
  have hnw : ((n₁ * w₀ : ℕ) : ℤ) ∣ E := by
    refine ⟨(g : ℤ) * d₁ * k - a * s, ?_⟩
    dsimp only [E]
    rw [hN₁Z]
    push_cast
    linear_combination (g : ℤ) * d₁ * n₁ * hk - a * hs -
      a * (g : ℤ) * d₁ * v₀ * t * hf
  have hδw : ((delta * w₀ : ℕ) : ℤ) ∣ E := by
    obtain ⟨j, hj⟩ := hb₂.dvd
    refine ⟨-j + (g : ℤ) * f * k, ?_⟩
    dsimp only [E]
    rw [hN₁Z]
    push_cast at hj ⊢
    rw [hN₂Z] at hj
    linear_combination -hj + (g : ℤ) * delta * f * hk - (g : ℤ) * b * hf
  have hδnw : ((delta * n₁ * w₀ : ℕ) : ℤ) ∣ E := by
    have h := nat_lcm_dvd_int hnw hδw
    rw [Nat.lcm_mul_right, hnδ.lcm_eq_mul] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hδnw' : ((delta * (n₁ * w₀) : ℕ) : ℤ) ∣ E := by
    simpa only [mul_assoc] using hδnw
  have h := nat_lcm_dvd_int hδv hδnw'
  rw [Nat.lcm_mul_left, hv.lcm_eq_mul] at h
  simpa only [E, hL, mul_assoc, mul_comm, mul_left_comm] using h

private theorem fourier_add (h : ℤ) (x y : UnitAddCircle) :
    fourier h (x + y) = fourier h x * fourier h y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n := by
  have hlo := (Finset.mem_Icc.mp hn).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem row_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ) × ℕ} (hl : l ∈ d.sharedFirstFactorRows) :
    0 < l.1.1 * l.1.2 ∧ 0 < l.2 := by
  obtain ⟨hf, hN⟩ := Finset.mem_product.mp hl
  obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp hf
  change l.2 ∈ factorCarrier d.U at hN
  exact ⟨Nat.mul_pos (factor_pos hd.2.2.2.1 h₂)
    (factor_pos hd.2.2.2.2.1 h₃), factor_pos hd.1 hN⟩

end SharedDifferenceReciprocity

/-- Every license, including the full E divisibility, follows from the raw tuple. -/
theorem sharedDifferenceData_licenses
    {p v w N₁ N₂ : ℕ}
    (hp : 0 < p) (hv : 0 < v) (hw : 0 < w)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hc : ComplexCRT.Compatible (p * v) (p * w) N₁ N₂) (a : ℤ) :
    let g := N₁.gcd N₂
    let D := v.gcd w
    let v₀ := v / D
    let w₀ := w / D
    let delta := p * D
    let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
    let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
    let n₂ := N₂ / g
    let A := g * d₁
    let L := (p * v).lcm (p * w)
    let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
    let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
    let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
    0 < g ∧ 0 < D ∧ 0 < d₁ ∧ 0 < n₁ ∧ 0 < n₂ ∧
      0 < v₀ ∧ 0 < w₀ ∧ 0 < A ∧ 0 < L ∧
      N₁ = g * d₁ * n₁ ∧ N₂ = g * n₂ ∧
      v = D * v₀ ∧ w = D * w₀ ∧ L = delta * v₀ * w₀ ∧
      v₀.Coprime w₀ ∧ n₁.Coprime delta ∧ v₀.Coprime (n₁ * w₀) ∧
      (A * n₂ * v₀).Coprime (n₁ * w₀) ∧ (n₁ * L).Coprime A ∧
      (delta : ℤ) * f = (d₁ : ℤ) * n₁ - n₂ ∧
      ((n₁ * L : ℕ) : ℤ) ∣
        ((N₁ : ℤ) * b - a - a * f * (A : ℤ) * delta * v₀ * t) := by
  let g := N₁.gcd N₂
  let D := v.gcd w
  let v₀ := v / D
  let w₀ := w / D
  let delta := p * D
  let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
  let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
  let n₂ := N₂ / g
  let A := g * d₁
  let L := (p * v).lcm (p * w)
  let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
  let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
  let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
  change 0 < g ∧ 0 < D ∧ 0 < d₁ ∧ 0 < n₁ ∧ 0 < n₂ ∧
    0 < v₀ ∧ 0 < w₀ ∧ 0 < A ∧ 0 < L ∧
    N₁ = g * d₁ * n₁ ∧ N₂ = g * n₂ ∧
    v = D * v₀ ∧ w = D * w₀ ∧ L = delta * v₀ * w₀ ∧
    v₀.Coprime w₀ ∧ n₁.Coprime delta ∧ v₀.Coprime (n₁ * w₀) ∧
    (A * n₂ * v₀).Coprime (n₁ * w₀) ∧ (n₁ * L).Coprime A ∧
    (delta : ℤ) * f = (d₁ : ℤ) * n₁ - n₂ ∧
    ((n₁ * L : ℕ) : ℤ) ∣
      ((N₁ : ℤ) * b - a - a * f * (A : ℤ) * delta * v₀ * t)
  have hcan := CanonicalReciprocalData.wGCDData_valid
    (Nat.mul_pos hp hv) (Nat.mul_pos hp hw) hN₁ hN₂
  have hg : 0 < g := hcan.d_pos
  have hd₁ : 0 < d₁ := hcan.d₁_pos
  have hn₁ : 0 < n₁ := hcan.n₁_pos
  have hn₂ : 0 < n₂ := hcan.n₂_pos
  have hN₁eq : N₁ = g * d₁ * n₁ := hcan.N₁_eq
  have hN₂eq : N₂ = g * n₂ := hcan.N₂_eq
  have hD : 0 < D := Nat.gcd_pos_of_pos_left w hv
  have hv₀ : 0 < v₀ :=
    Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_left v w)) hD
  have hw₀ : 0 < w₀ :=
    Nat.div_pos (Nat.le_of_dvd hw (Nat.gcd_dvd_right v w)) hD
  have hA : 0 < A := Nat.mul_pos hg hd₁
  have hL : 0 < L := Nat.pos_of_ne_zero
    (Nat.lcm_ne_zero (Nat.mul_pos hp hv).ne' (Nat.mul_pos hp hw).ne')
  have hveq : v = D * v₀ := (Nat.mul_div_cancel' (Nat.gcd_dvd_left v w)).symm
  have hweq : w = D * w₀ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right v w)).symm
  have hvw : v₀.Coprime w₀ := by
    change (v / D).gcd (w / D) = 1
    apply Nat.mul_left_cancel hD
    rw [← Nat.gcd_mul_left, Nat.mul_div_cancel' (Nat.gcd_dvd_left v w),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right v w), mul_one]
  have hq : p * v = delta * v₀ := by
    dsimp only [delta]
    rw [hveq]
    ring
  have hr : p * w = delta * w₀ := by
    dsimp only [delta]
    rw [hweq]
    ring
  have hLeq : L = delta * v₀ * w₀ := by
    change (p * v).lcm (p * w) = _
    rw [hq, hr, Nat.lcm_mul_left, hvw.lcm_eq_mul, mul_assoc]
    dsimp only [delta]
    ring
  have hgq : g.Coprime (p * v) :=
    hc.1.of_dvd_left (Nat.gcd_dvd_left N₁ N₂)
  have hgr : g.Coprime (p * w) :=
    hc.2.1.of_dvd_left (Nat.gcd_dvd_right N₁ N₂)
  have hgL : g.Coprime L :=
    (hgq.mul_right hgr).of_dvd_right (Nat.lcm_dvd_mul (p * v) (p * w))
  have hd₁L : d₁.Coprime L :=
    (CanonicalReciprocalData.coprime_of_prime_support hgL.symm hcan.d₁_support).symm
  have hAL : A.Coprime L := hgL.mul_left hd₁L
  have hn₁A : n₁.Coprime A := hcan.n₁_d.mul_right hcan.n₁_d₁
  have hn₁N : n₁ ∣ N₁ := by rw [hN₁eq]; exact dvd_mul_left _ _
  have hn₂N : n₂ ∣ N₂ := by rw [hN₂eq]; exact dvd_mul_left _ _
  have hn₁q : n₁.Coprime (delta * v₀) := by
    rw [← hq]
    exact hc.1.of_dvd_left hn₁N
  have hnδ : n₁.Coprime delta := hn₁q.of_dvd_right (dvd_mul_right _ _)
  have hvn : v₀.Coprime (n₁ * w₀) :=
    (hn₁q.of_dvd_right (dvd_mul_left _ _)).symm.mul_right hvw
  have hwL : w₀ ∣ L := by rw [hLeq]; exact dvd_mul_left _ _
  have hAw : A.Coprime w₀ := hAL.of_dvd_right hwL
  have hn₂w : n₂.Coprime w₀ := by
    apply hc.2.1.of_dvd hn₂N
    rw [hr]
    exact dvd_mul_left _ _
  have hInv : (A * n₂ * v₀).Coprime (n₁ * w₀) :=
    ((hn₁A.symm.mul_right hAw).mul_left
      (hcan.n₁_n₂.symm.mul_right hn₂w)).mul_left hvn
  have hRoot : (n₁ * L).Coprime A := hn₁A.mul_left hAL.symm
  have hcong : Nat.ModEq delta (d₁ * n₁) n₂ := by
    have h := hcan.n_congruence hc
    change Nat.ModEq ((p * v).gcd (p * w)) (d₁ * n₁) n₂ at h
    simpa only [sharedFirstFactor_gcd] using h
  have hfdiv : (delta : ℤ) ∣ (d₁ : ℤ) * n₁ - n₂ := by
    simpa only [Nat.cast_mul] using (Int.natCast_modEq_iff.mpr hcong).symm.dvd
  have hf : (delta : ℤ) * f = (d₁ : ℤ) * n₁ - n₂ :=
    Int.mul_ediv_cancel' hfdiv
  have hb := ComplexCRT.residue_spec a hc
  have hb₁ : Int.ModEq (delta * v₀ : ℕ) (b * N₁) a := by
    have hh : Int.ModEq (p * v : ℕ) (b * N₁) a := hb.1
    rw [hq] at hh
    exact hh
  have hb₂ : Int.ModEq (delta * w₀ : ℕ) (b * N₂) a := by
    have hh : Int.ModEq (p * w : ℕ) (b * N₂) a := hb.2.1
    rw [hr] at hh
    exact hh
  have ht : Int.ModEq (n₁ * w₀ : ℕ) (((A * n₂ * v₀ : ℕ) : ℤ) * t) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec hInv
  have hE := SharedDifferenceReciprocity.differenceE_dvd
    hN₁eq hN₂eq hLeq hnδ hvn hf ht hb₁ hb₂
  exact ⟨hg, hD, hd₁, hn₁, hn₂, hv₀, hw₀, hA, hL,
    hN₁eq, hN₂eq, hveq, hweq, hLeq, hvw, hnδ, hvn, hInv, hRoot, hf, hE⟩

/-- Exact root, slow and signed reciprocal phases, including zero difference. -/
theorem sharedDifferenceReciprocity_circle
    {p v w N₁ N₂ : ℕ}
    (hp : 0 < p) (hv : 0 < v) (hw : 0 < w)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hc : ComplexCRT.Compatible (p * v) (p * w) N₁ N₂) (a : ℤ) :
    let g := N₁.gcd N₂
    let D := v.gcd w
    let v₀ := v / D
    let w₀ := w / D
    let delta := p * D
    let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
    let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
    let n₂ := N₂ / g
    let A := g * d₁
    let L := (p * v).lcm (p * w)
    let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
    let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
    let z := CanonicalReciprocalPhase.wPhaseInverse (n₁ * L) A
    let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
    ((((b : ℝ) / (L : ℝ)) : ℝ) : UnitAddCircle) =
      (((-(a : ℝ) * (z : ℝ) / (A : ℝ)) : ℝ) : UnitAddCircle) +
        ((((a : ℝ) / ((N₁ : ℝ) * L)) : ℝ) : UnitAddCircle) +
          (((((a : ℝ) * (f : ℝ) * (t : ℝ)) / ((n₁ : ℝ) * w₀)) : ℝ) : UnitAddCircle) := by
  let g := N₁.gcd N₂
  let D := v.gcd w
  let v₀ := v / D
  let w₀ := w / D
  let delta := p * D
  let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
  let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
  let n₂ := N₂ / g
  let A := g * d₁
  let L := (p * v).lcm (p * w)
  let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
  let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
  let z := CanonicalReciprocalPhase.wPhaseInverse (n₁ * L) A
  let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
  change (((b : ℝ) / (L : ℝ) : ℝ) : UnitAddCircle) =
    ((-(a : ℝ) * (z : ℝ) / (A : ℝ) : ℝ) : UnitAddCircle) +
      (((a : ℝ) / ((N₁ : ℝ) * L) : ℝ) : UnitAddCircle) +
        (((a : ℝ) * (f : ℝ) * (t : ℝ) / ((n₁ : ℝ) * w₀) : ℝ) : UnitAddCircle)
  have hdata := sharedDifferenceData_licenses hp hv hw hN₁ hN₂ hc a
  change 0 < g ∧ 0 < D ∧ 0 < d₁ ∧ 0 < n₁ ∧ 0 < n₂ ∧
    0 < v₀ ∧ 0 < w₀ ∧ 0 < A ∧ 0 < L ∧
    N₁ = g * d₁ * n₁ ∧ N₂ = g * n₂ ∧
    v = D * v₀ ∧ w = D * w₀ ∧ L = delta * v₀ * w₀ ∧
    v₀.Coprime w₀ ∧ n₁.Coprime delta ∧ v₀.Coprime (n₁ * w₀) ∧
    (A * n₂ * v₀).Coprime (n₁ * w₀) ∧ (n₁ * L).Coprime A ∧
    (delta : ℤ) * f = (d₁ : ℤ) * n₁ - n₂ ∧
    ((n₁ * L : ℕ) : ℤ) ∣
      ((N₁ : ℤ) * b - a - a * f * (A : ℤ) * delta * v₀ * t) at hdata
  rcases hdata with ⟨_hg, hD, _hd₁, hn₁, _hn₂, hv₀, hw₀, hA, hL,
    hN₁eq, _hN₂eq, _hveq, _hweq, hLeq, _hvw, _hnδ, _hvn, _hInv, hRoot, _hf, hE⟩
  obtain ⟨j, hj⟩ := hE
  have hN₁A : N₁ = A * n₁ := hN₁eq
  have hN₁Z : (N₁ : ℤ) = (A : ℤ) * n₁ := by exact_mod_cast hN₁A
  have hz : Int.ModEq A (((n₁ * L : ℕ) : ℤ) * z) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec hRoot
  obtain ⟨u, hu⟩ := hz.dvd
  push_cast at hj hu
  rw [hN₁Z] at hj
  have hjmod : Int.ModEq A j (-a * z) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-j * u - ((n₁ : ℤ) * b - a * f * delta * v₀ * t) * z, ?_⟩
    linear_combination -j * hu + z * hj
  have hjcircle : (((j : ℝ) / (A : ℝ) : ℝ) : UnitAddCircle) =
      ((-(a : ℝ) * (z : ℝ) / (A : ℝ) : ℝ) : UnitAddCircle) := by
    simpa only [Int.cast_mul, Int.cast_neg] using
      CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq hA hjmod
  have hjR : (A : ℝ) * n₁ * b - a -
      (a : ℝ) * f * A * delta * v₀ * t = (n₁ : ℝ) * L * j := by
    exact_mod_cast hj
  have hN₁R : (N₁ : ℝ) = (A : ℝ) * n₁ := by exact_mod_cast hN₁A
  have hLR : (L : ℝ) = (delta : ℝ) * v₀ * w₀ := by exact_mod_cast hLeq
  have hnum : (N₁ : ℝ) * b = (n₁ : ℝ) * L * j + a +
      (a : ℝ) * f * A * delta * v₀ * t := by
    rw [hN₁R]
    linarith [hjR]
  have hA0 : (A : ℝ) ≠ 0 := by positivity
  have hN₁0 : (N₁ : ℝ) ≠ 0 := by positivity
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hn₁0 : (n₁ : ℝ) ≠ 0 := by positivity
  have hv₀0 : (v₀ : ℝ) ≠ 0 := by positivity
  have hw₀0 : (w₀ : ℝ) ≠ 0 := by positivity
  have hdelta0 : (delta : ℝ) ≠ 0 := by dsimp only [delta]; positivity
  have hreal : (b : ℝ) / L = (j : ℝ) / A +
      (a : ℝ) / ((N₁ : ℝ) * L) +
        (a : ℝ) * f * t / ((n₁ : ℝ) * w₀) := by
    calc
      (b : ℝ) / L =
          ((n₁ : ℝ) * L * j + a + (a : ℝ) * f * A * delta * v₀ * t) /
            ((N₁ : ℝ) * L) := by
        rw [← hnum]
        field_simp [hN₁0, hL0]
      _ = (j : ℝ) / A + (a : ℝ) / ((N₁ : ℝ) * L) +
          (a : ℝ) * f * t / ((n₁ : ℝ) * w₀) := by
        rw [hN₁R, hLR]
        field_simp [hA0, hn₁0, hdelta0, hv₀0, hw₀0]
  rw [hreal, AddCircle.coe_add, AddCircle.coe_add, hjcircle]

/-- Fourier transport retains every signed integer frequency and all three phases. -/
theorem sharedDifferenceReciprocity_fourier
    {p v w N₁ N₂ : ℕ}
    (hp : 0 < p) (hv : 0 < v) (hw : 0 < w)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hc : ComplexCRT.Compatible (p * v) (p * w) N₁ N₂) (a h : ℤ) :
    let g := N₁.gcd N₂
    let D := v.gcd w
    let v₀ := v / D
    let w₀ := w / D
    let delta := p * D
    let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
    let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
    let n₂ := N₂ / g
    let A := g * d₁
    let L := (p * v).lcm (p * w)
    let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
    let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
    let z := CanonicalReciprocalPhase.wPhaseInverse (n₁ * L) A
    let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
    fourier h (((b : ℝ) / (L : ℝ) : ℝ) : UnitAddCircle) =
      fourier h (((-(a : ℝ) * (z : ℝ) / (A : ℝ)) : ℝ) : UnitAddCircle) *
        fourier h ((((a : ℝ) / ((N₁ : ℝ) * L)) : ℝ) : UnitAddCircle) *
          fourier h (((((a : ℝ) * (f : ℝ) * (t : ℝ)) / ((n₁ : ℝ) * w₀)) : ℝ) : UnitAddCircle) := by
  have he := sharedDifferenceReciprocity_circle hp hv hw hN₁ hN₂ hc a
  dsimp only at he ⊢
  rw [he, SharedDifferenceReciprocity.fourier_add,
    SharedDifferenceReciprocity.fourier_add]

/-- The actual standard finite additive character has the same positive sign. -/
theorem fourier_int_div_nat_eq_stdAddChar
    (m : ℕ) [NeZero m] (h z : ℤ) :
    fourier h ((((z : ℝ) / (m : ℝ)) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((h * z : ℤ) : ZMod m) := by
  rw [fourier_coe_apply, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- The constructed Bezout inverse is precisely the existing `ZMod` inverse. -/
theorem fourier_inverse_phase_eq_stdAddChar
    (m n : ℕ) [NeZero m] (hc : n.Coprime m) (h a : ℤ) :
    fourier h (((((a : ℝ) *
      (CanonicalReciprocalPhase.wPhaseInverse n m : ℝ)) / (m : ℝ)) : ℝ) :
        UnitAddCircle) =
      ZMod.stdAddChar (((h * a : ℤ) : ZMod m) * (n : ZMod m)⁻¹) := by
  let t := CanonicalReciprocalPhase.wPhaseInverse n m
  have ht : (n : ZMod m) * (t : ZMod m) = 1 := by
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff ((n : ℤ) * t) 1 m).mpr
        (CanonicalReciprocalPhase.wPhaseInverse_spec hc)
  have hinv : (t : ZMod m) = (n : ZMod m)⁻¹ :=
    (ZMod.inv_eq_of_mul_eq_one m (n : ZMod m) (t : ZMod m) ht).symm
  have he := fourier_int_div_nat_eq_stdAddChar m h (a * t)
  simpa only [Int.cast_mul, mul_assoc, hinv] using he

/-- The original shared-row Poisson frequency uses original `V`, literal cutoff and all h. -/
theorem MediumAtom.sharedFirstFactor_poissonFrequency_eq_differencePhases
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier)
    {l l' : (ℕ × ℕ) × ℕ}
    (hl : l ∈ d.sharedFirstFactorRows) (hl' : l' ∈ d.sharedFirstFactorRows)
    (hc : ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
      (p * (l'.1.1 * l'.1.2)) l.2 l'.2) (h : ℤ) :
    let v := l.1.1 * l.1.2
    let w := l'.1.1 * l'.1.2
    let N₁ := l.2
    let N₂ := l'.2
    let a := d.residue
    let g := N₁.gcd N₂
    let D := v.gcd w
    let v₀ := v / D
    let w₀ := w / D
    let delta := p * D
    let d₁ := CanonicalReciprocalData.supportedPart (N₁ / g) g
    let n₁ := CanonicalReciprocalData.coprimePart (N₁ / g) g
    let n₂ := N₂ / g
    let A := g * d₁
    let L := (p * v).lcm (p * w)
    let f : ℤ := ((d₁ : ℤ) * n₁ - n₂) / (delta : ℤ)
    let t := CanonicalReciprocalPhase.wPhaseInverse (A * n₂ * v₀) (n₁ * w₀)
    let z := CanonicalReciprocalPhase.wPhaseInverse (n₁ * L) A
    let b := ComplexCRT.residue (p * v) (p * w) N₁ N₂ a
    CommonSmoothCutoff.poissonNonzeroFrequency
      (d.V / (L : ℝ)) ((b : ℝ) / (L : ℝ)) h =
      if h = 0 then 0 else
        (d.V / (L : ℝ)) •
          (𝓕 CommonSmoothCutoff.dyadicCutoffSchwartz) ((d.V / (L : ℝ)) * h) *
          fourier h (((-(a : ℝ) * (z : ℝ) / (A : ℝ)) : ℝ) : UnitAddCircle) *
            fourier h ((((a : ℝ) / ((N₁ : ℝ) * L)) : ℝ) : UnitAddCircle) *
              fourier h (((((a : ℝ) * (f : ℝ) * (t : ℝ)) / ((n₁ : ℝ) * w₀)) : ℝ) : UnitAddCircle) := by
  have hpp : 0 < p := SharedDifferenceReciprocity.factor_pos hd.2.2.1
    (Finset.mem_filter.mp hp).1
  have hleft := SharedDifferenceReciprocity.row_pos hd hl
  have hright := SharedDifferenceReciprocity.row_pos hd hl'
  have he := sharedDifferenceReciprocity_fourier hpp hleft.1 hright.1
    hleft.2 hright.2 hc d.residue h
  dsimp only at he ⊢
  unfold CommonSmoothCutoff.poissonNonzeroFrequency
  by_cases hh : h = 0
  · simp only [hh, if_true]
  · simp only [if_neg hh]
    rw [he]
    ring

end

end ImbalancedChen.Part3
