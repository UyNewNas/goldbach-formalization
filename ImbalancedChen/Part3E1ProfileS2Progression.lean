import ImbalancedChen.Part3E1FixedDSource
import ImbalancedChen.Part3SmoothReciprocalWeil

/-!
# The physical one-congruence progression for a supported Schwartz profile
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators FourierTransform SchwartzMap
open OriginalSmoothPoissonTail (inverseResidue)

/-- The natural sample points in the physical support of the profile. -/
def sameCutoffS2Carrier (V : ℝ) : Finset ℕ :=
  Icc ⌈V / 2⌉₊ ⌊5 * V / 2⌋₊

theorem profileS2Carrier_support (ψ : 𝓢(ℝ, ℂ))
    (hψ : ∀ ⦃x : ℝ⦄, ψ x ≠ 0 → x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2))
    {V : ℝ} (hV : 0 < V) {v : ℕ}
    (hv : ψ ((v : ℝ) / V) ≠ 0) : v ∈ sameCutoffS2Carrier V := by
  obtain ⟨hlo, hhi⟩ := hψ hv
  exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (by linarith [(le_div_iff₀ hV).mp hlo]),
    Nat.le_floor (by linarith [(div_le_iff₀ hV).mp hhi])⟩

/-- The original multiplicative congruence on the natural sample carrier. -/
def physicalProfileS2Progression (ψ : 𝓢(ℝ, ℂ)) (V : ℝ) (a : ℤ) (m n : ℕ) : ℂ :=
  ∑ v ∈ sameCutoffS2Carrier V,
    if Int.ModEq m ((v * n : ℕ) : ℤ) a then ψ ((v : ℝ) / V) else 0

/-- The exact zero Fourier coefficient at the left physical modulus. -/
def profileS2ZeroMode (ψ : 𝓢(ℝ, ℂ)) (V : ℝ) (m : ℕ) : ℂ :=
  (V / (m : ℝ)) • (𝓕 ψ) 0

/-- For a primitive sample multiplier, the original congruence has the
exact inverse-residue zero mode and complete nonzero signed series. -/
theorem physicalProfileS2Progression_eq_zero_add_nonzero (ψ : 𝓢(ℝ, ℂ))
    (hψ : ∀ ⦃x : ℝ⦄, ψ x ≠ 0 → x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2))
    {V : ℝ} (hV : 0 < V)
    (a : ℤ) {m n : ℕ} (hm : 0 < m) (hn : n.Coprime m) :
    physicalProfileS2Progression ψ V a m n =
      profileS2ZeroMode ψ V m +
        ∑' h : ℤ, retainedS2Mode (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) V a m n h := by
  let _ : NeZero m := ⟨hm.ne'⟩
  let u : ZMod m := (a : ZMod m) * ((n : ZMod m)⁻¹)
  have hnUnit := (ZMod.isUnit_iff_coprime n m).mpr hn
  have hclass (v : ℕ) : Int.ModEq m ((v * n : ℕ) : ℤ) a ↔ (v : ZMod m) = u := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    constructor
    · intro hv
      calc
        (v : ZMod m) = (v : ZMod m) * (n : ZMod m) * (n : ZMod m)⁻¹ := by
          rw [mul_assoc, ZMod.mul_inv_of_unit _ hnUnit, mul_one]
        _ = u := by rw [hv]
    · intro hv
      rw [hv]
      change ((a : ZMod m) * (n : ZMod m)⁻¹) * (n : ZMod m) = (a : ZMod m)
      rw [mul_assoc, ZMod.inv_mul_of_unit _ hnUnit, mul_one]
  have hneg (x : ℝ) (hx : x < 0) : ψ x = 0 := by
    by_contra h
    linarith [(hψ h).1]
  have hphase (h : ℤ) :
      ZMod.stdAddChar ((h : ZMod m) * u) =
        fourier h ((((a * inverseResidue m (n : ℤ) : ℤ) : ℝ) / (m : ℝ)) : UnitAddCircle) := by
    have hc : ((h * (a * inverseResidue m (n : ℤ)) : ℤ) : ZMod m) =
        (h : ZMod m) * u := by
      simp only [u, inverseResidue, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [← hc, ZMod.stdAddChar_coe, fourier_coe_apply]
    push_cast
    congr 1
    ring
  let f (h : ℤ) : ℂ :=
    (V / (m : ℝ)) • (𝓕 ψ) ((V / (m : ℝ)) * (h : ℝ)) *
      ZMod.stdAddChar ((h : ZMod m) * u)
  have hs : Summable f :=
    (smoothProfile_progressionFourier_norm_summable m u hV ψ).of_norm
  have hupdate := hs.update (0 : ℤ) (0 : ℂ)
  have hsplit := Summable.tsum_eq_add_tsum_ite' (f := f) 0 hupdate
  simp only [physicalProfileS2Progression, hclass]
  rw [smoothProfile_progression_eq_tsum m u hV ψ _ hneg
    (fun _ hv => profileS2Carrier_support ψ hψ hV hv)]
  change (∑' h, f h) = _
  rw [hsplit]
  have hzero : f 0 = profileS2ZeroMode ψ V m := by
    simp [f, profileS2ZeroMode]
  rw [hzero]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · rw [if_pos hh, retainedS2Mode, if_pos hh]
  · simp only [retainedS2Mode, if_neg hh, f, hphase]

end

end ImbalancedChen.Part3.E1Finite
