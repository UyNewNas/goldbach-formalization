import ImbalancedChen.Part3GevreyCutoff
import ImbalancedChen.Part3E1FixedDSource

/-!
# The omitted nonzero modes of one S2 cell

The infinite mode sum and the finite E1 carrier use the same compact
Gevrey cutoff and the same physical mesh.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Filter Finset
open scoped BigOperators FourierTransform SchwartzMap
open GevreyCutoff
open OriginalSmoothPoissonTail (inverseResidue)

private theorem mem_e1NonzeroFrequencies_floor {H : ℝ} (hH : 0 ≤ H) {h : ℤ} :
    h ∈ e1NonzeroFrequencies ⌊H⌋₊ ↔ h ≠ 0 ∧ |(h : ℝ)| ≤ H := by
  have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [e1NonzeroFrequencies, mem_erase, mem_Icc, ← abs_le, Int.abs_eq_natAbs,
    habs, ← Nat.le_floor_iff hH]
  norm_cast

/-- The compact-cutoff Fourier coefficient at the physical mesh,
with its phase and the zero mode removed. -/
def sameCutoffMode (t : ℝ) (phase : ℤ → ℂ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else t • (𝓕 cutoffSchwartz) (t * (h : ℝ)) * phase h

/-- The threshold is uniform over every positive mesh, every sufficiently
wide retained window, and every phase of modulus at most one. -/
theorem sameCutoffMode_tail (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ t H : ℝ, 0 < t → 0 ≤ H → Real.log X ^ 5 ≤ t * H →
      ∀ phase : ℤ → ℂ, (∀ h, ‖phase h‖ ≤ 1) →
        Summable (fun h => ‖sameCutoffMode t phase h‖) ∧
          ‖(∑' h : ℤ, sameCutoffMode t phase h) -
            ∑ h ∈ e1NonzeroFrequencies ⌊H⌋₊, sameCutoffMode t phase h‖ ≤
            8 * X ^ (-(K : ℝ)) := by
  filter_upwards [cutoff_fourier_log_five_tail K] with X hX t H ht hH hwidth phase hphase
  obtain ⟨hsTail, hTail⟩ := hX t ht H hwidth
  let S := e1NonzeroFrequencies ⌊H⌋₊
  let f := sameCutoffMode t phase
  let g (h : ℤ) := if h ∈ S then f h else 0
  let r (h : ℤ) := if h ∈ S then 0 else f h
  have hf (h : ℤ) : f h = g h + r h := by
    by_cases hh : h ∈ S <;> simp [g, r, hh]
  have hr (h : ℤ) : ‖r h‖ ≤ cutoffFourierTail t H h := by
    rw [cutoffFourierTail_eq_schwartz]
    by_cases hhH : H < |(h : ℝ)|
    · rw [if_pos hhH]
      have h0 : h ≠ 0 := by
        rintro rfl
        simp at hhH
        exact (not_lt_of_ge hH) hhH
      have hhS : h ∉ S := fun hh =>
        (not_le_of_gt hhH) ((mem_e1NonzeroFrequencies_floor hH).mp hh).2
      simp only [r, if_neg hhS, f, sameCutoffMode, if_neg h0, norm_mul, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_of_le_one_right (by positivity) (hphase _)
    · rw [if_neg hhH]
      by_cases h0 : h = 0
      · simp [r, f, sameCutoffMode, h0]
      · have hhS : h ∈ S := (mem_e1NonzeroFrequencies_floor hH).mpr ⟨h0, le_of_not_gt hhH⟩
        simp [r, hhS]
  have hrs : Summable (fun h => ‖r h‖) :=
    hsTail.of_nonneg_of_le (fun _ => norm_nonneg _) hr
  have hgs : Summable (fun h => ‖g h‖) :=
    summable_of_ne_finset_zero (s := S) (fun h hh => by simp [g, hh])
  have hfs : Summable (fun h => ‖f h‖) :=
    (hgs.add hrs).of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => by
      rw [hf h]
      exact norm_add_le _ _)
  have hg : ∑' h, g h = ∑ h ∈ S, f h := by
    rw [tsum_eq_sum (s := S) (fun h hh => by simp [g, hh])]
    exact sum_congr rfl (fun h hh => if_pos hh)
  refine ⟨hfs, ?_⟩
  change ‖(∑' h, f h) - ∑ h ∈ S, f h‖ ≤ _
  have hsplit : (∑' h, f h) = (∑' h, g h) + ∑' h, r h := by
    simpa only [hf] using hgs.of_norm.tsum_add hrs.of_norm
  rw [hsplit, hg, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hrs).trans ((hrs.tsum_le_tsum hr hsTail).trans hTail)

/-- The exact inverse-residue character of the S2 cell satisfies the
same cutoff estimate at the mesh `V / (q*d*r)`. -/
theorem retainedS2Mode_sameCutoff_tail (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (V H : ℝ) (a : ℤ) (q d r n : ℕ),
      0 < V → 0 < q → 0 < d → 0 < r → 0 ≤ H →
      Real.log X ^ 5 ≤ V / ((q * d * r : ℕ) : ℝ) * H →
        Summable (fun h => ‖retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h‖) ∧
          ‖(∑' h : ℤ, retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h) -
            ∑ h ∈ e1NonzeroFrequencies ⌊H⌋₊,
              retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h‖ ≤
            8 * X ^ (-(K : ℝ)) := by
  filter_upwards [sameCutoffMode_tail K] with X hX V H a q d r n hV hq hd hr hH hwidth
  let m := q * d * r
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos hq hd) hr
  have ht : 0 < V / (m : ℝ) := div_pos hV (Nat.cast_pos.mpr hm)
  let phase (h : ℤ) : ℂ :=
    fourier h ((((a * inverseResidue m (n : ℤ) : ℤ) : ℝ) / (m : ℝ)) : UnitAddCircle)
  have hphase (h : ℤ) : ‖phase h‖ ≤ 1 := by
    simp only [phase, fourier_apply, Circle.norm_coe, le_refl]
  exact hX (V / (m : ℝ)) H ht hH hwidth phase hphase

/-- A common retained window for the supported smooth q carrier and
closed dyadic d and r windows meets every physical mesh condition. -/
theorem sameCutoffMode_medium_mesh {X V Q₁ D R H : ℝ} {q d r : ℕ}
    (hX : 1 ≤ X) (hV : 0 < V) (hq : 0 < q) (hd : 0 < d) (hr : 0 < r)
    (hqHi : (q : ℝ) ≤ 5 * Q₁ / 2) (hdHi : (d : ℝ) ≤ 2 * D) (hrHi : (r : ℝ) ≤ 2 * R)
    (hH : 10 * Real.log X ^ 5 * (D * Q₁ * R / V) ≤ H) :
    0 ≤ H ∧ Real.log X ^ 5 ≤ V / ((q * d * r : ℕ) : ℝ) * H := by
  have hq₀ : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hd₀ : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hr₀ : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hQ₁ : 0 < Q₁ := by linarith
  have hD : 0 < D := by linarith
  have hR : 0 < R := by linarith
  have hlog := Real.log_nonneg hX
  have hmod : ((q * d * r : ℕ) : ℝ) ≤ 10 * (D * Q₁ * R) := by
    push_cast
    calc
      (q : ℝ) * d * r ≤ (5 * Q₁ / 2) * (2 * D) * (2 * R) := by gcongr
      _ = _ := by ring
  refine ⟨(by positivity : 0 ≤ 10 * Real.log X ^ 5 * (D * Q₁ * R / V)).trans hH, ?_⟩
  calc
    Real.log X ^ 5 = V / ((q * d * r : ℕ) : ℝ) *
        (Real.log X ^ 5 * (((q * d * r : ℕ) : ℝ) / V)) := by
      have hmod₀ : (0 : ℝ) < ((q * d * r : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos hq hd) hr)
      field_simp
    _ ≤ V / ((q * d * r : ℕ) : ℝ) *
        (Real.log X ^ 5 * ((10 * (D * Q₁ * R)) / V)) := by gcongr
    _ = V / ((q * d * r : ℕ) : ℝ) *
        (10 * Real.log X ^ 5 * (D * Q₁ * R / V)) := by ring
    _ ≤ _ := by gcongr

end

end ImbalancedChen.Part3.E1Finite
