import ImbalancedChen.Part3E1SameCutoffTail
import ImbalancedChen.Part3E1ProfileS2Progression

/-!
# The physical one-congruence S2 progression

The natural sample sum, the zero mode and the full signed Fourier series
are computed with the same compact Gevrey profile.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Filter Finset
open scoped BigOperators FourierTransform SchwartzMap
open GevreyCutoff

private theorem cutoffSchwartz_support ⦃x : ℝ⦄ (hx : cutoffSchwartz x ≠ 0) :
    x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
  have hcutoff : cutoff x ≠ 0 := by
    intro h
    exact hx (by simp [complexCutoff, h])
  exact cutoff_tsupport_subset (subset_tsupport _ hcutoff)

theorem sameCutoffS2Carrier_support {V : ℝ} (hV : 0 < V) {v : ℕ}
    (hv : cutoffSchwartz ((v : ℝ) / V) ≠ 0) : v ∈ sameCutoffS2Carrier V :=
  profileS2Carrier_support cutoffSchwartz cutoffSchwartz_support hV hv

/-- The original multiplicative congruence on the natural sample carrier. -/
def physicalSameCutoffS2Progression (V : ℝ) (a : ℤ) (m n : ℕ) : ℂ :=
  physicalProfileS2Progression cutoffSchwartz V a m n

/-- The exact zero Fourier coefficient at the left physical modulus. -/
def sameCutoffS2ZeroMode (V : ℝ) (m : ℕ) : ℂ :=
  profileS2ZeroMode cutoffSchwartz V m

/-- For a primitive sample multiplier, the original congruence has the
exact inverse-residue zero mode and complete nonzero signed series. -/
theorem physicalSameCutoffS2Progression_eq_zero_add_nonzero {V : ℝ} (hV : 0 < V)
    (a : ℤ) {m n : ℕ} (hm : 0 < m) (hn : n.Coprime m) :
    physicalSameCutoffS2Progression V a m n =
      sameCutoffS2ZeroMode V m +
        ∑' h : ℤ, retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a m n h :=
  physicalProfileS2Progression_eq_zero_add_nonzero cutoffSchwartz cutoffSchwartz_support hV a hm hn

/-- At the mesh from the same left modulus, the natural progression minus
its exact zero mode is approximated by the retained S2 frequencies. -/
theorem physicalSameCutoffS2Progression_retained_bound (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (V H : ℝ) (a : ℤ) (q d r n : ℕ),
      0 < V → 0 < q → 0 < d → 0 < r → 0 ≤ H → n.Coprime (q * d * r) →
      Real.log X ^ 5 ≤ V / ((q * d * r : ℕ) : ℝ) * H →
        ‖physicalSameCutoffS2Progression V a (q * d * r) n - sameCutoffS2ZeroMode V (q * d * r) -
          ∑ h ∈ e1NonzeroFrequencies ⌊H⌋₊,
            retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h‖ ≤
            8 * X ^ (-(K : ℝ)) := by
  filter_upwards [retainedS2Mode_sameCutoff_tail K] with X hX V H a q d r n
    hV hq hd hr hH hn hwidth
  rw [physicalSameCutoffS2Progression_eq_zero_add_nonzero hV a
    (Nat.mul_pos (Nat.mul_pos hq hd) hr) hn, add_sub_cancel_left]
  exact (hX V H a q d r n hV hq hd hr hH hwidth).2

/-- The physical fibre retains the two independent primitive gates,
the original prefactor, and the right totient divisor. -/
def physicalSameCutoffS2Fibre (V : ℝ) (a : ℤ) (q d r s n n' : ℕ) (c : ℂ) : ℂ :=
  if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
    c * physicalSameCutoffS2Progression V a (q * d * r) n / ((q * d * s).totient : ℂ)
  else 0

/-- Both terms in the Poisson decomposition have the original prefactor
and both primitive gates on the tagged fibre. -/
theorem physicalSameCutoffS2Fibre_eq_zero_add_nonzero {V : ℝ} (hV : 0 < V)
    (a : ℤ) (q d r s n n' : ℕ) (c : ℂ) (hm : 0 < q * d * r) :
    physicalSameCutoffS2Fibre V a q d r s n n' c =
      (if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
        c * sameCutoffS2ZeroMode V (q * d * r) / ((q * d * s).totient : ℂ)
      else 0) +
      (if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
        c * (∑' h : ℤ, retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h) /
          ((q * d * s).totient : ℂ)
      else 0) := by
  unfold physicalSameCutoffS2Fibre
  split_ifs with hg
  · rw [physicalSameCutoffS2Progression_eq_zero_add_nonzero hV a hm hg.1, mul_add, add_div]
  · simp

end

end ImbalancedChen.Part3.E1Finite
