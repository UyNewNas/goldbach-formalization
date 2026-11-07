import ImbalancedChen.ActualNormalizedRhoError

/-!
# P4A: exact invariance under covering enumeration caps

The existing membership API removes a covering cap from the prime
predicate. This module first upgrades it to equality of the actual sorted
lists, then transports that equality through the actual retained policy
and the actual small Rosser weights. The scan order is preserved exactly.

The resulting limit transport changes only the enumeration cap. It does
not replace the policy, supply its signed density limit, or assert K.

SOURCE ONLY; no compilation was performed.
-/

namespace ImbalancedChen.P4ACoveringCapInvariance

noncomputable section

open Filter Topology

theorem roughPrimeFinset_eq_of_cover {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    roughPrimeFinset N cap₁ w z = roughPrimeFinset N cap₂ w z := by
  ext p
  rw [mem_roughPrimeFinset_iff_of_cutoff_le_cap h₁,
    mem_roughPrimeFinset_iff_of_cutoff_le_cap h₂]

/-- Equality is of the decreasing lists, not just of their memberships. -/
theorem roughPrimeUniverse_eq_of_cover {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    roughPrimeUniverse N cap₁ w z = roughPrimeUniverse N cap₂ w z := by
  unfold roughPrimeUniverse
  rw [roughPrimeFinset_eq_of_cover h₁ h₂]

theorem fixedRoughSupport_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    fixedRoughSupport retainOdd N cap₁ w z =
      fixedRoughSupport retainOdd N cap₂ w z := by
  unfold fixedRoughSupport
  rw [roughPrimeUniverse_eq_of_cover h₁ h₂]

/-- The same causal policy on the same ordered prime list gives the same
coefficient function on every modulus, including outside the support. -/
theorem fixedRoughCoefficient_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    fixedRoughCoefficient retainOdd N cap₁ w z =
      fixedRoughCoefficient retainOdd N cap₂ w z := by
  funext d
  unfold fixedRoughCoefficient
  rw [roughPrimeUniverse_eq_of_cover h₁ h₂]

theorem actualSmallPrimeFinset_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallPrimeFinset N cap₁ w = actualSmallPrimeFinset N cap₂ w := by
  unfold actualSmallPrimeFinset
  exact roughPrimeFinset_eq_of_cover h₁ h₂

theorem actualSmallPrimeProduct_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallPrimeProduct N cap₁ w = actualSmallPrimeProduct N cap₂ w := by
  unfold actualSmallPrimeProduct
  rw [actualSmallPrimeFinset_eq_of_cover h₁ h₂]

theorem actualSmallRosserSupport_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallRosserSupport N cap₁ w = actualSmallRosserSupport N cap₂ w := by
  unfold actualSmallRosserSupport
  rw [actualSmallPrimeProduct_eq_of_cover h₁ h₂]

theorem actualSmallRosserMinus_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (L : ℝ) (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallRosserMinus N cap₁ w L = actualSmallRosserMinus N cap₂ w L := by
  unfold actualSmallRosserMinus
  rw [actualSmallPrimeProduct_eq_of_cover h₁ h₂]

theorem actualSmallRosserPlus_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (L : ℝ) (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallRosserPlus N cap₁ w L = actualSmallRosserPlus N cap₂ w L := by
  unfold actualSmallRosserPlus
  rw [actualSmallPrimeProduct_eq_of_cover h₁ h₂]

theorem actualSmallEulerProduct_eq_of_cover {N cap₁ cap₂ : ℕ} {w : ℝ}
    (h₁ : w ≤ (cap₁ : ℝ)) (h₂ : w ≤ (cap₂ : ℝ)) :
    actualSmallEulerProduct N cap₁ w = actualSmallEulerProduct N cap₂ w := by
  unfold actualSmallEulerProduct
  rw [actualSmallPrimeFinset_eq_of_cover h₁ h₂]

/-- Covering z covers the small cutoff w as well. -/
theorem actualSmallRoughModuli_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (hwz : w ≤ z) (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    actualSmallRoughModuli retainOdd N cap₁ w z =
      actualSmallRoughModuli retainOdd N cap₂ w z := by
  unfold actualSmallRoughModuli
  rw [actualSmallRosserSupport_eq_of_cover (hwz.trans h₁) (hwz.trans h₂),
    fixedRoughSupport_eq_of_cover retainOdd h₁ h₂]

/-- The complete physical coefficient is exactly cap independent when
both caps cover z and w≤z. The small level L is identical on both sides. -/
theorem actualSmallRoughRho_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (L : ℝ) (hwz : w ≤ z)
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    actualSmallRoughRho retainOdd N cap₁ w z L =
      actualSmallRoughRho retainOdd N cap₂ w z L := by
  unfold actualSmallRoughRho
  rw [actualSmallRosserSupport_eq_of_cover (hwz.trans h₁) (hwz.trans h₂),
    fixedRoughSupport_eq_of_cover retainOdd h₁ h₂,
    fixedRoughCoefficient_eq_of_cover retainOdd h₁ h₂,
    actualSmallRosserMinus_eq_of_cover L (hwz.trans h₁) (hwz.trans h₂),
    actualSmallRosserPlus_eq_of_cover L (hwz.trans h₁) (hwz.trans h₂)]

theorem signedRoughDensity_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    reciprocalTotientDensity (fixedRoughSupport retainOdd N cap₁ w z)
        (fixedRoughCoefficient retainOdd N cap₁ w z) =
      reciprocalTotientDensity (fixedRoughSupport retainOdd N cap₂ w z)
        (fixedRoughCoefficient retainOdd N cap₂ w z) := by
  rw [fixedRoughSupport_eq_of_cover retainOdd h₁ h₂,
    fixedRoughCoefficient_eq_of_cover retainOdd h₁ h₂]

theorem physicalDensity_eq_of_cover
    (retainOdd : List ℕ → Bool) {N cap₁ cap₂ : ℕ} {w z : ℝ}
    (L : ℝ) (hwz : w ≤ z)
    (h₁ : z ≤ (cap₁ : ℝ)) (h₂ : z ≤ (cap₂ : ℝ)) :
    physicalDensitySum (actualSmallRoughModuli retainOdd N cap₁ w z)
        (actualSmallRoughRho retainOdd N cap₁ w z L) =
      physicalDensitySum (actualSmallRoughModuli retainOdd N cap₂ w z)
        (actualSmallRoughRho retainOdd N cap₂ w z L) := by
  rw [actualSmallRoughModuli_eq_of_cover retainOdd hwz h₁ h₂,
    actualSmallRoughRho_eq_of_cover retainOdd L hwz h₁ h₂]

/-- Transport an existing same-policy normalized signed limit from cap=N
to any eventually covering cap. No analytic limit is manufactured here. -/
theorem tendsto_signedRoughDensity_covering_cap
    (retainOdd : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (w z : ℕ → ℝ) (I : ℝ)
    (hdiag : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      z N ≤ (N : ℝ))
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      z N ≤ (cap N : ℝ))
    (hlim : Tendsto (fun N : ℕ =>
      reciprocalTotientDensity (fixedRoughSupport (retainOdd N) N N (w N) (z N))
          (fixedRoughCoefficient (retainOdd N) N N (w N) (z N)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I)) :
    Tendsto (fun N : ℕ =>
      reciprocalTotientDensity
          (fixedRoughSupport (retainOdd N) N (cap N) (w N) (z N))
          (fixedRoughCoefficient (retainOdd N) N (cap N) (w N) (z N)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I) := by
  apply hlim.congr'
  filter_upwards [hdiag, hcap] with N hdiagN hcapN
  rw [signedRoughDensity_eq_of_cover (retainOdd N) hcapN hdiagN]

/-- The same cap transport applies to the complete physical rho. -/
theorem tendsto_physicalDensity_covering_cap
    (retainOdd : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (w z L : ℕ → ℝ) (I : ℝ)
    (hwz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      w N ≤ z N)
    (hdiag : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      z N ≤ (N : ℝ))
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      z N ≤ (cap N : ℝ))
    (hlim : Tendsto (fun N : ℕ =>
      physicalDensitySum
          (actualSmallRoughModuli (retainOdd N) N N (w N) (z N))
          (actualSmallRoughRho (retainOdd N) N N (w N) (z N) (L N)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I)) :
    Tendsto (fun N : ℕ =>
      physicalDensitySum
          (actualSmallRoughModuli (retainOdd N) N (cap N) (w N) (z N))
          (actualSmallRoughRho (retainOdd N) N (cap N) (w N) (z N) (L N)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I) := by
  apply hlim.congr'
  filter_upwards [hwz, hdiag, hcap] with N hwzN hdiagN hcapN
  rw [physicalDensity_eq_of_cover (retainOdd N) (L N) hwzN hcapN hdiagN]

/-- A power cutoff with exponent at most one is eventually covered by the
diagonal cap N. This discharges the cap=N side in the manuscript range. -/
theorem eventually_power_cutoff_le_diagonal (u : ℝ) (hu : u ≤ 1) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (N : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      1 ≤ N := (eventually_ge_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN' hu

/-- Direct cap=N to covering-cap interface for the full signed policy
density at z=N^u, without a separate diagonal-coverage hypothesis. -/
theorem tendsto_signed_power_density_covering_cap
    (retainOdd : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (u I : ℝ) (hu : u ≤ 1)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ))
    (hlim : Tendsto (fun N : ℕ =>
      reciprocalTotientDensity
          (fixedRoughSupport (retainOdd N) N N 0 ((N : ℝ) ^ u))
          (fixedRoughCoefficient (retainOdd N) N N 0 ((N : ℝ) ^ u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I)) :
    Tendsto (fun N : ℕ =>
      reciprocalTotientDensity
          (fixedRoughSupport (retainOdd N) N (cap N) 0 ((N : ℝ) ^ u))
          (fixedRoughCoefficient (retainOdd N) N (cap N) 0 ((N : ℝ) ^ u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 I) := by
  exact tendsto_signedRoughDensity_covering_cap retainOdd cap
    (fun _ => 0) (fun N => (N : ℝ) ^ u) I
    (eventually_power_cutoff_le_diagonal u hu) hcap hlim

end
end ImbalancedChen.P4ACoveringCapInvariance
