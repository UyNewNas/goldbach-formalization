import ImbalancedChen.Part3PoincareOrbitalDilation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

A real actual orbital identity beyond formal notation: x=y*u dilation,
reflection u -> -u, and cancellation of the odd oscillation reduce each
literal compact-cusp orbital integral to an exact cosine radial kernel.
The original quotient L2 pairing is then expressed with this explicit
kernel. Every slice integral used in the reflection is proved L1 from
the actual compact kernels. No Bessel transform is asserted without the
missing Whittaker/Weber product-integral identification.
-/

namespace ImbalancedChen.Part3.PoincareOrbitalCosine20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.PoincareOrbitalDilation20261026a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.CompactCuspQuotientGeometricPairing20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

/-- The actual cosine orbital kernel retains both radial profiles,
the actual frequency pair, and the exact canonical dy/y measure. -/
def cosineOrbitalKernel (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2⁻¹ : ℂ) * star (ψ p.2) *
    Complex.cos (orbitalPhase c m n p.2 p.1 : ℂ) * φ (orbitalHeight c p.2 p.1)

private theorem phase_continuous (m : ℤ) : Continuous (phase m) :=
  (map_continuous (AddCircle.fourier m)).comp continuous_quotient_mk'

/-- Actual x-slice L1, including the zero extension at nonpositive height. -/
theorem geometricPairKernel_slice_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (y : ℝ) : Integrable (fun x => geometricPairKernel c m n ψ φ (x, y)) := by
  by_cases hy : 0 < y
  · have hbase := ((phase_continuous (-m)).mul (actualKernel_continuous c hc y hy n φ hφ)).integrable_of_hasCompactSupport
      (actualKernel_hasCompactSupport c hc y hy n φ hcφ hposφ).mul_left
    apply (hbase.const_mul (radialWeight ψ y)).congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [geometricPairKernel, rawBruhatKernel_eq_actual, mul_assoc]
  · have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hy (hposψ hm))
    simp only [geometricPairKernel, radialWeight, hz, star_zero, mul_zero, zero_mul]
    exact integrable_zero _ _ _

/-- The explicit dimensionless phase integral is absolutely convergent at
every height, before reflection is used. -/
theorem explicitOrbitalKernel_slice_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (y : ℝ) : Integrable (fun u => explicitOrbitalKernel c m n ψ φ (u, y)) := by
  rw [← dilatedOrbitalKernel_eq_explicit_all c hc m n ψ φ hposψ]
  by_cases hy : 0 < y
  · exact ((geometricPairKernel_slice_integrable c hc m n ψ φ hposψ hφ hcφ hposφ y).comp_mul_left' hy.ne').const_mul (y : ℂ)
  · have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hy (hposψ hm))
    simp only [dilatedOrbitalKernel, geometricPairKernel, radialWeight, hz, star_zero, mul_zero, zero_mul]
    exact integrable_zero _ _ _

theorem orbitalHeight_neg (c y u : ℝ) : orbitalHeight c y (-u) = orbitalHeight c y u := by
  simp only [orbitalHeight, neg_sq]

theorem orbitalPhase_neg (c : ℝ) (m n : ℤ) (y u : ℝ) :
    orbitalPhase c m n y (-u) = -orbitalPhase c m n y u := by
  simp only [orbitalPhase, orbitalHeight_neg]
  ring

/-- Reflection is an exact identity of the ACTUAL orbital phases. -/
theorem orbital_phase_pair (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ) (y u : ℝ) :
    explicitOrbitalKernel c m n ψ φ (u, y) + explicitOrbitalKernel c m n ψ φ (-u, y) =
      (2 : ℂ) * cosineOrbitalKernel c m n ψ φ (u, y) := by
  have hpos : -Complex.I * ((-orbitalPhase c m n y u : ℝ) : ℂ) =
      (orbitalPhase c m n y u : ℂ) * Complex.I := by push_cast; ring
  have hneg : -Complex.I * (orbitalPhase c m n y u : ℂ) =
      (-(orbitalPhase c m n y u : ℂ)) * Complex.I := by ring
  simp only [explicitOrbitalKernel, orbitalPhase_neg, orbitalHeight_neg]
  rw [hpos, hneg]
  calc
    _ = (y⁻¹ : ℂ) * star (ψ y) *
        (Complex.exp ((orbitalPhase c m n y u : ℂ) * Complex.I) +
          Complex.exp (-(orbitalPhase c m n y u : ℂ) * Complex.I)) *
            φ (orbitalHeight c y u) := by ring
    _ = _ := by rw [← Complex.two_cos]; unfold cosineOrbitalKernel; ring

/-- Reflection on the full Fourier line does not introduce a factor two:
the cosine kernel is integrated over the full u-line as well. -/
theorem orbital_integral_eq_cosine (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (y : ℝ) :
    (∫ u : ℝ, explicitOrbitalKernel c m n ψ φ (u, y)) =
      ∫ u : ℝ, cosineOrbitalKernel c m n ψ φ (u, y) := by
  have he := explicitOrbitalKernel_slice_integrable c hc m n ψ φ hposψ hφ hcφ hposφ y
  have hn : Integrable (fun u => explicitOrbitalKernel c m n ψ φ (-u, y)) := by
    simpa only [neg_one_mul] using he.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have href : (∫ u : ℝ, explicitOrbitalKernel c m n ψ φ (-u, y)) =
      ∫ u : ℝ, explicitOrbitalKernel c m n ψ φ (u, y) := by
    simpa using Measure.integral_comp_mul_left (fun u => explicitOrbitalKernel c m n ψ φ (u, y)) (-1)
  have hpoint : (fun u => cosineOrbitalKernel c m n ψ φ (u, y)) =
      fun u => (1 / 2 : ℂ) *
        (explicitOrbitalKernel c m n ψ φ (u, y) + explicitOrbitalKernel c m n ψ φ (-u, y)) := by
    funext u
    rw [orbital_phase_pair]
    ring
  rw [hpoint, integral_const_mul, integral_add he hn, href]
  ring

/-- The actual double-coset Archimedean integral equals the fully explicit
cosine radial integral. This is a proved integral identity, with compact
supports and L1 supplying the exchanges. -/
theorem actual_orbital_eq_cosine (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, ∫ y : ℝ, geometricPairKernel c m n ψ φ (x, y)) =
      ∫ y : ℝ, ∫ u : ℝ, cosineOrbitalKernel c m n ψ φ (u, y) := by
  rw [actual_orbital_eq_explicit_dimensionless c hc m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (orbital_integral_eq_cosine c hc m n ψ φ hposψ hφ hcφ hposφ))

/-- Actual compact-cusp quotient pairing with the derived explicit
Archimedean cosine orbital kernel. This is geometric and does not claim
a J_{2it}/K_{2it} transform or any spectral expansion. -/
theorem compactCuspPoincareL2_inner_eq_finite_cosine_orbitals (N : ℕ) [NeZero N]
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      inner ℂ (compactCuspPoincareL2 N m ψ hψ hcψ hposψ)
        (compactCuspPoincareL2 N n φ hφ hcφ hposφ) =
      (if m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then kloosterman (c : ℕ) m n *
          ∫ y : ℝ, ∫ u : ℝ, cosineOrbitalKernel (c : ℝ) m n ψ φ (u, y)
        else 0 := by
  obtain ⟨C, hC⟩ := compactCuspPoincareL2_inner_eq_finite_geometric N m n ψ φ
    hψ hcψ hposψ hφ hcφ hposφ
  refine ⟨C, hC.trans ?_⟩
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hNc : N ∣ (c : ℕ)
  · simp only [if_pos hNc]
    rw [actual_orbital_eq_cosine (c : ℝ) (by exact_mod_cast (Nat.ne_of_gt c.property))
      m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  · simp only [if_neg hNc]

end
end ImbalancedChen.Part3.PoincareOrbitalCosine20261026a
