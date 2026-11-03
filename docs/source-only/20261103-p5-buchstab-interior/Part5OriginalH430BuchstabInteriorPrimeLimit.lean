import ImbalancedChen.Part5OriginalH430CompactParameterGates
import ImbalancedChen.P2OriginalCompactThetaMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine prime-sum limit for the full Buchstab normalized range
[1/6,1/2], uniform simultaneously in the residual exponent and both
moving endpoints. The two endpoints may coincide or be reversed.
The integer target remains N. Actual target-deleted prime carriers and
the exact fresh/repeated-prefix singular factors are retained.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabInteriorPrimeLimit

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology Pointwise
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactScaledPrimeMass P2OriginalCompactThetaMass
open Part5OriginalH430CompactParameterGates

abbrev Parameters := ℝ × ℝ × ℝ

def parameterBox (Lmin Lmax : ℝ) : Set Parameters :=
  Icc Lmin Lmax ×ˢ (Icc (1/6:ℝ) (1/2) ×ˢ Icc (1/6:ℝ) (1/2))

def movingBounds (t : Parameters) (j : Fin 2) : ℝ :=
  t.1 * singleBounds t.2.1 t.2.2 j

def movingKernel (Lmin : ℝ) (q : Parameters × Coord 1) : ℝ :=
  dilationKernel Lmin residualSingle (q.1.1,q.2)

def intervalIntegral (lo hi : ℝ) : ℝ :=
  ∫ u in Ioo lo hi, 1/(u*(1-u))

theorem parameterBox_compact (Lmin Lmax : ℝ) : IsCompact (parameterBox Lmin Lmax) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem movingBounds_continuous (j : Fin 2) : Continuous (fun t => movingBounds t j) := by
  fin_cases j <;> simp only [movingBounds, singleBounds, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

theorem movingKernel_continuous {Lmin : ℝ} (hmin : 0 < Lmin) :
    Continuous (movingKernel Lmin) :=
  (dilationKernel_continuous hmin residualSingle residualSingle_continuous).comp
    ((continuous_fst.fst).prodMk continuous_snd)

theorem movingKernel_bound (Lmin : ℝ) (q : Parameters × Coord 1) :
    |movingKernel Lmin q| ≤ 10 := by
  change |residualSingle ((max (Lmin/2) q.1.1)⁻¹ • q.2)| ≤ 10
  rw [abs_of_nonneg (residualSingle_bounds _).1]
  exact (residualSingle_bounds _).2

/-- The enlarged original enumeration already contains this entire
range. Only the old W1/W2 convenience lemma had a 1/5 restriction. -/
theorem single_in_cube_sixth {lo hi : ℝ}
    (hlo : (1/6:ℝ) ≤ lo) (hhi : hi ≤ 1/2) : singleDomain lo hi ⊆ cube 1 := by
  intro x hx
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  change lo < x 0 ∧ x 0 < hi at hx
  constructor <;> linarith

theorem single_integral_eq (lo hi : ℝ) (hhi : hi ≤ 1/2) :
    (∫ x in singleDomain lo hi, residualSingle x*(∏ i, 1/x i)) =
      intervalIntegral lo hi := by
  calc
    _ = ∫ x in singleDomain lo hi, 1/(x 0*(1-x 0)) := by
      apply setIntegral_congr_fun
      · rw [single_as_affine]
        exact measurableSet_primeAffineGateRegion _ _
      · intro x hx
        exact single_kernel hhi hx
    _ = _ := single_integral_coordinates lo hi (fun u => 1/(u*(1-u)))

/-- One threshold precedes all three real parameters. In particular
this is NOT a fixed-window theorem reused at an N-dependent window. -/
theorem compact_uniform_scaled_openInterval {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ lo ∈ Icc (1/6:ℝ) (1/2), ∀ hi ∈ Icc (1/6:ℝ) (1/2),
      |scaledPrimeSum N L (singleDomain lo hi) residualSingle-
        intervalIntegral lo hi| < epsilon := by
  obtain ⟨T,hT⟩ := compact_uniform_parameter_gates
    (parameterBox_compact Lmin Lmax)
    (a := Lmin/20) (b := Lmax) (by positivity) (by linarith)
    (by norm_num : (0:ℝ) ≤ 10) singleForms singleForms_ne
    movingBounds movingBounds_continuous
    (movingKernel Lmin) (movingKernel_continuous hmin)
    (fun t ht x hx => movingKernel_bound Lmin (t,x)) he
  refine ⟨max 2 T, ?_⟩
  intro N hN L hL lo hlo hi hhi
  have hN1 : 1 < N := by omega
  have hL0 : 0 < L := hmin.trans_le hL.1
  have hD : primeAffineGateRegion singleForms (singleBounds lo hi) ⊆ cube 1 := by
    rw [← single_as_affine]
    exact single_in_cube_sixth hlo.1 hhi.2
  have hh := hT N (by omega) (L,lo,hi) ⟨hL,hlo,hhi⟩
  change |actualPrimeBoxTestSum N (fun _ : Fin 1 => Lmin/20) (fun _ => Lmax)
      ((primeAffineGateRegion singleForms (fun j => L*singleBounds lo hi j)).indicator
        (fun x => dilationKernel Lmin residualSingle (L,x)))-
      (∫ x in logPrimeBox (fun _ : Fin 1 => Lmin/20) (fun _ => Lmax) ∩
        primeAffineGateRegion singleForms (fun j => L*singleBounds lo hi j),
        dilationKernel Lmin residualSingle (L,x)*(∏ i,1/x i))| < epsilon at hh
  simp_rw [dilationKernel_on_interval hmin hL] at hh
  rw [← scaledPrimeSum_eq_ambient hN1 hmin hL singleForms (singleBounds lo hi)
      hD residualSingle,
    ambient_region_eq_dilation hmin hL singleForms (singleBounds lo hi) hD,
    integral_log_density_dilation hL0,
    ← single_as_affine, single_integral_eq lo hi hhi.2] at hh
  exact hh

/-- Exact localPrimeFactor is retained on all N-deleted prime lanes,
including primes already dividing the old prefix. -/
theorem compact_uniform_true_openInterval {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ lo ∈ Icc (1/6:ℝ) (1/2), ∀ hi ∈ Icc (1/6:ℝ) (1/2), ∀ d : ℕ,
      |trueSingleMass N L d lo hi-intervalIntegral lo hi| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_scaled_openInterval hmin hmax
    (by positivity : 0 < epsilon/2)
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k := 1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 20) (by positivity : 0 < epsilon/2)
  refine ⟨max Tp Te, ?_⟩
  intro N hN L hL lo hlo hi hhi d
  have hp := hTp N (by omega) L hL lo hlo hi hhi
  obtain ⟨hA,he'⟩ := hTe N (by omega) L hL
  have hd := single_mass_difference d lo hi hA
  have ht := abs_sub_le (trueSingleMass N L d lo hi)
    (scaledPrimeSum N L (singleDomain lo hi) residualSingle) (intervalIntegral lo hi)
  linarith

end
end ImbalancedChen.Part5OriginalH430BuchstabInteriorPrimeLimit
