import ImbalancedChen.ActualUpperDensityAssembly
import ImbalancedChen.SmallRosserErrorLimit

/-!
# A proved density reserve for the actual small-weight attachment

The abstract compiler transport requests absolute bounds for both small
Rosser densities. Here those two inputs are supplied by the actual
fundamental-lemma sandwich. The compiled and raw rough coefficients use
the identical small weights, rough carrier, and physical modulus carrier.
Only their literal absolute coefficient difference is charged.

The result does not assert a bound for a manuscript box compiler, its
support, or its signed distribution error.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology

/-- The actual density sandwich controls both slopes, including when the
lower Rosser density is negative. No positivity of that lower density is
assumed. -/
private theorem abs_slopes_le_of_density_sandwich
    {V E lo hi : ℝ} (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hlo : V * (1 - E) ≤ lo) (hloUpper : lo ≤ V)
    (hhiLower : V ≤ hi) (hhi : hi ≤ V * (1 + E)) :
    |lo| ≤ V * (1 + E) ∧ |hi| ≤ V * (1 + E) := by
  have hVE : 0 ≤ V * E := mul_nonneg hV hE
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith
  · rw [abs_of_nonneg (hV.trans hhiLower)]
    exact hhi

/-- A common pair of absolute constants supplies the concrete compiler
density slope. The threshold precedes every even target, enumeration cap,
rough carrier and pair of rough coefficients. -/
theorem exists_actualCompiledRho_density_difference_bound :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, Even N → ∀ rough : Finset ℕ,
            (∀ d ∈ rough, RoughPrimeSupportedAt (D ^ (epsilon ^ 2)) d) →
              ∀ compiled raw : ℕ → ℝ,
                let w := D ^ (epsilon ^ 2)
                let L := D ^ epsilon
                let small := actualSmallRosserSupport N cap w
                let density := fun c => physicalDensitySum (smallRoughModuli small rough)
                  (smallRoughRho small rough c (actualSmallRosserMinus N cap w L)
                    (actualSmallRosserPlus N cap w L))
                |density compiled - density raw| ≤
                  (actualSmallEulerProduct N cap w *
                    (1 + actualSmallRosserDensityError C K D epsilon)) *
                      reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D₀, hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hEven rough hrough compiled raw
  have h := hsupply D hD N cap hEven
  have hV := (actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hEven).le
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hE : 0 ≤ actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have habs := abs_slopes_le_of_density_sandwich hV hE h.1 h.2.1 h.2.2.1 h.2.2.2.1
  dsimp only at habs ⊢
  apply abs_physicalDensitySum_smallRoughRho_sub_le
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    hrough compiled raw (actualSmallRosserMinus N cap _ _)
      (actualSmallRosserPlus N cap _ _)
  · exact habs.1
  · exact habs.2

/-- The compiler pays only its literal rough coefficient error on the
natural density scale. The constant is chosen before epsilon, and epsilon
before the common threshold. Both small-density slope estimates and the
Euler normalization are proved suppliers, not hypotheses of this result. -/
theorem exists_actualCompiledRho_normalized_density_difference_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, 0 < N → Even N → D ^ (epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ rough : Finset ℕ,
              (∀ d ∈ rough, RoughPrimeSupportedAt (D ^ (epsilon ^ 2)) d) →
                ∀ compiled raw : ℕ → ℝ,
                  let w := D ^ (epsilon ^ 2)
                  let L := D ^ epsilon
                  let small := actualSmallRosserSupport N cap w
                  let density := fun c => physicalDensitySum (smallRoughModuli small rough)
                    (smallRoughRho small rough c (actualSmallRosserMinus N cap w L)
                      (actualSmallRosserPlus N cap w L))
                  |density compiled - density raw| ≤
                    ((B / epsilon ^ 2) *
                      reciprocalTotientDensity rough (fun d => |compiled d - raw d|)) *
                        (singularSeries N / Real.log D) := by
  obtain ⟨A, hA, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, _hK, hsupply⟩ := exists_actualCompiledRho_density_difference_bound
  refine ⟨A * (C + 2), mul_pos hA (by linarith), ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨Dsieve, hDsieve, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  have hexp : Real.exp (-(1 / epsilon)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr hepsilon.le))
  have hfloor : C * Real.exp (-(1 / epsilon)) < C + 1 := by
    have h := mul_le_mul_of_nonneg_left hexp hC.le
    nlinarith
  have herror : ∀ᶠ D : ℝ in atTop,
      actualSmallRosserDensityError C K D epsilon < C + 1 :=
    (tendsto_actualSmallRosserDensityError C K epsilon hepsilon).eventually
      (gt_mem_nhds hfloor)
  obtain ⟨Dscalar, hDscalar⟩ := eventually_atTop.mp
    (herror.and (eventually_four_le_smallRosserPower epsilon hepsilon))
  refine ⟨max Dsieve Dscalar, hDsieve.trans (le_max_left _ _), ?_⟩
  intro D hD N cap hN hEven hcap rough hrough compiled raw
  have hDs : Dsieve ≤ D := (le_max_left _ _).trans hD
  have hDt : Dscalar ≤ D := (le_max_right _ _).trans hD
  have hDpos : 0 < D := by linarith
  have hE := (hDscalar D hDt).1
  have hV := hEuler N cap hN hEven (D ^ (epsilon ^ 2))
    (hDscalar D hDt).2 hcap
  rw [Real.log_rpow hDpos] at hV
  have hVnonneg := (actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hEven).le
  have hmass : 0 ≤ reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
    unfold reciprocalTotientDensity
    apply Finset.sum_nonneg
    intro d _hd
    positivity
  have h := hsupply D hDs N cap hEven rough hrough compiled raw
  dsimp only at h ⊢
  calc
    _ ≤ (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        (1 + actualSmallRosserDensityError C K D epsilon)) *
          reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := h
    _ ≤ (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) * (C + 2)) *
        reciprocalTotientDensity rough (fun d => |compiled d - raw d|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hVnonneg) hmass
    _ ≤ ((A * singularSeries N / (epsilon ^ 2 * Real.log D)) * (C + 2)) *
        reciprocalTotientDensity rough (fun d => |compiled d - raw d|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hV (by linarith)) hmass
    _ = _ := by ring

/-- Target-scale form for the manuscript parameterization `D = N^nu`.
The error is for the compiled physical density itself, with the same
small weights as the raw coefficient. In particular its budget contains
the exact factor `1 / nu` from changing logarithmic scales. -/
theorem exists_actualCompiledRho_target_density_difference_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ rough : Finset ℕ,
              (∀ d ∈ rough, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d) →
                ∀ compiled raw : ℕ → ℝ,
                  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
                  let L := (N : ℝ) ^ (nu * epsilon)
                  let small := actualSmallRosserSupport N cap w
                  let density := fun c => physicalDensitySum (smallRoughModuli small rough)
                    (smallRoughRho small rough c (actualSmallRosserMinus N cap w L)
                      (actualSmallRosserPlus N cap w L))
                  |density compiled - density raw| ≤
                    ((B / (nu * epsilon ^ 2)) *
                      reciprocalTotientDensity rough (fun d => |compiled d - raw d|)) *
                        (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_normalized_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon hepsilon hepsilon8
  obtain ⟨D₀, _hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge, hNlarge⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop D₀))
  refine ⟨max Nlarge 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap rough hrough compiled raw
  have hNlarge' : Nlarge ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsmall : ((N : ℝ) ^ nu) ^ (epsilon ^ 2) =
      (N : ℝ) ^ (nu * epsilon ^ 2) := (Real.rpow_mul hNposR.le _ _).symm
  have h := hsupply ((N : ℝ) ^ nu) (hNlarge N hNlarge') N cap hNpos hEven
    (by rwa [hsmall]) rough (by rwa [hsmall]) compiled raw
  dsimp only at h ⊢
  simp only [← Real.rpow_mul hNposR.le, Real.log_rpow hNposR] at h
  convert h using 1; ring

/-- The exact finite compiler mass budget which suffices after the raw
density has been bounded. This removes the two abstract small-density
premises from the previous compiler interface; the raw density and the
literal compiler coefficient error remain visible and are not asserted.
The threshold is uniform in these coefficients and in their budget. -/
theorem exists_actualCompiledRho_density_budget :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ rough : Finset ℕ,
              (∀ d ∈ rough, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d) →
                ∀ (compiled raw : ℕ → ℝ) (rawBound reserve : ℝ),
                  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
                  let L := (N : ℝ) ^ (nu * epsilon)
                  let small := actualSmallRosserSupport N cap w
                  let density := fun c => physicalDensitySum (smallRoughModuli small rough)
                    (smallRoughRho small rough c (actualSmallRosserMinus N cap w L)
                      (actualSmallRosserPlus N cap w L))
                  density raw ≤ rawBound * (singularSeries N / Real.log (N : ℝ)) →
                  reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
                    reserve * (nu * epsilon ^ 2) / B →
                  rawBound + reserve ≤ currentK →
                  density compiled ≤ currentK * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon hepsilon hepsilon8
  obtain ⟨N₀, hN₀, hsupply⟩ := hsupply nu hnu epsilon hepsilon hepsilon8
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap rough hrough compiled raw rawBound reserve
  dsimp only
  intro hraw hcompiler hbudget
  have herror := hsupply N hN hEven cap hcap rough hrough compiled raw
  dsimp only at herror
  have hpower : 0 < nu * epsilon ^ 2 := mul_pos hnu (sq_pos_of_pos hepsilon)
  have hreserve : (B / (nu * epsilon ^ 2)) *
      reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤ reserve := by
    have h := mul_le_mul_of_nonneg_left hcompiler (div_pos hB hpower).le
    have heq : (B / (nu * epsilon ^ 2)) * (reserve * (nu * epsilon ^ 2) / B) =
        reserve := by field_simp [hB.ne', hpower.ne']
    rwa [heq] at h
  have hscale := (densityScale_pos (hN₀.trans hN)).le
  have herror' := herror.trans (mul_le_mul_of_nonneg_right hreserve hscale)
  have hupper := (le_abs_self _).trans herror'
  have htotal := mul_le_mul_of_nonneg_right hbudget hscale
  linarith

end
end ImbalancedChen
