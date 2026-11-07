import ImbalancedChen.ActualCompilerDensityReserve

/-!
# P4A: vanishing literal compiler mass gives vanishing physical error

The two densities use identical actual small Rosser weights and identical
small/rough carriers. The input limit concerns only the reciprocal-totient
absolute coefficient difference. The physical-error limit follows from
the proved actual compiler supplier with factor B/(nu*epsilon^2).

SOURCE ONLY; no compilation was performed.
-/

namespace ImbalancedChen.P4ACompilerMassVanishes

noncomputable section

open Filter Topology

/-- Literal physical attachment of a rough coefficient with actual small
Rosser weights at the manuscript powers. -/
def attachedDensity (nu epsilon : ℝ) (N cap : ℕ)
    (rough : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let L := (N : ℝ) ^ (nu * epsilon)
  let small := actualSmallRosserSupport N cap w
  physicalDensitySum (smallRoughModuli small rough)
    (smallRoughRho small rough c
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L))

/-- The manuscript's density normalization of that same coefficient. -/
def normalizedDensity (nu epsilon : ℝ) (N cap : ℕ)
    (rough : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  attachedDensity nu epsilon N cap rough c * Real.log (N : ℝ) / singularSeries N

private theorem abs_normalized_sub_le {N : ℕ} (hN : 2 ≤ N)
    {x y M : ℝ}
    (h : |x - y| ≤ M * (singularSeries N / Real.log (N : ℝ))) :
    |x * Real.log (N : ℝ) / singularSeries N -
      y * Real.log (N : ℝ) / singularSeries N| ≤ M := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hn := (density_le_manuscriptScale_iff_normalized hN |x - y| M).mp h
  calc
    |x * Real.log (N : ℝ) / singularSeries N -
        y * Real.log (N : ℝ) / singularSeries N| =
      |x - y| * Real.log (N : ℝ) / singularSeries N := by
        rw [← sub_div, ← sub_mul, abs_div, abs_mul,
          abs_of_pos hlog, abs_of_pos (singularSeries_pos N)]
    _ ≤ M := hn

/-- The actual uniform threshold supplies a normalized estimate for any
eventually admissible carrier sequence. B comes from the proved small
Rosser density supplier; it is not an assumed physical error constant. -/
theorem exists_eventual_normalized_difference_bound
    (nu epsilon : ℝ) (hnu : 0 < nu)
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (cap : ℕ → ℕ) (rough : ℕ → Finset ℕ)
    (compiled raw : ℕ → ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap N : ℝ))
    (hrough : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ d ∈ rough N, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        |normalizedDensity nu epsilon N (cap N) (rough N) (compiled N) -
          normalizedDensity nu epsilon N (cap N) (rough N) (raw N)| ≤
          (B / (nu * epsilon ^ 2)) *
            reciprocalTotientDensity (rough N) (fun d => |compiled N d - raw N d|) := by
  obtain ⟨B, hB, hsupply⟩ :=
    exists_actualCompiledRho_target_density_difference_bound
  obtain ⟨N₀, hN₀, hsupply⟩ := hsupply nu hnu epsilon hepsilon hepsilon8
  refine ⟨B, hB, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      N₀ ≤ N := (eventually_ge_atTop N₀).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap, hrough] with N hN hEven hcapN hroughN
  have h := hsupply N hN hEven.2 (cap N) hcapN (rough N) hroughN
    (compiled N) (raw N)
  dsimp only at h
  exact abs_normalized_sub_le (hN₀.trans hN) h

/-- Vanishing absolute coefficient mass forces the actual normalized
physical density difference to vanish. The mass premise is not a physical
error premise. Fixed positive nu and epsilon keep the supplied multiplier
B/(nu*epsilon^2) constant along the target limit. -/
theorem tendsto_normalized_difference_zero_of_absolute_mass_zero
    (nu epsilon : ℝ) (hnu : 0 < nu)
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (cap : ℕ → ℕ) (rough : ℕ → Finset ℕ)
    (compiled raw : ℕ → ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap N : ℝ))
    (hrough : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ d ∈ rough N, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d)
    (hmass : Tendsto (fun N : ℕ =>
      reciprocalTotientDensity (rough N) (fun d => |compiled N d - raw N d|))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      normalizedDensity nu epsilon N (cap N) (rough N) (compiled N) -
        normalizedDensity nu epsilon N (cap N) (rough N) (raw N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  obtain ⟨B, _hB, hbound⟩ := exists_eventual_normalized_difference_bound
    nu epsilon hnu hepsilon hepsilon8 cap rough compiled raw hcap hrough
  have hscaled : Tendsto (fun N : ℕ => (B / (nu * epsilon ^ 2)) *
      reciprocalTotientDensity (rough N) (fun d => |compiled N d - raw N d|))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
    simpa only [mul_zero] using hmass.const_mul (B / (nu * epsilon ^ 2))
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hsmall := hscaled.eventually (gt_mem_nhds heta)
  filter_upwards [hbound, hsmall] with N hN hsmallN
  simpa only [Real.dist_eq, sub_zero] using hN.trans_lt hsmallN

/-- For an actual fixed retention policy the rough-support hypothesis is
supplied by its construction. Only cap coverage and literal compiler mass
convergence are inputs. The raw coefficient is the actual policy's fixed
rough coefficient, and its physical attachment is the original actual rho. -/
theorem tendsto_actual_policy_compiler_normalized_difference_zero
    (nu epsilon : ℝ) (hnu : 0 < nu)
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (cap : ℕ → ℕ) (z : ℕ → ℝ) (retainOdd : ℕ → List ℕ → Bool)
    (compiled : ℕ → ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap N : ℝ))
    (hmass : Tendsto (fun N : ℕ =>
      reciprocalTotientDensity
        (fixedRoughSupport (retainOdd N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N))
        (fun d => |compiled N d - fixedRoughCoefficient (retainOdd N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N) d|))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      normalizedDensity nu epsilon N (cap N)
        (fixedRoughSupport (retainOdd N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N)) (compiled N) -
        physicalDensitySum
          (actualSmallRoughModuli (retainOdd N) N (cap N)
            ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N))
          (actualSmallRoughRho (retainOdd N) N (cap N)
            ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N)
            ((N : ℝ) ^ (nu * epsilon))) * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  exact tendsto_normalized_difference_zero_of_absolute_mass_zero
    nu epsilon hnu hepsilon hepsilon8 cap
    (fun N => fixedRoughSupport (retainOdd N) N (cap N)
      ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N)) compiled
    (fun N => fixedRoughCoefficient (retainOdd N) N (cap N)
      ((N : ℝ) ^ (nu * epsilon ^ 2)) (z N)) hcap
    (Filter.Eventually.of_forall (fun N d hd =>
      fixedRoughSupport_roughPrimeSupportedAt (retainOdd N) N (cap N) _ _ hd)) hmass

end
end ImbalancedChen.P4ACompilerMassVanishes
