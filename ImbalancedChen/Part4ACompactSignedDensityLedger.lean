import ImbalancedChen.ActualExtendedThirdCompactSignedDensityLimit
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve

/-!
SOURCEONLY / UNCOMPILED. The coefficient is the actual compact policy's
fixed signed coefficient, at cap N and w=0. The initial dyadic-stop density
is kept as an unevaluated first term. A common buffer and mesh are chosen
before N; the full finite functional is a comparison object at these same
parameters. Three analytic errors pay the transfer to that functional.
Its existing compact + Tnew + u/4 supplier then gives a total reserve u.
No full22, K, numerical compact enclosure or initial-density bound is input.
-/

namespace ImbalancedChen.Part4ACompactSignedDensityLedger

noncomputable section
open Set Filter Topology
open OriginalThirdFiniteReserveSourceOnly

/-- The literal retained support, without taking absolute values. -/
def signedSupport (e h : ℝ) (m N : ℕ) : Finset ℕ :=
  fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false)
    N N 0 ((N : ℝ) ^ thirdPrefixRho)

/-- The original signed Möbius coefficient on that support. -/
def signedCoefficient (e h : ℝ) (m N d : ℕ) : ℝ :=
  fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
    N N 0 ((N : ℝ) ^ thirdPrefixRho) d

/-- The sign is exactly Möbius on the actual support, and zero elsewhere. -/
theorem signedCoefficient_eq_moebius (e h : ℝ) (m N d : ℕ) :
    signedCoefficient e h m N d =
      if d ∈ signedSupport e h m N then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  classical
  unfold signedCoefficient fixedRoughCoefficient oddFirstExitRetainedCoefficient
  change ((if d ∈ signedSupport e h m N then ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  split_ifs <;> simp

def signedDensity (e h : ℝ) (m N : ℕ) : ℝ :=
  reciprocalTotientDensity (signedSupport e h m N) (signedCoefficient e h m N)

/-- The same policy's exact initial plus-density, with its floor-grid stop. -/
def initialDensity (e : ℝ) (m N : ℕ) : ℝ :=
  actualSmallRosserPlusDensity N N
    ((N : ℝ) ^ actualExtendedThirdInitialStopExponent e m)
    ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))

def normalizedCorrection (e h : ℝ) (m N : ℕ) : ℝ :=
  (signedDensity e h m N - initialDensity e m N) *
    Real.log (N : ℝ) / singularSeries N

/-- In particular, the density under the eventual upper bound is the actual
reciprocal-totient sum, not a newly postulated coefficient envelope. -/
theorem signedDensity_eq_actual (e h : ℝ) (m N : ℕ) :
    signedDensity e h m N =
      reciprocalTotientDensity
        (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false)
          N N 0 ((N : ℝ) ^ thirdPrefixRho))
        (fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
          N N 0 ((N : ℝ) ^ thirdPrefixRho)) := by
  rfl

theorem normalizedDensity_eq_initial_add_correction (e h : ℝ) (m N : ℕ) :
    signedDensity e h m N * Real.log (N : ℝ) / singularSeries N =
      initialDensity e m N * Real.log (N : ℝ) / singularSeries N +
        normalizedCorrection e h m N := by
  unfold normalizedCorrection
  ring

theorem tendsto_normalizedCorrection {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    Tendsto (normalizedCorrection e h m)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  exact tendsto_actualExtendedThirdCompactSignedDensityCorrection hh he0 he hmesh

/-- Arbitrarily prescribed buffer/mesh thresholds can be met while paying
the comparison with the full finite functional. These are analytically
proved errors, not a signed-density or target-constant premise. -/
theorem exists_same_parameters_transfer {δ E : ℝ} (hδ : 0 < δ) (hE : 0 < E)
    (M : ℕ) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ E ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      M ≤ m ∧ actualExtendedThirdDyadicStep m ≤ e / 2 ∧
        ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
          |normalizedCorrection e h m N - actualExtendedThirdFiniteFunctional e m| ≤ δ := by
  have hthird : 0 < δ / 3 := by linarith
  obtain ⟨h, hh, eC, heC, heCcap, mC, hcompact⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx hthird
  obtain ⟨eF, heF, _heFcap, mF, hfinite⟩ :=
    actualExtendedThirdFiniteFunctional_uniform_approx hthird
  let e : ℝ := min E (min eC eF) / 2
  have he0 : 0 < e := half_pos (lt_min hE (lt_min heC heF))
  have hehalf : e ≤ min E (min eC eF) := by
    dsimp [e]
    linarith [lt_min hE (lt_min heC heF)]
  have heE : e ≤ E := hehalf.trans (min_le_left _ _)
  have heC' : e ≤ eC := hehalf.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heF' : e ≤ eF := hehalf.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hecap : e ≤ 1 / 384 := heC'.trans heCcap
  obtain ⟨mS, hmS⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (half_pos he0)))
  let m : ℕ := max M (max mC (max mF mS))
  have hMm : M ≤ m := le_max_left _ _
  have hmC : mC ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmF : mF ≤ m := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hmS' : mS ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hmesh : actualExtendedThirdDyadicStep m ≤ e / 2 := (hmS m hmS').le
  have hC := hcompact e he0.le heC' m hmC
  have hF : |actualExtendedThirdIdealFunctional - actualExtendedThirdFiniteFunctional e m|
      ≤ δ / 3 := by
    simpa only [abs_sub_comm] using hfinite e he0.le heF' m hmF
  have hA : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      |normalizedCorrection e h m N - actualExtendedThirdCompactCellFunctional e h m| < δ / 3 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_normalizedCorrection hh he0 hecap hmesh) (δ / 3) hthird
  refine ⟨h, hh, e, he0, heE, hecap, m, hMm, hmesh, ?_⟩
  filter_upwards [hA] with N hN
  calc
    |normalizedCorrection e h m N - actualExtendedThirdFiniteFunctional e m| ≤
        |normalizedCorrection e h m N - actualExtendedThirdCompactCellFunctional e h m| +
          |actualExtendedThirdCompactCellFunctional e h m - actualExtendedThirdFiniteFunctional e m| :=
      abs_sub_le _ _ _
    _ ≤ δ / 3 + (δ / 3 + δ / 3) :=
      add_le_add hN.le ((abs_sub_le _ actualExtendedThirdIdealFunctional _).trans
        (add_le_add hC hF))
    _ = δ := by ring

/-- Concrete signed upper ledger. The finite supplier pays u/4, while the
three transfer errors together pay 3u/4. The actual first-term density is
retained with its original positive sign. One fixed legal compact policy
works for all sufficiently large positive even targets. -/
theorem exists_signedDensity_upper_ledger :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
        ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
          signedDensity e h m N * Real.log (N : ℝ) / singularSeries N ≤
            initialDensity e m N * Real.log (N : ℝ) / singularSeries N +
              originalCompactThirdCorrection +
              (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve := by
  obtain ⟨E, hE, _hEcap, M, hsupplier⟩ :=
    finiteFunctional_le_compact_add_Tnew_add_original_density_quarter
  have hu : 0 < originalDensityReserve := by norm_num [originalDensityReserve]
  obtain ⟨h, hh, e, he0, heE, hecap, m, hMm, hmesh, htransfer⟩ :=
    exists_same_parameters_transfer (by positivity : 0 < 3 * originalDensityReserve / 4) hE M
  have hF := hsupplier e he0.le heE m hMm
  refine ⟨h, hh, e, he0, hecap, m, hmesh, ?_⟩
  filter_upwards [htransfer] with N hN
  have hpaid : normalizedCorrection e h m N - actualExtendedThirdFiniteFunctional e m ≤
      3 * originalDensityReserve / 4 := (le_abs_self _).trans hN
  rw [normalizedDensity_eq_initial_add_correction]
  linarith only [hpaid, hF]

end
end ImbalancedChen.Part4ACompactSignedDensityLedger
