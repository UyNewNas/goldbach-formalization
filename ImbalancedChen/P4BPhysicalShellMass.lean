import ImbalancedChen.P4BSublinearCutoffMass
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual product-shell mass on the original source scale

SOURCE ONLY / YELLOW / UNCOMPILED. The sibling import is its intended
future normal module name.

For fixed `0<b<1` and `c>1`, the actual ordered-source shell
`N < m ≤ floor(c*N)` has cardinality divided by the ORIGINAL `N/log N`
tending to `(c-1)*log(1/b)`. Natural flooring, logarithmic normalization,
and composition of the proved actual zero-cutoff source limit are paid
below. No mass limit is assumed as a parameter.

The final theorem chooses one positive logarithmic width and one natural
threshold for an arbitrarily small upper payment on this same scale.
It concerns the genuine source shell; no upper-sieve closure is asserted.
-/

namespace ImbalancedChen.P4BPhysicalShellMass

noncomputable section
open Filter Topology

/-- The actual ordered bad-source product shell, retaining both exact
boundaries and the original predicate, with no witness multiplicity. -/
def physicalProductShell (b c : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).filter
    (fun m : ℕ => N < m)

@[simp] theorem mem_physicalProductShell {b c : ℝ} {N m : ℕ} :
    m ∈ physicalProductShell b c N ↔
      N < m ∧ m ≤ Nat.floor (c * (N : ℝ)) ∧ RealOrderedBadReceiver b m := by
  classical
  rw [physicalProductShell, Finset.mem_filter, mem_realHalfProductSource]
  constructor
  · rintro ⟨⟨hmcap, _hmzero, hbad⟩, hNm⟩
    exact ⟨hNm, hmcap, hbad⟩
  · rintro ⟨hNm, hmcap, hbad⟩
    exact ⟨⟨hmcap, Nat.cast_nonneg m, hbad⟩, hNm⟩

/-- The dilation floor is at least the original natural endpoint when
`c≥1`; this includes the zero target. -/
theorem le_dilation_floor {c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    N ≤ Nat.floor (c * (N : ℝ)) := by
  apply Nat.le_floor
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)

/-- Exact finite shell cardinality, before division by any scale. -/
theorem shell_card_eq_source_sub {b c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    ((physicalProductShell b c N).card : ℝ) =
      ((realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).card : ℝ) -
        ((realHalfProductSource b N 0).card : ℝ) := by
  classical
  have hfilter : (realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).filter
      (fun m : ℕ => m ≤ N) = realHalfProductSource b N 0 := by
    ext m
    constructor
    · intro hm
      rcases Finset.mem_filter.mp hm with ⟨hsource, hmN⟩
      rcases mem_realHalfProductSource.mp hsource with ⟨_hmcap, hmzero, hbad⟩
      exact mem_realHalfProductSource.mpr ⟨hmN, hmzero, hbad⟩
    · intro hm
      rcases mem_realHalfProductSource.mp hm with ⟨hmN, hmzero, hbad⟩
      exact Finset.mem_filter.mpr
        ⟨mem_realHalfProductSource.mpr
          ⟨hmN.trans (le_dilation_floor hc N), hmzero, hbad⟩, hmN⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0)
    (fun m : ℕ => m ≤ N)
  rw [hfilter] at hcard
  simp only [not_le] at hcard
  have hreal : ((realHalfProductSource b N 0).card : ℝ) +
      ((physicalProductShell b c N).card : ℝ) =
      ((realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The actual uncut source limit is supplied by the sibling proved
sublinear-cutoff theorem, with coefficient zero and exponent zero. -/
theorem tendsto_source_zero_mass {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun N : ℕ => ((realHalfProductSource b N 0).card : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 (Real.log (1 / b))) := by
  simpa only [zero_mul] using
    P4BSublinearCutoffMass.tendsto_source_powerCutoff_mass
      (b := b) (C := (0 : ℝ)) (theta := (0 : ℝ)) hb hb1 (by norm_num) (by norm_num)

/-- Natural dilation endpoints tend to infinity. -/
theorem tendsto_dilation_floor_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Nat.floor (c * (N : ℝ))) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop c hc

/-- The exact natural floor pays its unit rounding error in the dilation
ratio, using the proved pinned mathlib floor limit. -/
theorem tendsto_dilation_floor_div {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => (Nat.floor (c * (N : ℝ)) : ℝ) / (N : ℝ))
      atTop (𝓝 c) := by
  exact (tendsto_nat_floor_mul_div_atTop hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The floor endpoint has the same logarithmic scale as the original
target. This proof explicitly normalizes by `log N`, rather than replacing
it by the logarithm of a real or natural dilated target. -/
theorem tendsto_log_dilation_floor_div_log {c : ℝ} (hc : 1 < c) :
    Tendsto (fun N : ℕ => Real.log (Nat.floor (c * (N : ℝ)) : ℝ) /
      Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hratio := tendsto_dilation_floor_div hcpos.le
  have hlogRatio : Tendsto (fun N : ℕ =>
      Real.log ((Nat.floor (c * (N : ℝ)) : ℝ) / (N : ℝ)))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hcpos.ne').tendsto.comp hratio
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hlogRatio.div_atTop hlogTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsum : Tendsto (fun N : ℕ =>
      Real.log ((Nat.floor (c * (N : ℝ)) : ℝ) / (N : ℝ)) /
        Real.log (N : ℝ) + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using hsmall.add hone
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos := zero_lt_one.trans hN1
  have hK : 2 ≤ Nat.floor (c * (N : ℝ)) := hN.trans (le_dilation_floor hc.le N)
  have hKpos : (0 : ℝ) < (Nat.floor (c * (N : ℝ)) : ℝ) := by
    exact_mod_cast (show 0 < Nat.floor (c * (N : ℝ)) by omega)
  rw [Real.log_div hKpos.ne' hNpos.ne']
  field_simp [(Real.log_pos hN1).ne'] <;> ring

/-- Conversion of the dilated source scale to the original `N/log N`
scale, including the exact natural floor and both logarithms. -/
theorem tendsto_dilation_massScale_ratio {c : ℝ} (hc : 1 < c) :
    Tendsto (fun N : ℕ =>
      ((Nat.floor (c * (N : ℝ)) : ℝ) /
        Real.log (Nat.floor (c * (N : ℝ)) : ℝ)) /
          ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 c) := by
  have hratio := (tendsto_dilation_floor_div (zero_lt_one.trans hc).le).div
    (tendsto_log_dilation_floor_div_log hc) (by norm_num : (1 : ℝ) ≠ 0)
  have hlim : Tendsto (fun N : ℕ =>
      ((Nat.floor (c * (N : ℝ)) : ℝ) / (N : ℝ)) /
        (Real.log (Nat.floor (c * (N : ℝ)) : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 c) := by simpa only [Pi.div_def, div_one] using hratio
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos := zero_lt_one.trans hN1
  have hK : 2 ≤ Nat.floor (c * (N : ℝ)) := hN.trans (le_dilation_floor hc.le N)
  have hK1 : (1 : ℝ) < (Nat.floor (c * (N : ℝ)) : ℝ) := by
    exact_mod_cast (show 1 < Nat.floor (c * (N : ℝ)) by omega)
  have hKpos := zero_lt_one.trans hK1
  field_simp [hNpos.ne', hKpos.ne', (Real.log_pos hN1).ne', (Real.log_pos hK1).ne']
    <;> ring

/-- The proved actual zero-cutoff mass at the floor-dilated target,
expressed on the original target's normalization. -/
theorem tendsto_dilated_source_on_original_scale
    {b c : ℝ} (hb : 0 < b) (hb1 : b < 1) (hc : 1 < c) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (c * Real.log (1 / b))) := by
  have hprefix := (tendsto_source_zero_mass hb hb1).comp
    (tendsto_dilation_floor_atTop (zero_lt_one.trans hc))
  have hprod := hprefix.mul (tendsto_dilation_massScale_ratio hc)
  rw [mul_comm (Real.log (1 / b)) c] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos := zero_lt_one.trans hN1
  have hK : 2 ≤ Nat.floor (c * (N : ℝ)) := hN.trans (le_dilation_floor hc.le N)
  have hK1 : (1 : ℝ) < (Nat.floor (c * (N : ℝ)) : ℝ) := by
    exact_mod_cast (show 1 < Nat.floor (c * (N : ℝ)) by omega)
  have hKpos := zero_lt_one.trans hK1
  dsimp only [Function.comp_def]
  field_simp [hNpos.ne', hKpos.ne', (Real.log_pos hN1).ne', (Real.log_pos hK1).ne']
    <;> ring

/-- True product-shell mass, with no PNT or mass-limit hypothesis and no
change to the original `N/log N` normalization. -/
theorem tendsto_physicalProductShell_mass
    {b c : ℝ} (hb : 0 < b) (hb1 : b < 1) (hc : 1 < c) :
    Tendsto (fun N : ℕ => ((physicalProductShell b c N).card : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 ((c - 1) * Real.log (1 / b))) := by
  have hsub := (tendsto_dilated_source_on_original_scale hb hb1 hc).sub
    (tendsto_source_zero_mass hb hb1)
  have hlimit : c * Real.log (1 / b) - Real.log (1 / b) =
      (c - 1) * Real.log (1 / b) := by ring
  rw [hlimit] at hsub
  have hlim : Tendsto (fun N : ℕ =>
      (((realHalfProductSource b (Nat.floor (c * (N : ℝ))) 0).card : ℝ) -
        ((realHalfProductSource b N 0).card : ℝ)) /
          ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 ((c - 1) * Real.log (1 / b))) := by
    simpa only [sub_div] using hsub
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    rw [shell_card_eq_source_sub hc.le N]

/-- A genuine physical product ramp may be given an arbitrarily small
source-shell payment by fixing a positive logarithmic width FIRST, then
choosing one natural threshold. The displayed shell retains `N<m≤floor(e^δ N)`.
This theorem supplies actual cardinality mass, not a distribution transfer. -/
theorem exists_log_width_eventually_shell_le
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ((physicalProductShell b (Real.exp delta) N).card : ℝ) ≤
        eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  let J : ℝ := Real.log (1 / b)
  have hJ : 0 < J := by
    dsimp only [J]
    apply Real.log_pos
    exact (one_lt_div hb).mpr hb1
  let delta : ℝ := Real.log (1 + eta / (2 * J))
  have harg : 1 < 1 + eta / (2 * J) := by
    have hfrac := div_pos heta (mul_pos (by norm_num : (0 : ℝ) < 2) hJ)
    linarith
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact Real.log_pos harg
  have hexp : Real.exp delta = 1 + eta / (2 * J) := by
    dsimp only [delta]
    exact Real.exp_log (zero_lt_one.trans harg)
  have hc : 1 < Real.exp delta := by rw [hexp]; exact harg
  have hcoefficient : (Real.exp delta - 1) * Real.log (1 / b) = eta / 2 := by
    change (Real.exp delta - 1) * J = eta / 2
    rw [hexp]
    field_simp [hJ.ne'] <;> ring
  have hless : (Real.exp delta - 1) * Real.log (1 / b) < eta := by
    rw [hcoefficient]
    linarith
  have hnear := (tendsto_physicalProductShell_mass hb hb1 hc).eventually
    (gt_mem_nhds hless)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ((physicalProductShell b (Real.exp delta) N).card : ℝ) ≤
        eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with N hnearN hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
    exact ((div_lt_iff₀ hscale).mp hnearN).le
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbound
  exact ⟨delta, hdelta, N0, hN0⟩

end
end ImbalancedChen.P4BPhysicalShellMass
