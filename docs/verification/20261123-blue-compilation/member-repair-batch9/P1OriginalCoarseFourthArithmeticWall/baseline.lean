import ImbalancedChen.P1ActualCoarseLevelCeiling
import ImbalancedChen.P1OriginalCoarseFourthJointGeometry
import ImbalancedChen.AffinePrimeWallReserve

/-!
# The original coarse T3 frontier's actual fourth arithmetic wall

The parent here is literally `HistoricalThirdCoarse.policy`, including its
initialPolicy/firstStop and its actual raw Gamma-2e third level.  No
HistoricalPrefixCapData is used.  The raw level is represented by its true
logarithmic exponent, which belongs to the finite original exponentValues
table, including the exact initial fallback.

The fourth reciprocal-prime tree coefficient is positive by its actual
even-length sign.  Its near-s=1 mass is bounded by one public cube strip
family with form sum(t)+t(last).  A single width and threshold work for all
rough activation parameters omega and all adequate enumeration caps.

Source-only/uncompiled.  Sibling imports require their proposed module names.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set
open HistoricalThirdCoarse

namespace P1OriginalCoarseFourthArithmeticWall

def wallForm : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1 +
    ContinuousLinearMap.proj 2 + (2 : ℝ) • ContinuousLinearMap.proj 3

theorem wallForm_eq_sum_last (t : Fin 4 → ℝ) :
    wallForm t = (∑ i, t i) + t 3 := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  have hform : wallForm t = t 0 + t 1 + t 2 + 2 * t 3 := by
    simp [wallForm]
  rw [hform, hsum]
  ring

theorem wallForm_ne_zero : wallForm ≠ 0 := by
  intro h
  have hh := congrArg (fun F : (Fin 4 → ℝ) →L[ℝ] ℝ => F (fun _ => 1)) h
  norm_num [wallForm] at hh

/-- The exact original old third level, read at the same tuple ancestor. -/
def rawTupleLevel (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  rawLevel e chi m omega (N : ℝ) (HistoricalThirdCoarse.P1OriginalFourth.history3 p)

def rawTupleExponent (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ)
    (p : Fin 4 → ℕ) : ℝ :=
  Real.log (rawTupleLevel e chi m omega N p) / Real.log (N : ℝ)

def rawTupleGap (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  rawTupleExponent e chi m omega N p - (∑ i, actualPrimeTupleLog N p i) -
    actualPrimeTupleLog N p 3

/-- An actual raw-level equality fixes its logarithmic exponent exactly. -/
theorem rawTupleExponent_eq_of_level {e chi omega lambda : ℝ} {m N : ℕ}
    (hN : 1 < N) (p : Fin 4 → ℕ)
    (hlevel : rawTupleLevel e chi m omega N p = (N : ℝ) ^ lambda) :
    rawTupleExponent e chi m omega N p = lambda := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hn).ne'
  unfold rawTupleExponent
  rw [hlevel, Real.log_rpow (zero_lt_one.trans hn)]
  field_simp [hlog]

/-- This finite range includes inactive/unselected initial fallbacks.
It is independent of omega, N and the selected fourth tuple. -/
theorem rawTupleExponent_mem_values (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) :
    rawTupleExponent e chi m omega N p ∈
      P1ActualCoarseLevelCeiling.exponentValues e chi m := by
  obtain ⟨lambda, hlambda, hlevel⟩ :=
    P1ActualCoarseLevelCeiling.rawLevel_eq_rpow_mem_exponentValues e chi m omega (N : ℝ)
      (HistoricalThirdCoarse.P1OriginalFourth.history3 p)
  have heq := rawTupleExponent_eq_of_level hN p hlevel
  rw [heq]
  exact hlambda

/-- The affine gap is the true original quotient-level logarithmic gap,
including all four primes in the literal natural product denominator. -/
theorem rawTupleGap_eq_quotientLogGap
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (hN : 1 < N)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) :
    rawTupleGap e chi m omega N p =
      Real.log (rawTupleLevel e chi m omega N p / (∏ i, p i : ℕ)) /
        Real.log (N : ℝ) - actualPrimeTupleLog N p 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ : 0 < rawTupleLevel e chi m omega N p :=
    P1ActualCoarseLevelCeiling.rawLevel_pos e chi m omega (N : ℝ) hn _
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  unfold rawTupleGap rawTupleExponent
  rw [Real.log_div hQ.ne' hP.ne', actualPrimeTupleLog_sum_prod p hpos]
  ring

def originalAdmittedTuples (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (b : ℝ) : Finset (Fin 4 → ℕ) :=
  firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))

/-- Original carrier with an explicit positive-power last-prime cutoff. -/
def originalWallTuples (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (a b delta : ℝ) : Finset (Fin 4 → ℕ) :=
  (originalAdmittedTuples e chi m omega N cap b).filter fun p =>
    (N : ℝ) ^ a ≤ (p (Fin.last 3) : ℝ) ∧
      0 < rawTupleGap e chi m omega N p ∧ rawTupleGap e chi m omega N p ≤ delta

/-- Strict decreasing order lifts the last-prime lower cutoff to every coordinate. -/
theorem original_admitted_mem_cube
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (a b : ℝ)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (p : Fin 4 → ℕ)
    (hp : p ∈ originalAdmittedTuples e chi m omega N cap b)
    (hlast : (N : ℝ) ^ a ≤ (p (Fin.last 3) : ℝ)) :
    p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b) := by
  have hd := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ b) hcap p).mp hp
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hlastle : (p (Fin.last 3) : ℝ) ≤ p i := by
    exact_mod_cast hd.1.antitone (Fin.le_last i)
  exact ⟨(hd.2.1 i).1, (hd.2.1 i).2.1, hlast.trans hlastle, (hd.2.1 i).2.2.2⟩

/-- The actual original T3 third cube implies the strict fourth PLUS gate.
Its current Gamma level is retained, even when below the initial level. -/
theorem original_admitted_gap_pos
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (b : ℝ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (p : Fin 4 → ℕ)
    (hp : p ∈ originalAdmittedTuples e chi m omega N cap b) :
    0 < rawTupleGap e chi m omega N p := by
  have hd := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ b) hcap p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).1.pos
  have hv := (HistoricalThirdCoarse.P1OriginalFourth.valid_fourth_iff
    e chi m omega (N : ℝ) p hpos hd.1).mp hd.2.2
  obtain ⟨lambda, _hlambda, hlevel⟩ :=
    P1ActualCoarseLevelCeiling.rawLevel_eq_rpow_mem_exponentValues e chi m omega (N : ℝ)
      (HistoricalThirdCoarse.P1OriginalFourth.history3 p)
  rw [hlevel] at hv
  have hc := (HistoricalThirdCoarse.P1ActualTuple.cube_tests_iff_log hN (initial e) lambda
    (HistoricalThirdCoarse.P1OriginalFourth.prefix3 p)
    (fun i => hpos ⟨i.val, by omega⟩)).mp ⟨hv.1, hv.2.2.1, hv.2.2.2⟩
  have hthird : actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2 < lambda := by
    simpa only [HistoricalThirdCoarse.P1OriginalFourth.prefix3,
      historicalPrefixProject, actualPrimeTupleLog] using hc.2.2
  have hs := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hd.1
  have h32 := hs (by decide : (2 : Fin 4) < 3)
  have hsum : (∑ i, actualPrimeTupleLog N p i) =
      actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
        actualPrimeTupleLog N p 2 + actualPrimeTupleLog N p 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  unfold rawTupleGap
  rw [rawTupleExponent_eq_of_level hN p hlevel, hsum]
  linarith

/-- A finite wall family enumerates the TRUE source exponent table. -/
abbrev WallIndex (values : Finset ℝ) := Fin (Fintype.card {x : ℝ // x ∈ values})

def finiteWallForms (values : Finset ℝ) : WallIndex values → (Fin 4 → ℝ) →L[ℝ] ℝ :=
  fun _ => wallForm

def finiteWallBounds (values : Finset ℝ) (i : WallIndex values) : ℝ :=
  ((Fintype.equivFin {x : ℝ // x ∈ values}).symm i).val

theorem finiteWallForms_ne_zero (values : Finset ℝ) : ∀ i, finiteWallForms values i ≠ 0 := by
  intro i
  exact wallForm_ne_zero

/-- Scalar fixed-level entry: one-sided gap is inside the public closed strip. -/
theorem scalar_gap_mem_public {values : Finset ℝ} {lambda delta : ℝ}
    (hlambda : lambda ∈ values) (t : Fin 4 → ℝ)
    (hpos : 0 < lambda - (∑ i, t i) - t 3)
    (hsmall : lambda - (∑ i, t i) - t 3 ≤ delta) :
    t ∈ primeAffineWallStrip (finiteWallForms values) (finiteWallBounds values) delta := by
  let v : {x : ℝ // x ∈ values} := ⟨lambda, hlambda⟩
  refine ⟨Fintype.equivFin {x : ℝ // x ∈ values} v, ?_⟩
  have habs : |wallForm t - lambda| ≤ delta := by
    rw [wallForm_eq_sum_last, abs_of_nonpos (by linarith)]
    linarith
  simpa only [finiteWallForms, finiteWallBounds, Equiv.symm_apply_apply, v] using habs

/-- Every original actual near-wall tuple lies in a strip at one actual
initial or selected Gamma-2e exponent; no ceiling replaces that exponent. -/
theorem originalWallTuples_subset_public
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (a b delta delta' : ℝ)
    (hN : 1 < N) (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (hdelta : delta ≤ delta') :
    originalWallTuples e chi m omega N cap a b delta ⊆
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter fun p =>
        actualPrimeTupleLog N p ∈ primeAffineWallStrip
          (finiteWallForms (P1ActualCoarseLevelCeiling.exponentValues e chi m))
          (finiteWallBounds (P1ActualCoarseLevelCeiling.exponentValues e chi m)) delta' := by
  intro p hp
  obtain ⟨ha, hlast, hpos, hsmall⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr
    ⟨original_admitted_mem_cube e chi m omega N cap a b hcap p ha hlast, ?_⟩
  exact scalar_gap_mem_public (rawTupleExponent_mem_values e chi m omega N hN p)
    (actualPrimeTupleLog N p) hpos (hsmall.trans hdelta)

/-- This is the actual rank-four signed reciprocal-prime coefficient. -/
def signedTupleWeight (p : Fin 4 → ℕ) : ℝ :=
  signedTreeCoefficient (evenListLength ((List.ofFn p).reverse))
    (∏ i, 1 / ((p i : ℝ) - 1))

theorem signedTupleWeight_eq (p : Fin 4 → ℕ) :
    signedTupleWeight p = ∏ i, 1 / ((p i : ℝ) - 1) := by
  unfold signedTupleWeight
  rw [signedTreeCoefficient_evenListLength_eq_negOnePow]
  norm_num

/-- The displayed signed tuple weight is exactly the original reverse-history
tree coefficient, including its original mapped reciprocal-prime product. -/
theorem signedTupleWeight_history (history : List ℕ) (hlen : history.length = 4) :
    signedTupleWeight (primeHistoryTuple 4 history) =
      signedTreeCoefficient (evenListLength history)
        ((history.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod) := by
  unfold signedTupleWeight
  rw [primeHistoryTuple_reverse_ofFn hlen, primeHistoryTuple_reciprocal_mass hlen]

def originalSignedWallMass (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (a b delta : ℝ) : ℝ :=
  ∑ p ∈ originalWallTuples e chi m omega N cap a b delta, signedTupleWeight p

/-- The absolute signed mass uses exactly the same actual product weights. -/
theorem originalSignedWallMass_eq_abs_sum
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (a b delta : ℝ)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) :
    originalSignedWallMass e chi m omega N cap a b delta =
      ∑ p ∈ originalWallTuples e chi m omega N cap a b delta, |signedTupleWeight p| := by
  unfold originalSignedWallMass
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨ha, hlast, _hgap⟩ := Finset.mem_filter.mp hp
  have hw := actualPrimeBoxWeight_nonneg
    (original_admitted_mem_cube e chi m omega N cap a b hcap p ha hlast)
  simp only [signedTupleWeight_eq, abs_of_nonneg hw]

/-- Explicit actual prime product-sum domination on the ambient public cube. -/
theorem originalSignedWallMass_le_public
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (a b delta delta' : ℝ)
    (hN : 1 < N) (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (hdelta : delta ≤ delta') :
    |originalSignedWallMass e chi m omega N cap a b delta| ≤
      actualPrimeAffineWallStripMass N (fun _ : Fin 4 => a) (fun _ => b)
        (finiteWallForms (P1ActualCoarseLevelCeiling.exponentValues e chi m))
        (finiteWallBounds (P1ActualCoarseLevelCeiling.exponentValues e chi m)) delta' := by
  have hnonneg : 0 ≤ originalSignedWallMass e chi m omega N cap a b delta := by
    unfold originalSignedWallMass
    apply Finset.sum_nonneg
    intro p hp
    obtain ⟨ha, hlast, _hgap⟩ := Finset.mem_filter.mp hp
    rw [signedTupleWeight_eq]
    exact actualPrimeBoxWeight_nonneg
      (original_admitted_mem_cube e chi m omega N cap a b hcap p ha hlast)
  rw [abs_of_nonneg hnonneg]
  unfold originalSignedWallMass actualPrimeAffineWallStripMass
  simp only [signedTupleWeight_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (originalWallTuples_subset_public e chi m omega N cap a b delta delta' hN hcap hdelta)
  intro p hp _
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- One original-table reserve, uniform in omega/cap and every smaller width.
No levelCheck, Gamma ceiling replacement or residual mean is assumed. -/
theorem exists_originalSignedWallMass_small_widths_lt
    (e chi : ℝ) (m : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ b ≤ (cap : ℝ) →
        ∀ omega delta : ℝ, 0 < delta → delta ≤ delta₀ →
          |originalSignedWallMass e chi m omega N cap a b delta| < eta ∧
          (∑ p ∈ originalWallTuples e chi m omega N cap a b delta,
            |signedTupleWeight p|) < eta := by
  obtain ⟨delta₀, hd₀, N₀, hN₀, hmass⟩ := exists_actualPrimeAffineWallStrip_mass_lt ha hab
    (finiteWallForms (P1ActualCoarseLevelCeiling.exponentValues e chi m))
    (finiteWallBounds (P1ActualCoarseLevelCeiling.exponentValues e chi m))
    (finiteWallForms_ne_zero _) eta heta
  refine ⟨delta₀, hd₀, N₀, hN₀, ?_⟩
  intro N cap hN hcap omega delta _hd hdd₀
  have hn : 1 < N := by omega
  have hsmall := (originalSignedWallMass_le_public
    e chi m omega N cap a b delta delta₀ hn hcap hdd₀).trans_lt (hmass N hN)
  refine ⟨hsmall, ?_⟩
  rw [← originalSignedWallMass_eq_abs_sum e chi m omega N cap a b delta hcap]
  exact (le_abs_self _).trans_lt hsmall

/-- The frozen manuscript's original upper rough carrier is b=19/96. -/
theorem exists_originalSignedWallMass_manuscript_upper_lt
    (e chi : ℝ) (m : ℕ) (a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        ∀ omega delta : ℝ, 0 < delta → delta ≤ delta₀ →
          |originalSignedWallMass e chi m omega N cap a (19 / 96) delta| < eta ∧
          (∑ p ∈ originalWallTuples e chi m omega N cap a (19 / 96) delta,
            |signedTupleWeight p|) < eta := by
  exact exists_originalSignedWallMass_small_widths_lt e chi m a (19 / 96) ha hab eta heta

end P1OriginalCoarseFourthArithmeticWall

end

end ImbalancedChen
