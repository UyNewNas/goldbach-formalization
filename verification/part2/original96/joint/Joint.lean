import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQueryAllBranches
import ImbalancedChen.P0RationalQueryPublicAPI
import ImbalancedChen.P2HistoricBackendTypeAdapters
import ImbalancedChen.P5ZU1011AutomaticBuchstabIntervals
import ImbalancedChen.P2OriginalCompactQ80Table
import ImbalancedChen.Certificates.P2OriginalLog96
import ImbalancedChen.Certificates.P2OriginalP160DirectDivision
import Lean.Elab.Command
import Lean.Util.CollectAxioms
#check ImbalancedChen.P0All40PublicQuery.query_encloses_all
#check ImbalancedChen.P0All40PublicQuery.query_eq_original_all
#check ImbalancedChen.P0All40PublicQuery.public_query_encloses_all
#check ImbalancedChen.P0All40PublicQuery.query_integer_encloses_all
#check ImbalancedChen.P0All40PublicQuery.query_range_encloses_all
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.pointQuery_sound
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.pointQuery_int_div
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.literalPointQuery_sound
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.rational_endpoints_sound
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.rangeQuery_sound
#check ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly.rangeQuery_rational_bounds
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceSf_delegation
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceSf_lo_exact
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceSf_hi_exact
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceSf_contains_actual
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceLogI_lo_exact
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceLogI_hi_exact
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceLogI_contains
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceLogI_contains_of_one_le
#check ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters.sourceLogI_ratio_contains
#check ImbalancedChen.P5Z.AutomaticBuchstabIntervals.actual_interval_bounds
#check ImbalancedChen.P5Z.AutomaticBuchstabIntervals.actual_interval_width
#check ImbalancedChen.P2OriginalCompactQ80TableSourceOnly.table12_encloses_actual
#check ImbalancedChen.P2OriginalCompactQ80TableSourceOnly.numerator12_contains_actual_L
#check ImbalancedChen.P2OriginalCompactQ80TableSourceOnly.point12_contains_actual
#check ImbalancedChen.P2OriginalCompactQ80TableSourceOnly.sf12_contains_actual
#check ImbalancedChen.Certificates.P2OriginalLog96.logInterval_contains
#check ImbalancedChen.Certificates.P2OriginalLog96.logInterval_eq_source
#check ImbalancedChen.Certificates.P2OriginalP160DirectDivision.directDiv_eq_round160
#check ImbalancedChen.Certificates.P2OriginalP160DirectDivision.directDiv_contains

open ImbalancedChen.OriginalThirdClippedChordSourceOnly
open ImbalancedChen.OriginalThirdRoundedNewSourceOnly
open ImbalancedChen.Certificates.P2OriginalLog96

-- Python Interval(lo,hi,True) retains both integer arguments.
example (lo hi : ℤ) : ((IV.mk lo hi).lo, (IV.mk lo hi).hi) = (lo, hi) := rfl

-- The canonical rational denominator is positive and both integers match
-- the original floor and signed ceiling of the scaled rational point.
example (q : ℚ) : ofReal (q : ℝ) =
    ⟨q.num * P160 / (q.den : ℤ), -((-(q.num * P160)) / (q.den : ℤ))⟩ := by
  have hq : (q : ℝ) = (q.num : ℝ) / ((q.den : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using
      (Rat.cast_def q : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ))
  rw [hq]
  exact ofReal_int_div_source q.num (q.den : ℤ) (by exact_mod_cast q.den_pos)

example (q : ℚ) : Encloses (ofReal (q : ℝ)) (q : ℝ) := ofReal_sound _

-- These examples use the source's raw endpoint pairs directly, including
-- the reversal of the endpoints under unary negation.
example (x y : IV) (v w : ℝ) (hx : Encloses x v) (hy : Encloses y w) :
    Encloses ⟨x.lo + y.lo, x.hi + y.hi⟩ (v + w) :=
  ⟨(value_add _ _).le.trans (add_le_add hx.1 hy.1),
   (add_le_add hx.2 hy.2).trans (value_add _ _).ge⟩

example (x : IV) (v : ℝ) (hx : Encloses x v) :
    Encloses ⟨-x.hi, -x.lo⟩ (-v) := by
  have hneg (i : ℤ) : value (-i) = -value i := by
    simpa only [zero_sub, value_zero] using value_sub 0 i
  exact ⟨(hneg x.hi).le.trans (neg_le_neg hx.2),
    (neg_le_neg hx.1).trans (hneg x.lo).ge⟩

example (x y : IV) : sub x y = ⟨x.lo + -y.hi, x.hi + -y.lo⟩ := by
  simp only [sub, sub_eq_add_neg]

example (x y : IV) (v w : ℝ) (hx : Encloses x v) (hy : Encloses y w) :
    Encloses (sub x y) (v - w) := sub_sound hx hy

example (x y : IV) : mul x y =
    ⟨min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi)) / P160,
     up (max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi))) P160⟩ :=
  rfl

example (x y : IV) (v w : ℝ) (hx : Encloses x v) (hy : Encloses y w) :
    Encloses (mul x y) (v * w) := mul_sound hx hy

-- This is the exact output pair returned by the 96-term producer, with no
-- additional rounding or extra positivity assumption on its lower endpoint.
example (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    Encloses ⟨(logInterval q).1, (logInterval q).2⟩ (Real.log (q : ℝ)) :=
  logInterval_contains q h1 h2

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean moduleName
    let row := Json.mkObj [("module", toJson moduleName.toString), ("olean", toJson path.toString)]
    liftIO <| IO.println s!"P21_IMPORT {row.compress}"
