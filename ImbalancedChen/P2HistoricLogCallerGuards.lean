import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
import ImbalancedChen.P2HistoricChordDivisorGuard
import ImbalancedChen.Certificates.PairedV2FullMask

/-!
SOURCE ONLY / UNCOMPILED.

Actual nonenhanced/nondiagonal pair_cell in certify_sharp_184_baseline.py
(a4ebffaf2b13123cf8d7510fed18482f85ec1a79f1bcddb220bd3d3ec8197639)
calls log(I(tR/tL)) and log(I(uR/uL)). Its affine moments reuse these two
cached logs; there is no additional logarithm of an affine expression in
this branch. All 512-by-512 parent rectangles, hence every adopted row,
have both ratios >=1 and strictly positive rounded I80 lower endpoints.

The interval wrapper below keeps the original positive rounded-lower guard
for arbitrary intervals. Actual grid specializations prove that guard from
the imported knots. The final ordinary-estimator adapter removes both
logarithm-query premises, retaining the separate sf/divisor obligations.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogCallerGuards

open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter
open PairedV2
open ImbalancedChen.P2SavedFloorSemantics
open ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness

noncomputable section

/-- Literal log(I80): lower output from log_point(lo), upper from log_point(hi). -/
def logInterval (x : I80) : I80 :=
  ⟨(logPoint x.lo).lo, (logPoint x.hi).hi⟩

theorem logInterval_point (q : ℚ) : logInterval (I80.point q) = logI q := by
  rfl

/-- Monotone endpoint wrapper for every actually positive I80 interval. -/
theorem logInterval_contains {x : I80} {v : ℝ}
    (hx : x.Contains v) (hlo : 0 < x.lo) :
    (logInterval x).Contains (Real.log v) := by
  obtain ⟨hxl, hxh⟩ := (contains_iff x v).mp hx
  have hlR : 0 < decode x.lo :=
    div_pos (by exact_mod_cast hlo) Q_real_pos
  have hv : 0 < v := hlR.trans_le hxl
  have hhi : 0 < x.hi := by
    have hh : (0 : ℝ) < decode x.hi := hv.trans_le hxh
    have hh' := (lt_div_iff₀ Q_real_pos).mp hh
    have hiR : (0 : ℝ) < x.hi := by simpa using hh'
    exact_mod_cast hiR
  have hlogL := (contains_iff _ _).mp (logPoint_contains hlo)
  have hlogH := (contains_iff _ _).mp (logPoint_contains hhi)
  apply (contains_iff _ _).mpr
  exact ⟨hlogL.1.trans (Real.log_le_log hlR hxl),
    (Real.log_le_log hv hxh).trans hlogH.2⟩

theorem point_lo_ge_Q_of_one_le (q : ℚ) (hq : 1 ≤ q) :
    (Q : ℤ) ≤ (I80.point q).lo := by
  change (Q : ℤ) ≤ ⌊q * (Q : ℚ)⌋
  apply Int.le_floor.mpr
  simpa only [Int.cast_natCast, one_mul] using
    mul_le_mul_of_nonneg_right hq Q_pos.le

theorem point_lo_pos_of_one_le (q : ℚ) (hq : 1 ≤ q) :
    0 < (I80.point q).lo := by
  exact Q_int_pos.trans_le (point_lo_ge_Q_of_one_le q hq)

theorem rectangle_ratio_guards {tl tr ul ur : ℚ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    1 ≤ tr / tl ∧ 1 ≤ ur / ul := by
  constructor
  · exact (le_div_iff₀ htl).mpr (by simpa using ht)
  · exact (le_div_iff₀ hul).mpr (by simpa using hu)

/-- No local log enclosure or rounded-lower-endpoint hypothesis is needed
after the actual positive ordered rectangle endpoints are supplied. -/
theorem rectangle_log_contract {tl tr ul ur : ℚ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    (logI (tr / tl)).Contains (Real.log ((tr / tl : ℚ) : ℝ)) ∧
      (logI (ur / ul)).Contains (Real.log ((ur / ul : ℚ) : ℝ)) := by
  obtain ⟨hT, hU⟩ := rectangle_ratio_guards htl hul ht hu
  exact ⟨logI_contains _ (point_lo_pos_of_one_le _ hT),
    logI_contains _ (point_lo_pos_of_one_le _ hU)⟩

/-- All imported t-grid knots have positive width and positive endpoints. -/
theorem t_grid_endpoints (i : ℕ) : 0 < tLower i ∧ tLower i < tUpper i := by
  have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg _
  constructor <;> norm_num [tLower, tUpper, mu, d] <;> linarith

theorem u_grid_endpoints (j : ℕ) : 0 < uLower j ∧ uLower j < uUpper j := by
  have hj : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg _
  constructor <;> norm_num [uLower, uUpper, PairedV2.a, h] <;> linarith

theorem t_grid_high_branch (i : ℕ) : (25 / 128 : ℚ) ≤ tLower i := by
  have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg _
  norm_num [tLower, mu, d] <;> linarith

theorem grid_ratio_guards (i j : ℕ) :
    1 ≤ tUpper i / tLower i ∧ 1 ≤ uUpper j / uLower j := by
  exact rectangle_ratio_guards (t_grid_endpoints i).1 (u_grid_endpoints j).1
    (t_grid_endpoints i).2.le (u_grid_endpoints j).2.le

/-- Actual primitive `assert x.lo > 0` for both source log calls. -/
theorem grid_log_caller_guards (i j : ℕ) :
    0 < (I80.point (tUpper i / tLower i)).lo ∧
      0 < (I80.point (uUpper j / uLower j)).lo := by
  exact ⟨point_lo_pos_of_one_le _ (grid_ratio_guards i j).1,
    point_lo_pos_of_one_le _ (grid_ratio_guards i j).2⟩

theorem all_512_parent_log_guards : ∀ i j : Fin 512,
    0 < (I80.point (tUpper i.val / tLower i.val)).lo ∧
      0 < (I80.point (uUpper j.val / uLower j.val)).lo := by
  intro i j
  exact grid_log_caller_guards i.val j.val

theorem adopted_row_log_guards (r : FullMask.Row) :
    0 < (I80.point (tUpper (FullMask.indices r).1 / tLower (FullMask.indices r).1)).lo ∧
      0 < (I80.point (uUpper (FullMask.indices r).2 / uLower (FullMask.indices r).2)).lo := by
  exact grid_log_caller_guards _ _

theorem grid_log_contract (i j : ℕ) :
    (logI (tUpper i / tLower i)).Contains
        (Real.log ((tUpper i / tLower i : ℚ) : ℝ)) ∧
      (logI (uUpper j / uLower j)).Contains
        (Real.log ((uUpper j / uLower j : ℚ) : ℝ)) := by
  exact rectangle_log_contract (t_grid_endpoints i).1 (u_grid_endpoints j).1
    (t_grid_endpoints i).2.le (u_grid_endpoints j).2.le

/-- Exact source expressions: non-diagonal mass and its two affine moments
reuse the same two cached log(I(ratio)) values. -/
theorem rectangle_source_formulas (tl tr ul ur : ℚ) :
    rectangleMass logI tl tr ul ur =
        (logInterval (I80.point (tr / tl))).mul (logInterval (I80.point (ur / ul))) ∧
      rectangleMomentT logI tl tr ul ur =
        (I80.point (tr - tl)).mul (logInterval (I80.point (ur / ul))) ∧
      rectangleMomentU logI tl tr ul ur =
        (I80.point (ur - ul)).mul (logInterval (I80.point (tr / tl))) := by
  exact ⟨rfl, rfl, rfl⟩

theorem grid_rectangle_mass_moments (i j : ℕ) :
    (rectangleMass logI (tLower i) (tUpper i) (uLower j) (uUpper j)).Contains
        (rectangleMassValue (tLower i) (tUpper i) (uLower j) (uUpper j)) ∧
      (rectangleMomentT logI (tLower i) (tUpper i) (uLower j) (uUpper j)).Contains
        (rectangleMomentTValue (tLower i) (tUpper i) (uLower j) (uUpper j)) ∧
      (rectangleMomentU logI (tLower i) (tUpper i) (uLower j) (uUpper j)).Contains
        (rectangleMomentUValue (tLower i) (tUpper i) (uLower j) (uUpper j)) := by
  obtain ⟨hT, hU⟩ := grid_log_contract i j
  exact ⟨rectangleMass_contains logI _ _ _ _ hT hU,
    rectangleMomentT_contains logI _ _ _ _ hU,
    rectangleMomentU_contains logI _ _ _ _ hT⟩

theorem adopted_rectangle_mass_moments (r : FullMask.Row) :
    (rectangleMass logI (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
        (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)).Contains
        (rectangleMassValue (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
          (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)) ∧
      (rectangleMomentT logI (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
        (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)).Contains
        (rectangleMomentTValue (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
          (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)) ∧
      (rectangleMomentU logI (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
        (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)).Contains
        (rectangleMomentUValue (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
          (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2)) := by
  exact grid_rectangle_mass_moments _ _

/-- Ordinary-estimator soundness with the historical log backend completely
closed. The sf backend and eligible chord divisors retain their own licences. -/
theorem savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (tl tr ul ur : ℚ) (htl : (0 : ℝ) < tl) (hul : (0 : ℝ) < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur) (hHigh : (25 / 128 : ℚ) ≤ tl)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hden₀ : chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₀ tl tr ul ur).2 -
        (affineRange ordinaryPlane₀ tl tr ul ur).1)).lo)
    (hden₁ : chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₁ tl tr ul ur).2 -
        (affineRange ordinaryPlane₁ tl tr ul ur).1)).lo) :
    ((((savedOrdinaryRectangle sf logI tl tr ul ur : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have htlQ : (0 : ℚ) < tl := by exact_mod_cast htl
  have hulQ : (0 : ℚ) < ul := by exact_mod_cast hul
  obtain ⟨hT, hU⟩ := rectangle_log_contract htlQ hulQ ht hu
  exact savedOrdinaryRectangle_actual_lower sf logI tl tr ul ur
    htl hul ht hu hHigh hsf hT hU hden₀ hden₁

/-- Concrete 512-parent consumer: the existing actual knot divisor theorem
and this module's literal log contracts remove every log/divisor query
guard. The separate sf semantic licence is the only backend premise. -/
theorem parent_savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (i j : Fin 512)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ))) :
    ((((savedOrdinaryRectangle sf logI (tLower i.val) (tUpper i.val)
      (uLower j.val) (uUpper j.val) : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val) := by
  obtain ⟨hT, hU⟩ := grid_log_contract i.val j.val
  exact ImbalancedChen.P2HistoricChordDivisorGuard.parent_savedOrdinaryRectangle_actual_lower
    sf logI i.val j.val i.isLt j.isLt hsf hT hU

/-- Every one of the 17572 actual adopted rows receives the same fully
closed log/divisor backend, without an arbitrary global log guard. -/
theorem adopted_savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (r : FullMask.Row)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ))) :
    ((((savedOrdinaryRectangle sf logI
      (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
      (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2) : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral
        (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
        (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2) := by
  obtain ⟨hi, _, hj⟩ := FullMask.indices_bounds r
  exact parent_savedOrdinaryRectangle_actual_lower_logClosed sf
    ⟨(FullMask.indices r).1, hi⟩ ⟨(FullMask.indices r).2, hj⟩ hsf

end

end ImbalancedChen.Certificates.P2HistoricLogCallerGuards
