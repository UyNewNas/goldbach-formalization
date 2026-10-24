import ImbalancedChen.ActualThirdOriginalPositive256LogRange32
import ImbalancedChen.ActualThirdOriginalPositive256LogIntegerGuards

/-!
SOURCEONLY / HOLD_ELABORATION / OPEN30.
Original ordinary below-mu raw ln.lo>0 on the original integer coordinate
grid. At k=0 use integer width and the first rounded positive series term.
At k>0 use nonnegative unit_log(reduced).lo and the ORIGINAL rounded
unit_log(2)*V(k) product.lo>=1. No ideal-log-to-raw-floor inference is used.
No original definition, P160,256-term loop, range reduction or bound changes.
-/
namespace ImbalancedChen.OriginalThirdPositiveLogSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly

private theorem range32_unitLog_lo_nonneg {x : ℝ} (h1 : 1≤x) (h2 : x≤2) :
    0≤(unitLog x 256).lo := by
  have hz : (0:ℝ)≤1-1/x := (rounded_z_upper h1 h2).1
  have hfloor : 0≤(ofReal (1-1/x)).lo :=
    Int.floor_nonneg.mpr (mul_nonneg hz P160_real_pos.le)
  have hfirst := originalLnUnit_lo_ge_first h1 h2
  rw [originalLnUnit_eq] at hfirst
  exact hfloor.trans hfirst

/-- The strict positive floor is supplied from all four literal endpoint
products, each >=P160, not from positivity of the real product. -/
private theorem range32_logTwo_nat_mul_lo_pos (k : ℕ) (hk : 0<k) :
    0<(mul (unitLog 2 256) (ofReal (k:ℝ))).lo := by
  have hfirst := originalLnUnit_lo_ge_first (x:=2)
    (by norm_num : (1:ℝ)≤2) le_rfl
  rw [originalLnUnit_eq] at hfirst
  have hfloor : (1:ℤ)≤(ofReal (1-1/(2:ℝ))).lo := by
    change (1:ℤ)≤⌊(1-1/(2:ℝ))*(P160:ℝ)⌋
    apply Int.le_floor.mpr
    norm_num [P160]
  have hlo : (1:ℤ)≤(unitLog 2 256).lo := hfloor.trans hfirst
  have hlog := unitLog_sound (by norm_num : (1:ℝ)≤2) le_rfl 256
  have hvalid : (unitLog 2 256).lo≤(unitLog 2 256).hi :=
    value_le_iff.mp (hlog.1.trans hlog.2)
  have hhi : (1:ℤ)≤(unitLog 2 256).hi := hlo.trans hvalid
  have hkNat : 1≤k := by omega
  have hkReal : (1:ℝ)≤(k:ℝ) := by exact_mod_cast hkNat
  have hklo : P160≤(ofReal (k:ℝ)).lo := by
    change P160≤⌊(k:ℝ)*(P160:ℝ)⌋
    apply Int.le_floor.mpr
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hkReal P160_real_pos.le
  have hkvalid : (ofReal (k:ℝ)).lo≤(ofReal (k:ℝ)).hi :=
    value_le_iff.mp ((ofReal_sound (k:ℝ)).1.trans (ofReal_sound (k:ℝ)).2)
  have hkhi : P160≤(ofReal (k:ℝ)).hi := hklo.trans hkvalid
  have hproduct (a b : ℤ) (ha : 1≤a) (hb : P160≤b) : P160≤a*b := by
    simpa only [one_mul] using mul_le_mul ha hb P160_pos.le
      ((by norm_num : (0:ℤ)≤1).trans ha)
  have hfour : P160≤fourLo (unitLog 2 256) (ofReal (k:ℝ)) :=
    le_min (le_min (hproduct _ _ hlo hklo) (hproduct _ _ hlo hkhi))
      (le_min (hproduct _ _ hhi hklo) (hproduct _ _ hhi hkhi))
  have hdiv : (1:ℤ)≤fourLo (unitLog 2 256) (ofReal (k:ℝ))/P160 :=
    (Int.le_ediv_iff_mul_le P160_pos).mpr (by simpa only [one_mul] using hfour)
  change 0<fourLo (unitLog 2 256) (ofReal (k:ℝ))/P160
  omega

private theorem range32_positive_branch_lo_pos {x : ℝ} (h1 : 1≤x) (h2 : x≤2)
    (k : ℕ) (hk : 0<k) : 0<(originalLogBranch x k).lo := by
  have hunit := range32_unitLog_lo_nonneg h1 h2
  have hproduct := range32_logTwo_nat_mul_lo_pos k hk
  change 0<(unitLog x 256).lo+(mul (unitLog 2 256) (ofReal (k:ℝ))).lo
  omega

private theorem range32_two_lt_lo_pos {x : ℝ} (hx : 2<x) (h32 : x≤32) :
    0<(originalLn32 x).lo := by
  have h0 : ¬x≤2 := not_le.mpr hx
  rw [originalLn32, if_neg h0]
  by_cases h2 : x/2≤2
  · rw [if_pos h2]
    refine range32_positive_branch_lo_pos ?_ h2 1 (by norm_num)
    exact (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2 (by simpa using hx.le)
  · rw [if_neg h2]
    by_cases h4 : x/(2:ℝ)^2≤2
    · rw [if_pos h4]
      refine range32_positive_branch_lo_pos ?_ h4 2 (by norm_num)
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).2
      have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).1 (lt_of_not_ge h2)
      norm_num at h ⊢
      exact h.le
    · rw [if_neg h4]
      by_cases h8 : x/(2:ℝ)^3≤2
      · rw [if_pos h8]
        refine range32_positive_branch_lo_pos ?_ h8 3 (by norm_num)
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).2
        have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).1
          (lt_of_not_ge h4)
        norm_num at h ⊢
        exact h.le
      · rw [if_neg h8]
        have h1 : 1≤x/(2:ℝ)^4 := by
          apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^4)).2
          have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).1
            (lt_of_not_ge h8)
          norm_num at h ⊢
          exact h.le
        have hlast : x/(2:ℝ)^4≤2 := by
          apply (div_le_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^4)).2
          simpa only [show 2*(2:ℝ)^4=32 by norm_num] using h32
        exact range32_positive_branch_lo_pos h1 hlast 4 (by norm_num)

/-- Common original-grid positive divisor theorem. The original positive
integer width gives gap>=1. The original upper corner x1<=mu*D bounds that
integer by P160. The unit branch therefore has a first-term floor>=1; every
positive range-reduction count has its ORIGINAL rounded ln2 multiple.lo>=1.
No desired raw endpoint, semantic log lower bound or width cutoff is assumed. -/
theorem original_integer_below_mu_log32_guard (x0 x1 : ℤ)
    (hx0 : 0<x0) (hwidth : x0<x1)
    (hmu : 128*x1≤25*(48000*2^24:ℤ))
    (h32 : (x1:ℝ)/(x0:ℝ)≤32) :
    0<(originalLn32 ((x1:ℝ)/(x0:ℝ))).lo := by
  have hx0Real : (0:ℝ)<(x0:ℝ) := by exact_mod_cast hx0
  have hwidthReal : (x0:ℝ)<(x1:ℝ) := by exact_mod_cast hwidth
  have hx1Real : (0:ℝ)<(x1:ℝ) := hx0Real.trans hwidthReal
  have h1 : (1:ℝ)≤(x1:ℝ)/(x0:ℝ) :=
    (le_div_iff₀ hx0Real).2 (by simpa only [one_mul] using hwidthReal.le)
  by_cases h2 : (x1:ℝ)/(x0:ℝ)≤2
  · have hgap : (1:ℤ)≤x1-x0 := by omega
    have hsmall : (25:ℤ)*(48000*2^24)≤128*P160 := by norm_num [P160]
    have hx1small : x1≤P160 :=
      (mul_le_mul_left (by norm_num : (0:ℤ)<128)).mp (hmu.trans hsmall)
    have hscaled : x1≤(x1-x0)*P160 :=
      hx1small.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap P160_pos.le)
    have hscaledReal : (x1:ℝ)≤((x1:ℝ)-(x0:ℝ))*(P160:ℝ) := by
      exact_mod_cast hscaled
    have hfirst : (1:ℝ)≤(1-1/((x1:ℝ)/(x0:ℝ)))*(P160:ℝ) := by
      calc
        (1:ℝ)≤((x1:ℝ)-(x0:ℝ))*(P160:ℝ)/(x1:ℝ) :=
          (le_div_iff₀ hx1Real).2 (by simpa only [one_mul] using hscaledReal)
        _ = (1-1/((x1:ℝ)/(x0:ℝ)))*(P160:ℝ) := by
          field_simp [hx0Real.ne', hx1Real.ne'] <;> ring
    have hfloor : (1:ℤ)≤(ofReal (1-1/((x1:ℝ)/(x0:ℝ)))).lo :=
      Int.le_floor.mpr hfirst
    have hlo := hfloor.trans (originalLnUnit_lo_ge_first h1 h2)
    rw [originalLn32, if_pos h2]
    change 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo
    omega
  · exact range32_two_lt_lo_pos (lt_of_not_ge h2) h32

/-- Direct reusable wrapper for one of the original ordinary x/y log
operands. These are literal coordinate bindings, positive width, the original
mu upper corner and the already-proved range-reduction domain. No guard is
an input; in an ordinary box apply this separately to x and y. -/
theorem original_stored_below_mu_log32_guard (x0 x1 : ℤ) (a b : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hapos : (0:ℝ)<(a:ℝ)) (hwidth : (a:ℝ)<(b:ℝ))
    (hmu : (b:ℝ)≤(25:ℝ)/128) (h32 : (b:ℝ)/(a:ℝ)≤32) :
    0<(originalLn32 ((b:ℝ)/(a:ℝ))).lo := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have haReal : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hbReal : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hx0Real : (0:ℝ)<(x0:ℝ) := by
    have h := (lt_div_iff₀ hD).1 (by simpa only [haReal] using hapos)
    simpa only [zero_mul] using h
  have hx0 : 0<x0 := by exact_mod_cast hx0Real
  have hwidthReal : (x0:ℝ)<(x1:ℝ) :=
    (div_lt_div_iff_of_pos_right hD).1 (by simpa only [haReal,hbReal] using hwidth)
  have hwidthInt : x0<x1 := by exact_mod_cast hwidthReal
  have hupper : (x1:ℝ)≤(25:ℝ)/128*((48000*2^24:ℤ):ℝ) :=
    (div_le_iff₀ hD).1 (by simpa only [hbReal] using hmu)
  have hmuInt : 128*x1≤25*(48000*2^24:ℤ) := by
    have h : 128*(x1:ℝ)≤25*((48000*2^24:ℤ):ℝ) := by linarith only [hupper]
    exact_mod_cast h
  have hratio : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haReal,hbReal]
    field_simp [hD.ne', hx0Real.ne']
  rw [hratio] at h32 ⊢
  exact original_integer_below_mu_log32_guard x0 x1 hx0 hwidthInt hmuInt h32

/-- The TWO ordinary log guards together. The upper y corner is bounded by
the original upper x corner through ordinary ordering and positive x width.
The two ratio<=32 facts are precisely the existing below_mu_B_log_ratios
conclusions; no semantic log estimate or desired rounded guard is assumed. -/
theorem original_stored_ordinary_log32_guards
    (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lower i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(upper i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha : ∀ i, (0:ℝ)<(a i:ℝ)) (hab : ∀ i, (a i:ℝ)<(b i:ℝ))
    (hyx : (b 1:ℝ)≤(a 0:ℝ)) (hmu : (b 0:ℝ)≤(25:ℝ)/128)
    (hx32 : (b 0:ℝ)/(a 0:ℝ)≤32) (hy32 : (b 1:ℝ)/(a 1:ℝ)≤32) :
    0<(originalLn32 ((b 0:ℝ)/(a 0:ℝ))).lo ∧
      0<(originalLn32 ((b 1:ℝ)/(a 1:ℝ))).lo := by
  have hmuY : (b 1:ℝ)≤(25:ℝ)/128 := hyx.trans ((hab 0).le.trans hmu)
  exact ⟨original_stored_below_mu_log32_guard (lower 0) (upper 0) (a 0) (b 0)
    (haBind 0) (hbBind 0) (ha 0) (hab 0) hmu hx32,
    original_stored_below_mu_log32_guard (lower 1) (upper 1) (a 1) (b 1)
      (haBind 1) (hbBind 1) (ha 1) (hab 1) hmuY hy32⟩

end
end ImbalancedChen.OriginalThirdPositiveLogSourceOnly
