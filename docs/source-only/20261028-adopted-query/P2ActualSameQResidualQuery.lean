import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import ImbalancedChen.P2LowerCapPlanIntegerRetention
import ImbalancedChen.P2EnhancedLowerPhysicalNode
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Phi/cutoff/Theta use the COMPLETE integer multiplier B.
Selected-subproduct marks certify factorization; they are not deleted
from B or from its logarithmic prefix sum. The physical cutoff exponent
is an independent argument: an L5/L6 root may have cutoff a even though
its last old marked prime is larger than a.

For one fixed total level Q=N^lambda, s=(lambda-S)/xi is the actual
residual query at cutoff N^xi. Ordinary cap replacements have TWO totals
Q_old and Q_new; only descendants of a fixed chosen total are same-Q.
No H/h table, count comparison, Sound field or endpoint licence is an
input. The statements below are exact source-count/normalizer identities.
-/

namespace ImbalancedChen.P2ActualSameQResidualQuery

noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention P2EnhancedLowerPhysicalNode
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneQuotientFinite
open Wu2008DoubleSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def prefixExponent (N : ℕ) (history : List ℕ) : ℝ :=
  (physicalWord N history).sum

def residualExponent (N : ℕ) (total : ℝ) (history : List ℕ) : ℝ :=
  total - prefixExponent N history

def residualQuery (N : ℕ) (total cutoffExponent : ℝ) (history : List ℕ) : ℝ :=
  residualExponent N total history / cutoffExponent

def sourceAlpha (N : ℕ) (total : ℝ) (history : List ℕ) : ℝ :=
  (1 - prefixExponent N history) / residualExponent N total history

theorem complete_multiplier_power {N : ℕ} (hN : (1:ℝ) < N)
    (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p) :
    (N:ℝ) ^ prefixExponent N history = (history.prod:ℝ) :=
  physicalWord_power hN history hpos

theorem actual_residual_level {N : ℕ} (hN : (1:ℝ) < N)
    (total : ℝ) (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p) :
    (N:ℝ)^total / (history.prod:ℝ) = (N:ℝ)^residualExponent N total history := by
  rw [← complete_multiplier_power hN history hpos]
  exact (Real.rpow_sub (zero_lt_one.trans hN)).symm

theorem residual_log {N : ℕ} (hN : (1:ℝ) < N)
    (total : ℝ) (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p) :
    Real.log ((N:ℝ)^total / (history.prod:ℝ)) =
      residualExponent N total history * Real.log N := by
  rw [actual_residual_level hN total history hpos,
    Real.log_rpow (zero_lt_one.trans hN)]

theorem original_cutoff_uniform_query {N : ℕ} (hN : (1:ℝ) < N)
    (total s : ℝ) (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p) :
    cutoff ((N:ℝ)^total) history.prod s =
      (N:ℝ)^(residualExponent N total history / s) := by
  rw [cutoff,actual_residual_level hN total history hpos,
    ← Real.rpow_mul (zero_lt_one.trans hN).le]
  congr 1
  ring

/-- The original local Phi cutoff is recovered from the independently
    specified physical cutoff, not by naming a candidate query as itself. -/
theorem original_cutoff_of_actual_query {N : ℕ} (hN : (1:ℝ) < N)
    (total xi : ℝ) (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p)
    (hL : 0 < residualExponent N total history) (hxi : 0 < xi) :
    cutoff ((N:ℝ)^total) history.prod (residualQuery N total xi history) = (N:ℝ)^xi := by
  rw [original_cutoff_uniform_query hN total _ history hpos]
  congr 1
  unfold residualQuery
  field_simp [hL.ne',hxi.ne'] <;> ring

theorem actual_query_positive {N : ℕ} (total xi : ℝ) (history : List ℕ)
    (hL : 0 < residualExponent N total history) (hxi : 0 < xi) :
    0 < residualQuery N total xi history := div_pos hL hxi

theorem actual_residual_gt_one {N : ℕ} (hN : (1:ℝ) < N)
    (total : ℝ) (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p)
    (hL : 0 < residualExponent N total history) :
    1 < (N:ℝ)^total / (history.prod:ℝ) := by
  rw [actual_residual_level hN total history hpos]
  exact Real.one_lt_rpow hN hL

/-- Variable physical cutoffs give variable local queries. They must not
    silently be called one constant-argument Phi. -/
def physicalPhi (N : ℕ) (D : Finset ℕ) (sigma : ℕ → ℝ) (xi : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * (sourceSieveCount N d (d*N) ((N:ℝ)^(xi d)) : ℝ)

theorem physicalPhi_eq_actual_local_queries {N : ℕ} (hN : (1:ℝ) < N)
    (total : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (history : ℕ → List ℕ) (xi : ℕ → ℝ)
    (hprod : ∀ d ∈ D, (history d).prod = d)
    (hpos : ∀ d ∈ D, ∀ p ∈ history d, 0 < p)
    (hL : ∀ d ∈ D, 0 < residualExponent N total (history d))
    (hxi : ∀ d ∈ D, 0 < xi d) :
    physicalPhi N D sigma xi =
      ∑ d ∈ D, sigma d * (sourceSieveCount N d (d*N)
        (cutoff ((N:ℝ)^total) d (residualQuery N total (xi d) (history d))) : ℝ) := by
  apply Finset.sum_congr rfl
  intro d hd
  have hc := original_cutoff_of_actual_query hN total (xi d) (history d)
    (hpos d hd) (hL d hd) (hxi d hd)
  rw [hprod d hd] at hc
  rw [hc]

/-- In the ORIGINAL constant-query Phi, the actual cutoff exponent is
    residual/s separately for each complete prefix d. -/
theorem original_Phi_eq_physical_cutoffs {N : ℕ} (hN : (1:ℝ) < N)
    (total s : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (history : ℕ → List ℕ) (hprod : ∀ d ∈ D, (history d).prod = d)
    (hpos : ∀ d ∈ D, ∀ p ∈ history d, 0 < p) :
    Phi N ((N:ℝ)^total) D sigma s =
      physicalPhi N D sigma (fun d => residualExponent N total (history d) / s) := by
  unfold Phi physicalPhi
  apply Finset.sum_congr rfl
  intro d hd
  have hc := original_cutoff_uniform_query hN total s (history d) (hpos d hd)
  rw [hprod d hd] at hc
  rw [hc]

/-- The same original normalizer has the true COMPLETE-prefix residual
    in its denominator; selected-subproduct sums do not replace it. -/
theorem original_Theta_eq_residual_mean {N : ℕ} (hN : (1:ℝ) < N)
    (total : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (history : ℕ → List ℕ) (hprod : ∀ d ∈ D, (history d).prod = d)
    (hpos : ∀ d ∈ D, ∀ p ∈ history d, 0 < p)
    (hL : ∀ d ∈ D, 0 < residualExponent N total (history d)) :
    Theta N ((N:ℝ)^total) D sigma =
      (4 * logarithmicIntegral N / Real.log N) *
        ∑ d ∈ D, sigma d * wuSingularSeries (d*N) /
          ((Nat.totient d:ℝ) * residualExponent N total (history d)) := by
  have hlog : Real.log (N:ℝ) ≠ 0 := (Real.log_pos hN).ne'
  have hsum :
      (∑ d ∈ D, sigma d * wuSingularSeries (d*N) /
        ((Nat.totient d:ℝ) * Real.log ((N:ℝ)^total / d))) =
      (1 / Real.log N) *
        ∑ d ∈ D, sigma d * wuSingularSeries (d*N) /
          ((Nat.totient d:ℝ) * residualExponent N total (history d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hlogd := residual_log hN total (history d) (hpos d hd)
    rw [hprod d hd] at hlogd
    rw [hlogd]
    have hdp : 0 < d := by
      have hp := Real.rpow_pos_of_pos (zero_lt_one.trans hN)
        (prefixExponent N (history d))
      rw [complete_multiplier_power hN (history d) (hpos d hd),hprod d hd] at hp
      exact_mod_cast hp
    have hphi : (Nat.totient d:ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr hdp)).ne'
    field_simp [hlog,hphi,(hL d hd).ne']
    <;> ring
  unfold Theta
  rw [hsum]
  ring

/-- A source node retains all original selected tags, but complete prefix
    sum, residual, alpha and query are independent of those tags. -/
def tagWord (mark : ℕ → Bool) : List ℝ → List Slot
  | [] => []
  | x::xs => ⟨x,mark 0⟩ :: tagWord (fun i => mark (i+1)) xs

theorem tagWord_exponents (mark : ℕ → Bool) (xs : List ℝ) :
    (tagWord mark xs).map Slot.exponent = xs := by
  induction xs generalizing mark with
  | nil => rfl
  | cons x xs ih => simp only [tagWord,List.map_cons,ih]

def integerNode (occurrence : Fin 11) (N : ℕ) (total ceiling xi : ℝ)
    (history : List ℕ) (mark : ℕ → Bool) : PhysicalNode :=
  ⟨occurrence,total,tagWord mark (physicalWord N history),ceiling,
    residualQuery N total xi history⟩

theorem integerNode_actual_query (occurrence : Fin 11) (N : ℕ)
    (total ceiling xi : ℝ) (history : List ℕ) (mark : ℕ → Bool) :
    word (integerNode occurrence N total ceiling xi history mark) = physicalWord N history ∧
      residual (integerNode occurrence N total ceiling xi history mark) =
        residualExponent N total history ∧
      (integerNode occurrence N total ceiling xi history mark).argument =
        residual (integerNode occurrence N total ceiling xi history mark) / xi ∧
      alpha (integerNode occurrence N total ceiling xi history mark) = sourceAlpha N total history := by
  simp [integerNode,word,tagWord_exponents,residual,residualExponent,
    residualQuery,prefixExponent,alpha,sourceAlpha]

def bindQuery (n : PhysicalNode) (xi : ℝ) : PhysicalNode :=
  compareAt n (residual n / xi)

theorem bindQuery_preserves_physical_state (n : PhysicalNode) (xi : ℝ) :
    (bindQuery n xi).total = n.total ∧ (bindQuery n xi).slots = n.slots ∧
      (bindQuery n xi).ceiling = n.ceiling ∧ residual (bindQuery n xi) = residual n ∧
      alpha (bindQuery n xi) = alpha n ∧
      fullGates (bindQuery n xi) = fullGates n ∧
      selectedGates (bindQuery n xi) = selectedGates n ∧
      (bindQuery n xi).argument = residual n / xi := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A genuine same-Q singleton changes the COMPLETE prefix and residual;
    it does not reset the source exponent or alpha to a seed value. -/
theorem sameQ_singleton_dictionary (n : PhysicalNode) (x s : ℝ)
    (hL : 0 < residual n) (hx : x < residual n) :
    (appendOne n x s).total = n.total ∧
      residual (appendOne n x s) = residual n-x ∧
      alpha (appendOne n x s) =
        1 + (alpha n-1)/(1-x/residual n) := by
  refine ⟨rfl,residual_appendOne n x s,?_⟩
  have hd : residual n-x ≠ 0 := (sub_pos.mpr hx).ne'
  have hden : 1-x/residual n ≠ 0 :=
    (sub_pos.mpr ((div_lt_one hL).mpr hx)).ne'
  unfold alpha
  rw [word_appendOne,residual_appendOne]
  simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero]
  field_simp [hL.ne',hd,hden] <;> ring

theorem sameQ_pair_dictionary (n : PhysicalNode) (x y s : ℝ)
    (hL : 0 < residual n) (hxy : x+y < residual n) :
    (appendPair n x y s).total = n.total ∧
      residual (appendPair n x y s) = residual n-y-x ∧
      alpha (appendPair n x y s) =
        1 + (alpha n-1)/(1-(x+y)/residual n) := by
  refine ⟨rfl,residual_appendPair n x y s,?_⟩
  have hd : residual n-y-x ≠ 0 := by linarith
  have hden : 1-(x+y)/residual n ≠ 0 :=
    (sub_pos.mpr ((div_lt_one hL).mpr hxy)).ne'
  unfold alpha
  rw [word_appendPair,residual_appendPair]
  simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero]
  field_simp [hL.ne',hd,hden] <;> ring

def singletonQueryReceiver (n : PhysicalNode) (x xi : ℝ) : PhysicalNode :=
  bindQuery (appendOne n x 0) xi

def pairQueryReceiver (n : PhysicalNode) (x y xi : ℝ) : PhysicalNode :=
  bindQuery (appendPair n x y 0) xi

theorem sameQ_actual_child_queries (n : PhysicalNode) (x y xi : ℝ) :
    (singletonQueryReceiver n x xi).total = n.total ∧
      (singletonQueryReceiver n x xi).argument = (residual n-x)/xi ∧
      (pairQueryReceiver n x y xi).total = n.total ∧
      (pairQueryReceiver n x y xi).argument = (residual n-y-x)/xi ∧
      selectedWord (singletonQueryReceiver n x xi).slots = selectedWord n.slots ∧
      selectedWord (pairQueryReceiver n x y xi).slots = selectedWord n.slots := by
  simp [singletonQueryReceiver,pairQueryReceiver,bindQuery,compareAt,
    residual_appendOne,residual_appendPair,selected_appendOne,selected_appendPair]

/-- Altering source tags alone cannot turn a complete-prefix query into
    a selected-complement query. No assertion about changed weights or
    changed source eligibility is made. -/
theorem query_ignores_retagging (occurrence : Fin 11) (N : ℕ)
    (total ceiling xi : ℝ) (history : List ℕ) (mark1 mark2 : ℕ → Bool) :
    (integerNode occurrence N total ceiling xi history mark1).argument =
      (integerNode occurrence N total ceiling xi history mark2).argument ∧
      alpha (integerNode occurrence N total ceiling xi history mark1) =
        alpha (integerNode occurrence N total ceiling xi history mark2) := by
  constructor
  · rfl
  · simp [integerNode,alpha,residual,word,tagWord_exponents]

/-- Rectangular physical data give a genuine whole-box QUERY INTERVAL.
    A midpoint is not substituted for this interval. -/
theorem whole_box_query_interval {lambda lambdaLo lambdaHi S SLo SHi xi xiLo xiHi : ℝ}
    (hlam : lambdaLo ≤ lambda ∧ lambda ≤ lambdaHi)
    (hS : SLo ≤ S ∧ S ≤ SHi) (hxi : xiLo ≤ xi ∧ xi ≤ xiHi)
    (hxiLo : 0 < xiLo) (hLLo : 0 < lambdaLo-SHi) :
    (lambdaLo-SHi)/xiHi ≤ (lambda-S)/xi ∧
      (lambda-S)/xi ≤ (lambdaHi-SLo)/xiLo := by
  have hx : 0 < xi := hxiLo.trans_le hxi.1
  have hxHi : 0 < xiHi := hx.trans_le hxi.2
  have hL : 0 ≤ lambda-S := by linarith
  have hLHi : 0 ≤ lambdaHi-SLo := by linarith
  constructor
  · calc
      (lambdaLo-SHi)/xiHi ≤ (lambda-S)/xiHi :=
        div_le_div_of_nonneg_right (by linarith) hxHi.le
      _ ≤ (lambda-S)/xi := (div_le_div_iff₀ hxHi hx).mpr
        (mul_le_mul_of_nonneg_left hxi.2 hL)
  · calc
      (lambda-S)/xi ≤ (lambdaHi-SLo)/xi :=
        div_le_div_of_nonneg_right (by linarith) hx.le
      _ ≤ (lambdaHi-SLo)/xiLo := (div_le_div_iff₀ hx hxiLo).mpr
        (mul_le_mul_of_nonneg_left hxi.1 hLHi)

/-- Different uses of the endpoint two remain different functions. -/
def upper430Argument (s : ℝ) : ℝ := max 2 s
def lower248Correction (h : ℝ → ℝ) (s : ℝ) : ℝ := if 2 ≤ s then h s else 0

theorem upper430_clamp (s : ℝ) (hs : s ≤ 2) : upper430Argument s = 2 := max_eq_left hs
theorem lower248_below (h : ℝ → ℝ) (s : ℝ) (hs : s < 2) :
    lower248Correction h s = 0 := by simp [lower248Correction,not_le.mpr hs]
theorem lower248_at_two (h : ℝ → ℝ) : lower248Correction h 2 = h 2 := by
  simp [lower248Correction]

end
end ImbalancedChen.P2ActualSameQResidualQuery
