import ImbalancedChen.CurrentNumericalTransfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exact budgets for two eighteen-term upper-density candidates

The four positive and eighteen negative rational inputs are quoted from the
manuscript repository at `ba6ec11d800eccc54406490631895e174de85766`.
`verification/parts/takeover-budget/check_inputs.py` records their JSON fields,
exact values, and pinned blob hashes. It checks provenance and arithmetic, not
the analytic validity of any integral certificate.

Slots 7, 15, and 18 (one-based) replace earlier estimates on the same domains;
they are never added to their earlier versions. The weaker table uses those
three earlier estimates, eliminating the need for their later refinements in
this numerical budget. Both tables leave room below the *current* `currentK`.

No theorem here constructs a sieve policy, proves disjointness of the domains,
replays their integral certificates, or proves a bound on representation counts.
Using either budget requires a common actual policy, its integral decomposition,
and proved upper/lower bounds for the actual positive/saving components.
-/

namespace ImbalancedChen

open scoped BigOperators

noncomputable section

/-- `4 / Theta`, first-stop integral, compact third integral, and third tail. -/
def currentUpperEighteenPositive : Fin 4 → ℝ :=
  ![2000 / 299,
    7179974843999672947 / 2^73,
    144590669409566793572719 / 2^80,
    319683857488126290909150567 / 2^111]

/-- Quoted saving estimates, in the numbered order of the provenance record. -/
def currentUpperEighteenGains : Fin 18 → ℝ :=
  ![10601625247768616959055 / 2^78,
    3037921066812732539869 / 2^78,
    1648717268323516459667 / 2^80,
    145496122603609407505 / 2^77,
    640339 / 15210735000,
    3097012678584315027795429 / 2^96,
    1208544915921356327515701 / 2^96,
    148834609033428677786865 / 2^96,
    306737545112876482463163 / 2^96,
    187277743940187526723019 / 2^96,
    670429887277013841791829 / 2^96,
    198410119216276585672773 / 2^95,
    5023185001132087792027 / 2^93,
    581521529176619227721 / 2^92,
    74558208451675327462975 / 2^96,
    1222997719565324892497827 / 2^96,
    467454156274267811817033 / 2^96,
    1033407531585213315823239 / 2^96]

/-- Same eighteen slots, with three less refined estimates on unchanged domains. -/
def currentUpperEighteenWeakGains : Fin 18 → ℝ :=
  ![10601625247768616959055 / 2^78,
    3037921066812732539869 / 2^78,
    1648717268323516459667 / 2^80,
    145496122603609407505 / 2^77,
    640339 / 15210735000,
    3097012678584315027795429 / 2^96,
    1201130581437641342320905 / 2^96,
    148834609033428677786865 / 2^96,
    306737545112876482463163 / 2^96,
    187277743940187526723019 / 2^96,
    670429887277013841791829 / 2^96,
    198410119216276585672773 / 2^95,
    5023185001132087792027 / 2^93,
    581521529176619227721 / 2^92,
    74010257929342545968375 / 2^96,
    1222997719565324892497827 / 2^96,
    467454156274267811817033 / 2^96,
    509255822034269351804717 / 2^95]

/-- The quoted refined candidate, before any asymptotic/compiler reserve. -/
def currentUpperEighteenRaw : ℝ :=
  (∑ i, currentUpperEighteenPositive i) - ∑ i, currentUpperEighteenGains i

/-- The quoted less refined candidate, before any asymptotic/compiler reserve. -/
def currentUpperEighteenWeakRaw : ℝ :=
  (∑ i, currentUpperEighteenPositive i) - ∑ i, currentUpperEighteenWeakGains i

/-- Two independent errors can each be budgeted by this positive constant. -/
def currentUpperEighteenReserve : ℝ := 1 / 200000

theorem currentUpperEighteenReserve_pos : 0 < currentUpperEighteenReserve := by
  norm_num [currentUpperEighteenReserve]

/-- Exact finite recombination; it is not an integral identity. -/
theorem currentUpperEighteenRaw_eq :
    currentUpperEighteenRaw =
      9979708415836147068815329797395632360011359959 /
        1475913550962201227946780619099353215139840000 := by
  norm_num [currentUpperEighteenRaw, currentUpperEighteenPositive,
    currentUpperEighteenGains, Fin.sum_univ_succ]

/-- Exact finite recombination after reverting the three estimates. -/
theorem currentUpperEighteenWeakRaw_eq :
    currentUpperEighteenWeakRaw =
      9979708841652996859365606449583844615816799959 /
        1475913550962201227946780619099353215139840000 := by
  norm_num [currentUpperEighteenWeakRaw, currentUpperEighteenPositive,
    currentUpperEighteenWeakGains, Fin.sum_univ_succ]

/-- Each earlier quoted estimate is no larger than its replacement. -/
theorem currentUpperEighteenWeakGains_le (i : Fin 18) :
    currentUpperEighteenWeakGains i ≤ currentUpperEighteenGains i := by
  fin_cases i <;> norm_num [currentUpperEighteenWeakGains, currentUpperEighteenGains]

theorem currentUpperEighteenRaw_le_weak :
    currentUpperEighteenRaw ≤ currentUpperEighteenWeakRaw := by
  unfold currentUpperEighteenRaw currentUpperEighteenWeakRaw
  exact sub_le_sub_left
    (Finset.sum_le_sum fun i _ => currentUpperEighteenWeakGains_le i) _

/-- Even the less refined quoted budget has more than `10^-5` left after
allocating two reserves of `1/200000`. Actual analytic errors are not paid here. -/
theorem currentUpperEighteenWeak_margin :
    currentUpperEighteenWeakRaw + 2 * currentUpperEighteenReserve + 1 / 100000
      < currentK := by
  norm_num [currentUpperEighteenWeakRaw, currentUpperEighteenPositive,
    currentUpperEighteenWeakGains, currentUpperEighteenReserve,
    currentK, Fin.sum_univ_succ]

theorem currentUpperEighteen_margin :
    currentUpperEighteenRaw + 2 * currentUpperEighteenReserve + 1 / 100000
      < currentK := by
  linarith only [currentUpperEighteenRaw_le_weak, currentUpperEighteenWeak_margin]

/-- Explicit conditional arithmetic adapter. Its component and policy-bound
hypotheses must be proved for the *same* actual density by later analytic work. -/
theorem currentUpperEighteenWeak_of_component_bounds
    (positive : Fin 4 → ℝ) (saving : Fin 18 → ℝ)
    (density rawError compilerError : ℝ)
    (hPositive : ∀ i, positive i ≤ currentUpperEighteenPositive i)
    (hSaving : ∀ i, currentUpperEighteenWeakGains i ≤ saving i)
    (hDensity : density ≤ (∑ i, positive i) - (∑ i, saving i) +
      rawError + compilerError)
    (hRawError : rawError ≤ currentUpperEighteenReserve)
    (hCompilerError : compilerError ≤ currentUpperEighteenReserve) :
    density + 1 / 100000 < currentK := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hPositive i)
  have hg := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hSaving i)
  have hMargin := currentUpperEighteenWeak_margin
  unfold currentUpperEighteenWeakRaw at hMargin
  linarith only [hp, hg, hDensity, hRawError, hCompilerError, hMargin]

end

end ImbalancedChen
