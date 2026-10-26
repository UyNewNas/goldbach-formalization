import ImbalancedChen.ActualUpperDensityAssembly
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
Source-only candidate: original current constants and perturbation assembly.

The rational constants below are the adopted-evidence-catalog endpoints. The
proofs check their finite arithmetic and transport separately supplied component
errors. They do not prove any of the missing original integral certificates,
nor identify a historical policy with this signed component expression.
-/

namespace ImbalancedChen.P2OriginalCertificateBudget

open scoped BigOperators

def baseUpper : Fin 4 → ℚ := ![
  2000 / 299,
  7179974843999672947 / 9444732965739290427392,
  144590669409566793572719 / 1208925819614629174706176,
  319683857488126290909150567 / 2596148429267413814265248164610048]

def savingLower : Fin 22 → ℚ := ![
  10601625247768616959055 / 302231454903657293676544,
  3037921066812732539869 / 302231454903657293676544,
  1648717268323516459667 / 1208925819614629174706176,
  145496122603609407505 / 151115727451828646838272,
  640339 / 15210735000,
  3097012678584315027795429 / 79228162514264337593543950336,
  1208544915921356327515701 / 79228162514264337593543950336,
  148834609033428677786865 / 79228162514264337593543950336,
  306737545112876482463163 / 79228162514264337593543950336,
  187277743940187526723019 / 79228162514264337593543950336,
  670429887277013841791829 / 79228162514264337593543950336,
  198410119216276585672773 / 39614081257132168796771975168,
  5023185001132087792027 / 9903520314283042199192993792,
  581521529176619227721 / 4951760157141521099596496896,
  74558208451675327462975 / 79228162514264337593543950336,
  1222997719565324892497827 / 79228162514264337593543950336,
  467454156274267811817033 / 79228162514264337593543950336,
  1033407531585213315823239 / 79228162514264337593543950336,
  283388722705335806564439 / 79228162514264337593543950336,
  14750615007945677662815 / 39614081257132168796771975168,
  77410436074156865471 / 79228162514264337593543950336,
  481322793305152847935 / 79228162514264337593543950336]

def rawUpper : ℚ :=
  9979702576710911234850619807816847864907359959 /
    1475913550962201227946780619099353215139840000

def upperReserve : ℚ :=
  145007961227048312210593427530128000784681 /
    11807308407697609823574244952794825721118720000

def upperSlack : ℚ :=
  71229286727542131248758574547050908572431 /
    737956775481100613973390309549676607569920000000

/-- Every adopted saving occurs once, including only the two seed increments. -/
theorem endpoint_sum : (∑ i, baseUpper i) - (∑ j, savingLower j) = rawUpper := by
  norm_num [baseUpper, savingLower, rawUpper, Fin.sum_univ_succ]

theorem endpoint_slack :
    currentK - ((rawUpper : ℝ) + 2 * upperReserve) = (upperSlack : ℝ) := by
  norm_num [currentK, rawUpper, upperReserve, upperSlack]

theorem upperSlack_pos : (0 : ℝ) < (upperSlack : ℝ) := by
  norm_num [upperSlack]

/-- Actual signed contributions need individually directed errors. No positivity
of a saving or of the component errors is needed by the algebra. -/
theorem component_error_bound
    (base : Fin 4 → ℝ) (saving : Fin 22 → ℝ)
    (baseError : Fin 4 → ℝ) (savingError : Fin 22 → ℝ)
    (hb : ∀ i, base i ≤ (baseUpper i : ℝ) + baseError i)
    (hs : ∀ j, (savingLower j : ℝ) - savingError j ≤ saving j) :
    (∑ i, base i) - (∑ j, saving j) ≤
      (rawUpper : ℝ) + (∑ i, baseError i) + (∑ j, savingError j) := by
  have hbase := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have hsaving := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
  have hend : (∑ i, (baseUpper i : ℝ)) - (∑ j, (savingLower j : ℝ)) =
      (rawUpper : ℝ) := by exact_mod_cast endpoint_sum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hbase hsaving
  linarith

/-- The literal original slack pays directed local errors after both original
reserves are charged. This theorem does not supply those local errors. -/
theorem component_error_and_both_reserves_lt_currentK
    (base : Fin 4 → ℝ) (saving : Fin 22 → ℝ)
    (baseError : Fin 4 → ℝ) (savingError : Fin 22 → ℝ)
    (hb : ∀ i, base i ≤ (baseUpper i : ℝ) + baseError i)
    (hs : ∀ j, (savingLower j : ℝ) - savingError j ≤ saving j)
    (herr : (∑ i, baseError i) + (∑ j, savingError j) < (upperSlack : ℝ)) :
    (∑ i, base i) - (∑ j, saving j) + 2 * (upperReserve : ℝ) < currentK := by
  have h := component_error_bound base saving baseError savingError hb hs
  have he := endpoint_slack
  linarith

/-- A uniform local tolerance for the original four costs and twenty-two
savings. It allocates half the existing slack and changes no selected constant. -/
def localTolerance : ℚ := upperSlack / 52

theorem twenty_six_local_errors_lt_slack :
    (∑ _i : Fin 4, (localTolerance : ℝ)) +
      (∑ _j : Fin 22, (localTolerance : ℝ)) < (upperSlack : ℝ) := by
  have hp := upperSlack_pos
  have he : (localTolerance : ℝ) = (upperSlack : ℝ) / 52 := by
    norm_num [localTolerance]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [he]
  linarith

theorem original_components_with_uniform_tolerance_lt_currentK
    (base : Fin 4 → ℝ) (saving : Fin 22 → ℝ)
    (hb : ∀ i, base i ≤ (baseUpper i : ℝ) + (localTolerance : ℝ))
    (hs : ∀ j, (savingLower j : ℝ) - (localTolerance : ℝ) ≤ saving j) :
    (∑ i, base i) - (∑ j, saving j) + 2 * (upperReserve : ℝ) < currentK := by
  exact component_error_and_both_reserves_lt_currentK base saving
    (fun _ => (localTolerance : ℝ)) (fun _ => (localTolerance : ℝ))
    hb hs twenty_six_local_errors_lt_slack

/-- Concrete receiver for original local certificates and the literal compiler
coefficient error. The attached density pays one reserve; the compiler pays the
other. Both coefficients in the conclusion are the ones in the error premise. -/
theorem compiled_density_of_component_errors
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M : ℝ)
    (base : Fin 4 → ℝ) (saving : Fin 22 → ℝ)
    (baseError : Fin 4 → ℝ) (savingError : Fin 22 → ℝ)
    (hb : ∀ i, base i ≤ (baseUpper i : ℝ) + baseError i)
    (hs : ∀ j, (savingLower j : ℝ) - savingError j ≤ saving j)
    (herr : (∑ i, baseError i) + (∑ j, savingError j) < (upperSlack : ℝ))
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      ((∑ i, base i) - (∑ j, saving j) + (upperReserve : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      (upperReserve : ℝ) * (singularSeries N / Real.log (N : ℝ))) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK := by
  apply compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    hN hsmall hrough compiled raw betaMinus betaPlus M
    ((∑ i, base i) - (∑ j, saving j) + (upperReserve : ℝ))
    (upperReserve : ℝ) hminus hplus hraw hcompiler
  have h := component_error_and_both_reserves_lt_currentK
    base saving baseError savingError hb hs herr
  linarith

def lowerRaw : ℚ :=
  1345983686820460038728276256001756964104092721 /
    685738127494661151198444592354557952000000000

def lowerReserve : ℚ :=
  2913305608548241964824517919947906098888971 /
    5485905019957289209587556738836463616000000000

def lowerSlack : ℚ :=
  13457260926863633771775678584711245753 /
    2742952509978644604793778369418231808000000000

theorem lower_endpoint_slack :
    (lowerRaw : ℝ) - 2 * lowerReserve - currentC = (lowerSlack : ℝ) := by
  norm_num [lowerRaw, lowerReserve, currentC, lowerSlack]

theorem lowerSlack_pos : (0 : ℝ) < (lowerSlack : ℝ) := by
  norm_num [lowerSlack]

/-- A true lower estimator can lose any amount strictly below the selected
slack and still pay both original lower reserves. Its semantic lower-count
theorem remains a separate required input. -/
theorem lower_error_and_both_reserves_gt_currentC
    {actual loss : ℝ}
    (hactual : (lowerRaw : ℝ) - loss ≤ actual)
    (hloss : loss < (lowerSlack : ℝ)) :
    currentC < actual - 2 * (lowerReserve : ℝ) := by
  have he := lower_endpoint_slack
  linarith

end ImbalancedChen.P2OriginalCertificateBudget
