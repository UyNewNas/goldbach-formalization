import Mathlib

/-!
# Real positive transition masses in the original action geometry

SOURCE ONLY; UNCOMPILED. Earlier delivered sources are frozen.

Original formulas: `own-chen-table-insertion-chain-20261009.tex` section 3,
`global-chen-lower-completion-20261010.txt` section 3, and
`final-lower-cross-review-20261010.txt` section 3.

No switched cost is counted as a feedback edge. The W2 unchanged-prefix
weights are exactly 4/5 and 1/5, followed by three singleton and four good
pair measures, each divided by five once. Clipped globally continuous
kernels are used to make integration outside their legal domains harmless;
the raw original kernels are proved equal on every original domain.
-/

namespace ImbalancedChen.P5OriginalActionMassBound

noncomputable section

open Set MeasureTheory
open scoped BigOperators

abbrev Point := Fin 2 → ℝ

def singletonAmbient : Set ℝ := Icc (1 / 5 : ℝ) (1 / 2)
def pairAmbient : Set Point := Icc (fun _ => (1 / 5 : ℝ)) (fun _ => (1 / 2 : ℝ))
def buchstabAmbient : Set ℝ := Icc (1 : ℝ) 5

def singletonKernel (u : ℝ) : ℝ :=
  1 / (max (1 / 5 : ℝ) u * max (1 / 2 : ℝ) (1 - u))
def pairKernel (x : Point) : ℝ :=
  1 / (max (1 / 5 : ℝ) (x 0) * max (1 / 5 : ℝ) (x 1) *
    max (1 / 5 : ℝ) (1 - x 0 - x 1))
def buchstabKernel (w : ℝ) : ℝ := 1 / max (1 : ℝ) w

theorem singletonKernel_continuous : Continuous singletonKernel := by
  apply continuous_const.div
  · fun_prop
  · intro u
    positivity

theorem pairKernel_continuous : Continuous pairKernel := by
  apply continuous_const.div
  · fun_prop
  · intro x
    positivity

theorem buchstabKernel_continuous : Continuous buchstabKernel := by
  apply continuous_const.div
  · fun_prop
  · intro w
    positivity

theorem singletonKernel_nonneg (u : ℝ) : 0 ≤ singletonKernel u := by
  dsimp [singletonKernel]
  positivity

theorem pairKernel_nonneg (x : Point) : 0 ≤ pairKernel x := by
  dsimp [pairKernel]
  positivity

theorem buchstabKernel_nonneg (w : ℝ) : 0 ≤ buchstabKernel w := by
  dsimp [buchstabKernel]
  positivity

theorem singletonKernel_le_ten (u : ℝ) : singletonKernel u ≤ 10 := by
  have hd : (1 / 10 : ℝ) ≤ max (1 / 5 : ℝ) u * max (1 / 2 : ℝ) (1 - u) := by
    calc
      (1 / 10 : ℝ) = (1 / 5 : ℝ) * (1 / 2 : ℝ) := by norm_num
      _ ≤ _ := by gcongr <;> exact le_max_left _ _
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hd
  norm_num only [one_div_div, one_mul] at h
  exact h

theorem pairKernel_le_125 (x : Point) : pairKernel x ≤ 125 := by
  have hd : (1 / 125 : ℝ) ≤ max (1 / 5 : ℝ) (x 0) * max (1 / 5 : ℝ) (x 1) *
      max (1 / 5 : ℝ) (1 - x 0 - x 1) := by
    calc
      (1 / 125 : ℝ) = ((1 / 5 : ℝ) * (1 / 5 : ℝ)) * (1 / 5 : ℝ) := by norm_num
      _ ≤ _ := by gcongr <;> exact le_max_left _ _
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 125) hd
  norm_num only [one_div_div, one_mul] at h
  exact h

theorem buchstabKernel_le_one (w : ℝ) : buchstabKernel w ≤ 1 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 w)
  simpa only [one_div_one, buchstabKernel] using h

theorem singletonKernel_eq_raw {u : ℝ} (hu : u ∈ singletonAmbient) :
    singletonKernel u = 1 / (u * (1 - u)) := by
  dsimp [singletonKernel]
  rw [max_eq_right hu.1, max_eq_right (by linarith [hu.2])]

theorem pairKernel_eq_raw {x : Point} (hx : x ∈ pairAmbient)
    (hr : (1 / 5 : ℝ) ≤ 1 - x 0 - x 1) :
    pairKernel x = 1 / (x 0 * x 1 * (1 - x 0 - x 1)) := by
  dsimp [pairKernel]
  rw [max_eq_right (hx.1 0), max_eq_right (hx.1 1), max_eq_right hr]

theorem buchstabKernel_eq_raw {w : ℝ} (hw : w ∈ buchstabAmbient) :
    buchstabKernel w = 1 / w := by
  simp only [buchstabKernel, max_eq_right hw.1]

def singletonMass (D : Set ℝ) : ℝ := ∫ u in D, singletonKernel u
def pairMass (D : Set Point) : ℝ := ∫ x in D, pairKernel x
def buchstabMass (D : Set ℝ) : ℝ := ∫ w in D, buchstabKernel w

theorem singletonMass_nonneg (D : Set ℝ) : 0 ≤ singletonMass D :=
  integral_nonneg (fun u => singletonKernel_nonneg u)

theorem pairMass_nonneg (D : Set Point) : 0 ≤ pairMass D :=
  integral_nonneg (fun x => pairKernel_nonneg x)

theorem buchstabMass_nonneg (D : Set ℝ) : 0 ≤ buchstabMass D :=
  integral_nonneg (fun w => buchstabKernel_nonneg w)

theorem singletonAmbient_constant_integral :
    (∫ _u in singletonAmbient, (10 : ℝ)) = 3 := by
  rw [integral_const]
  simp [singletonAmbient, Measure.real, Real.volume_Icc, smul_eq_mul]

theorem pairAmbient_volume_real : (volume pairAmbient).toReal = 9 / 100 := by
  rw [pairAmbient, Real.volume_Icc_pi_toReal (by intro i; norm_num)]
  norm_num [Fin.prod_univ_two]

theorem pairAmbient_constant_integral :
    (∫ _x in pairAmbient, (125 : ℝ)) = 45 / 4 := by
  rw [integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, pairAmbient_volume_real]
  norm_num

theorem buchstabAmbient_constant_integral :
    (∫ _w in buchstabAmbient, (1 : ℝ)) = 4 := by
  rw [integral_const]
  simp [buchstabAmbient, Measure.real, Real.volume_Icc, smul_eq_mul]

/-- These mass bounds use actual real integrals; no saved numeric total
and no operator-norm target is an input. -/
theorem singletonMass_le_three {D : Set ℝ} (hD : D ⊆ singletonAmbient) :
    singletonMass D ≤ 3 := by
  have hi : IntegrableOn singletonKernel singletonAmbient :=
    singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_set hi
    (Filter.Eventually.of_forall singletonKernel_nonneg) (Filter.Eventually.of_forall hD)
  have hc : (∫ u in singletonAmbient, singletonKernel u) ≤
      ∫ _u in singletonAmbient, (10 : ℝ) := by
    apply setIntegral_mono_on hi
      (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc
    intro u hu
    exact singletonKernel_le_ten u
  exact hm.trans (hc.trans_eq singletonAmbient_constant_integral)

theorem pairMass_le_45_fourths {D : Set Point} (hD : D ⊆ pairAmbient) :
    pairMass D ≤ 45 / 4 := by
  have hi : IntegrableOn pairKernel pairAmbient :=
    pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_set hi
    (Filter.Eventually.of_forall pairKernel_nonneg) (Filter.Eventually.of_forall hD)
  have hc : (∫ x in pairAmbient, pairKernel x) ≤
      ∫ _x in pairAmbient, (125 : ℝ) := by
    apply setIntegral_mono_on hi
      (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc
    intro x hx
    exact pairKernel_le_125 x
  exact hm.trans (hc.trans_eq pairAmbient_constant_integral)

theorem buchstabMass_le_four {D : Set ℝ} (hD : D ⊆ buchstabAmbient) :
    buchstabMass D ≤ 4 := by
  have hi : IntegrableOn buchstabKernel buchstabAmbient :=
    buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_set hi
    (Filter.Eventually.of_forall buchstabKernel_nonneg) (Filter.Eventually.of_forall hD)
  have hc : (∫ w in buchstabAmbient, buchstabKernel w) ≤
      ∫ _w in buchstabAmbient, (1 : ℝ) := by
    apply setIntegral_mono_on hi
      (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc
    intro w hw
    exact buchstabKernel_le_one w
  exact hm.trans (hc.trans_eq buchstabAmbient_constant_integral)

theorem singletonMass_eq_original {D : Set ℝ} (hm : MeasurableSet D)
    (hD : D ⊆ singletonAmbient) :
    singletonMass D = ∫ u in D, 1 / (u * (1 - u)) := by
  apply setIntegral_congr_fun hm
  intro u hu
  exact singletonKernel_eq_raw (hD hu)

theorem pairMass_eq_original {D : Set Point} (hm : MeasurableSet D)
    (hD : D ⊆ pairAmbient) (hr : ∀ x ∈ D, (1 / 5 : ℝ) ≤ 1 - x 0 - x 1) :
    pairMass D = ∫ x in D, 1 / (x 0 * x 1 * (1 - x 0 - x 1)) := by
  apply setIntegral_congr_fun hm
  intro x hx
  exact pairKernel_eq_raw (hD hx) (hr x hx)

theorem buchstabMass_eq_original {D : Set ℝ} (hm : MeasurableSet D)
    (hD : D ⊆ buchstabAmbient) :
    buchstabMass D = ∫ w in D, 1 / w := by
  apply setIntegral_congr_fun hm
  intro w hw
  exact buchstabKernel_eq_raw (hD hw)

structure W2Parameters where
  s : ℝ
  s0 : ℝ
  phi1 : ℝ
  phi2 : ℝ
  phi3 : ℝ

def a0 (p : W2Parameters) : ℝ := 1 / p.s0
def a1 (p : W2Parameters) : ℝ := 1 / p.phi1
def a2 (p : W2Parameters) : ℝ := 1 / p.phi2
def a3 (p : W2Parameters) : ℝ := 1 / p.phi3
def b (p : W2Parameters) : ℝ := 1 / p.s

/-- Genuine original rational geometry; this is not an operator-norm premise. -/
def W2Geometry (p : W2Parameters) : Prop :=
  (1 / 5 : ℝ) ≤ a0 p ∧ a0 p ≤ a1 p ∧ a1 p ≤ a2 p ∧ a2 p ≤ a3 p ∧
  a3 p ≤ 1 / 2 ∧ b p ≤ 1 / 2 ∧ a3 p + 2 * a1 p ≤ 1 ∧
  3 * a1 p ≤ 1 ∧ a2 p + 2 * a1 p ≤ 1

/-- Original three tuples followed by all33 repaired added tuples, verbatim
from certify_finite_w2_action_bank.json:actions[*].parameters and
expanded-w2-midpoint-bank33-v1.json:actions[*].parameters. -/
def originalRepairedW2Bank : List W2Parameters :=
  [⟨11/5, 227/50, 353/100, 29/10, 61/25⟩,
   ⟨11/5, 24/5, 353/100, 29/10, 47/20⟩,
   ⟨21/10, 24/5, 353/100, 29/10, 117/50⟩,
   ⟨101/50, 9707/2000, 89/25, 14663/5000, 11667/5000⟩,
   ⟨51/25, 46871/10000, 18297/5000, 28913/10000, 11909/5000⟩,
   ⟨103/50, 24/5, 7119/2000, 2931/1000, 4679/2000⟩,
   ⟨52/25, 1863/400, 181/50, 7253/2500, 23819/10000⟩,
   ⟨21/10, 46399/10000, 18099/5000, 1451/500, 23813/10000⟩,
   ⟨21/10, 47873/10000, 89/25, 14623/5000, 23379/10000⟩,
   ⟨53/25, 46681/10000, 35999/10000, 29037/10000, 2977/1250⟩,
   ⟨107/50, 119/25, 17897/5000, 1822/625, 23317/10000⟩,
   ⟨54/25, 46397/10000, 179/50, 29109/10000, 2977/1250⟩,
   ⟨11/5, 23199/5000, 89/25, 14597/5000, 4763/2000⟩,
   ⟨11/5, 47323/10000, 17799/5000, 7297/2500, 4659/2000⟩,
   ⟨56/25, 45799/10000, 89/25, 1457/500, 2977/1250⟩,
   ⟨56/25, 2911/625, 17899/5000, 233/80, 5843/2500⟩,
   ⟨57/25, 45393/10000, 179/50, 3641/1250, 2977/1250⟩,
   ⟨23/10, 5599/1250, 179/50, 729/250, 11907/5000⟩,
   ⟨58/25, 5573/1250, 18/5, 29101/10000, 2977/1250⟩,
   ⟨58/25, 45569/10000, 18099/5000, 29057/10000, 11619/5000⟩,
   ⟨59/25, 2209/500, 18/5, 2907/1000, 2977/1250⟩,
   ⟨12/5, 42999/10000, 18/5, 29131/10000, 24077/10000⟩,
   ⟨61/25, 20797/5000, 181/50, 29193/10000, 3053/1250⟩,
   ⟨61/25, 8319/2000, 18/5, 7289/2500, 24471/10000⟩,
   ⟨62/25, 4079/1000, 179/50, 29231/10000, 12433/5000⟩,
   ⟨5/2, 203/50, 7119/2000, 5837/2000, 25063/10000⟩,
   ⟨63/25, 40587/10000, 177/50, 2921/1000, 1263/500⟩,
   ⟨64/25, 191/50, 17699/5000, 5873/2000, 25619/10000⟩,
   ⟨64/25, 20297/5000, 34999/10000, 14601/5000, 12827/5000⟩,
   ⟨13/5, 81/20, 17293/5000, 5843/2000, 1628/625⟩,
   ⟨66/25, 40501/10000, 33999/10000, 29213/10000, 13221/5000⟩,
   ⟨67/25, 179/50, 86/25, 29529/10000, 13407/5000⟩,
   ⟨67/25, 10127/2500, 84/25, 14649/5000, 26837/10000⟩,
   ⟨68/25, 81/20, 33/10, 29343/10000, 1702/625⟩,
   ⟨69/25, 81/20, 163/50, 29343/10000, 13813/5000⟩,
   ⟨14/5, 81/20, 161/50, 5883/2000, 28021/10000⟩]

theorem originalRepairedW2Bank_length : originalRepairedW2Bank.length = 36 := by
  norm_num [originalRepairedW2Bank]

theorem originalRepairedW2Bank_geometry (p : W2Parameters)
    (hp : p ∈ originalRepairedW2Bank) : W2Geometry p := by
  simp only [originalRepairedW2Bank, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [W2Geometry, a0, a1, a2, a3, b]

def W2Singleton2 (p : W2Parameters) : Set ℝ := Ioo (a0 p) (b p)
def W2Singleton3 (p : W2Parameters) : Set ℝ := Ioo (a0 p) (a2 p)
def W2Singleton4 (p : W2Parameters) : Set ℝ := Ioo (a0 p) (a3 p)

def W2Pair5 (p : W2Parameters) : Set Point :=
  {x | a0 p < x 0 ∧ x 0 < x 1 ∧ x 1 < a2 p ∧ x 1 + 2 * x 0 < 1}
def W2Pair6 (p : W2Parameters) : Set Point :=
  {x | a0 p < x 0 ∧ x 0 < a1 p ∧ a2 p < x 1 ∧ x 1 < a3 p}
def W2Pair7 (p : W2Parameters) : Set Point :=
  {x | a0 p < x 0 ∧ x 0 < x 1 ∧ x 1 < a1 p}
def W2Pair8 (p : W2Parameters) : Set Point :=
  {x | a0 p < x 0 ∧ x 0 < a1 p ∧ a1 p < x 1 ∧ x 1 < a2 p}

theorem W2Singleton2_subset {p : W2Parameters} (hp : W2Geometry p) :
    W2Singleton2 p ⊆ singletonAmbient := by
  intro u hu
  exact ⟨hp.1.trans hu.1.le, hu.2.le.trans hp.2.2.2.2.2.1⟩

theorem W2Singleton3_subset {p : W2Parameters} (hp : W2Geometry p) :
    W2Singleton3 p ⊆ singletonAmbient := by
  intro u hu
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  exact ⟨h0.trans hu.1.le, hu.2.le.trans (h23.trans h3)⟩

theorem W2Singleton4_subset {p : W2Parameters} (hp : W2Geometry p) :
    W2Singleton4 p ⊆ singletonAmbient := by
  intro u hu
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  exact ⟨h0.trans hu.1.le, hu.2.le.trans h3⟩

theorem W2Pair5_geometry {p : W2Parameters} (hp : W2Geometry p)
    {x : Point} (hx : x ∈ W2Pair5 p) :
    x ∈ pairAmbient ∧ (1 / 5 : ℝ) ≤ 1 - x 0 - x 1 := by
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  rcases hx with ⟨hu, huv, hv, hgate⟩
  have hlo : (1 / 5 : ℝ) ≤ x 0 := h0.trans hu.le
  have hhi : x 1 ≤ (1 / 2 : ℝ) := hv.le.trans (h23.trans h3)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> simp only [Pi.le_def] <;> linarith
  · intro i; fin_cases i <;> simp only [Pi.le_def] <;> linarith
  · linarith

theorem W2Pair6_geometry {p : W2Parameters} (hp : W2Geometry p)
    {x : Point} (hx : x ∈ W2Pair6 p) :
    x ∈ pairAmbient ∧ (1 / 5 : ℝ) ≤ 1 - x 0 - x 1 := by
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  rcases hx with ⟨hu, hu', hv, hv'⟩
  have hlowu : (1 / 5 : ℝ) ≤ x 0 := h0.trans hu.le
  have hlowv : (1 / 5 : ℝ) ≤ x 1 := (h0.trans (h01.trans h12)).trans hv.le
  have hhiu : x 0 ≤ (1 / 2 : ℝ) := hu'.le.trans (h12.trans (h23.trans h3))
  have hhiv : x 1 ≤ (1 / 2 : ℝ) := hv'.le.trans h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · linarith

theorem W2Pair7_geometry {p : W2Parameters} (hp : W2Geometry p)
    {x : Point} (hx : x ∈ W2Pair7 p) :
    x ∈ pairAmbient ∧ (1 / 5 : ℝ) ≤ 1 - x 0 - x 1 := by
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  rcases hx with ⟨hu, huv, hv⟩
  have hlo : (1 / 5 : ℝ) ≤ x 0 := h0.trans hu.le
  have hhi : x 1 ≤ (1 / 2 : ℝ) := hv.le.trans (h12.trans (h23.trans h3))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> simp only [Pi.le_def] <;> linarith
  · intro i; fin_cases i <;> simp only [Pi.le_def] <;> linarith
  · linarith

theorem W2Pair8_geometry {p : W2Parameters} (hp : W2Geometry p)
    {x : Point} (hx : x ∈ W2Pair8 p) :
    x ∈ pairAmbient ∧ (1 / 5 : ℝ) ≤ 1 - x 0 - x 1 := by
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  rcases hx with ⟨hu, hu', hv, hv'⟩
  have hlowu : (1 / 5 : ℝ) ≤ x 0 := h0.trans hu.le
  have hlowv : (1 / 5 : ℝ) ≤ x 1 := (h0.trans h01).trans hv.le
  have hhiu : x 0 ≤ (1 / 2 : ℝ) := hu'.le.trans (h12.trans (h23.trans h3))
  have hhiv : x 1 ≤ (1 / 2 : ℝ) := hv'.le.trans (h23.trans h3)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · linarith

/-- Original W2 positive transition mass. The bad Gamma5 part and the
positive switched Gamma9--21 costs are base terms, not feedback edges. -/
def W2FeedbackMass (p : W2Parameters) : ℝ :=
  (4 + 1 + singletonMass (W2Singleton2 p) + singletonMass (W2Singleton3 p) +
    singletonMass (W2Singleton4 p) + pairMass (W2Pair5 p) + pairMass (W2Pair6 p) +
    pairMass (W2Pair7 p) + pairMass (W2Pair8 p)) / 5

theorem W2FeedbackMass_le_59_fifths {p : W2Parameters} (hp : W2Geometry p) :
    W2FeedbackMass p ≤ 59 / 5 := by
  have hs2 := singletonMass_le_three (W2Singleton2_subset hp)
  have hs3 := singletonMass_le_three (W2Singleton3_subset hp)
  have hs4 := singletonMass_le_three (W2Singleton4_subset hp)
  have hp5 := pairMass_le_45_fourths (fun x hx => (W2Pair5_geometry hp hx).1)
  have hp6 := pairMass_le_45_fourths (fun x hx => (W2Pair6_geometry hp hx).1)
  have hp7 := pairMass_le_45_fourths (fun x hx => (W2Pair7_geometry hp hx).1)
  have hp8 := pairMass_le_45_fourths (fun x hx => (W2Pair8_geometry hp hx).1)
  dsimp [W2FeedbackMass]
  linarith only [hs2, hs3, hs4, hp5, hp6, hp7, hp8]

theorem original36W2_feedback_mass_lt_twelve (p : W2Parameters)
    (hp : p ∈ originalRepairedW2Bank) : W2FeedbackMass p < 12 := by
  have h := W2FeedbackMass_le_59_fifths (originalRepairedW2Bank_geometry p hp)
  linarith

theorem W2Pair5_measurable (p : W2Parameters) : MeasurableSet (W2Pair5 p) := by
  have h1 : IsOpen {x : Point | a0 p < x 0} := isOpen_lt continuous_const (continuous_apply 0)
  have h2 : IsOpen {x : Point | x 0 < x 1} := isOpen_lt (continuous_apply 0) (continuous_apply 1)
  have h3 : IsOpen {x : Point | x 1 < a2 p} := isOpen_lt (continuous_apply 1) continuous_const
  have h4 : IsOpen {x : Point | x 1 + 2 * x 0 < 1} := isOpen_lt (by fun_prop) continuous_const
  exact (h1.inter (h2.inter (h3.inter h4))).measurableSet

theorem W2Pair6_measurable (p : W2Parameters) : MeasurableSet (W2Pair6 p) := by
  have h1 : IsOpen {x : Point | a0 p < x 0} := isOpen_lt continuous_const (continuous_apply 0)
  have h2 : IsOpen {x : Point | x 0 < a1 p} := isOpen_lt (continuous_apply 0) continuous_const
  have h3 : IsOpen {x : Point | a2 p < x 1} := isOpen_lt continuous_const (continuous_apply 1)
  have h4 : IsOpen {x : Point | x 1 < a3 p} := isOpen_lt (continuous_apply 1) continuous_const
  exact (h1.inter (h2.inter (h3.inter h4))).measurableSet

theorem W2Pair7_measurable (p : W2Parameters) : MeasurableSet (W2Pair7 p) := by
  have h1 : IsOpen {x : Point | a0 p < x 0} := isOpen_lt continuous_const (continuous_apply 0)
  have h2 : IsOpen {x : Point | x 0 < x 1} := isOpen_lt (continuous_apply 0) (continuous_apply 1)
  have h3 : IsOpen {x : Point | x 1 < a1 p} := isOpen_lt (continuous_apply 1) continuous_const
  exact (h1.inter (h2.inter h3)).measurableSet

theorem W2Pair8_measurable (p : W2Parameters) : MeasurableSet (W2Pair8 p) := by
  have h1 : IsOpen {x : Point | a0 p < x 0} := isOpen_lt continuous_const (continuous_apply 0)
  have h2 : IsOpen {x : Point | x 0 < a1 p} := isOpen_lt (continuous_apply 0) continuous_const
  have h3 : IsOpen {x : Point | a1 p < x 1} := isOpen_lt continuous_const (continuous_apply 1)
  have h4 : IsOpen {x : Point | x 1 < a2 p} := isOpen_lt (continuous_apply 1) continuous_const
  exact (h1.inter (h2.inter (h3.inter h4))).measurableSet

/-- Literal original kernel dictionary for all seven W2 feedback domains. -/
theorem W2FeedbackMass_eq_original {p : W2Parameters} (hp : W2Geometry p) :
    W2FeedbackMass p =
      (4 + 1 + (∫ u in W2Singleton2 p, 1 / (u * (1 - u))) +
        (∫ u in W2Singleton3 p, 1 / (u * (1 - u))) +
        (∫ u in W2Singleton4 p, 1 / (u * (1 - u))) +
        (∫ x in W2Pair5 p, 1 / (x 0 * x 1 * (1 - x 0 - x 1))) +
        (∫ x in W2Pair6 p, 1 / (x 0 * x 1 * (1 - x 0 - x 1))) +
        (∫ x in W2Pair7 p, 1 / (x 0 * x 1 * (1 - x 0 - x 1))) +
        (∫ x in W2Pair8 p, 1 / (x 0 * x 1 * (1 - x 0 - x 1)))) / 5 := by
  dsimp [W2FeedbackMass]
  rw [singletonMass_eq_original measurableSet_Ioo (W2Singleton2_subset hp),
    singletonMass_eq_original measurableSet_Ioo (W2Singleton3_subset hp),
    singletonMass_eq_original measurableSet_Ioo (W2Singleton4_subset hp),
    pairMass_eq_original (W2Pair5_measurable p)
      (fun x hx => (W2Pair5_geometry hp hx).1) (fun x hx => (W2Pair5_geometry hp hx).2),
    pairMass_eq_original (W2Pair6_measurable p)
      (fun x hx => (W2Pair6_geometry hp hx).1) (fun x hx => (W2Pair6_geometry hp hx).2),
    pairMass_eq_original (W2Pair7_measurable p)
      (fun x hx => (W2Pair7_geometry hp hx).1) (fun x hx => (W2Pair7_geometry hp hx).2),
    pairMass_eq_original (W2Pair8_measurable p)
      (fun x hx => (W2Pair8_geometry hp hx).1) (fun x hx => (W2Pair8_geometry hp hx).2)]

/-- Actual child arguments, with the original4/5 and1/5 unchanged-prefix
atoms. The excluded bad5 and switched9--21 costs do not occur here. -/
def W2FeedbackValue (p : W2Parameters) (H h : ℝ → ℝ) : ℝ :=
  (4 * H p.s0 + H p.phi1 +
    (∫ u in W2Singleton2 p, singletonKernel u * h (p.s0 * (1 - u))) +
    (∫ u in W2Singleton3 p, singletonKernel u * h (p.s0 * (1 - u))) +
    (∫ u in W2Singleton4 p, singletonKernel u * h (p.s0 * (1 - u))) +
    (∫ x in W2Pair5 p, pairKernel x * H (p.s0 * (1 - x 0 - x 1))) +
    (∫ x in W2Pair6 p, pairKernel x * H (p.s0 * (1 - x 0 - x 1))) +
    (∫ x in W2Pair7 p, pairKernel x * H ((1 - x 0 - x 1) / x 0)) +
    (∫ x in W2Pair8 p, pairKernel x * H ((1 - x 0 - x 1) / x 0))) / 5

theorem W2FeedbackValue_one (p : W2Parameters) :
    W2FeedbackValue p (fun _ => 1) (fun _ => 1) = W2FeedbackMass p := by
  simp only [W2FeedbackValue, W2FeedbackMass, singletonMass, pairMass, mul_one]

def W1Target (i : Fin 7) : ℝ := 12 / 5 + (i.val : ℝ) / 10
def W1Anchor (j : Fin 10) : ℝ := 16 / 5 + (j.val : ℝ) / 5
def W1Domain (i : Fin 7) (j : Fin 10) : Set ℝ := Ioo (1 / W1Anchor j) (1 / W1Target i)
def W1FeedbackMass (i : Fin 7) (j : Fin 10) : ℝ := 1 + singletonMass (W1Domain i j) / 2
def W1FeedbackValue (i : Fin 7) (j : Fin 10) (H h : ℝ → ℝ) : ℝ :=
  H (W1Anchor j) + (∫ u in W1Domain i j,
    singletonKernel u * h (W1Anchor j * (1 - u))) / 2

theorem W1Domain_subset (i : Fin 7) (j : Fin 10) : W1Domain i j ⊆ singletonAmbient := by
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hj9 : (j.val : ℝ) ≤ 9 := by exact_mod_cast (show j.val ≤ 9 by omega)
  have hs : (2 : ℝ) ≤ W1Target i := by dsimp [W1Target]; linarith
  have ha0 : 0 < W1Anchor j := by dsimp [W1Anchor]; linarith
  have ha5 : W1Anchor j ≤ (5 : ℝ) := by dsimp [W1Anchor]; linarith
  have hlo : (1 / 5 : ℝ) ≤ 1 / W1Anchor j := one_div_le_one_div_of_le ha0 ha5
  have hhi : 1 / W1Target i ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hs
  intro u hu
  exact ⟨hlo.trans hu.1.le, hu.2.le.trans hhi⟩

theorem original70W1_feedback_mass_le_five_halves (i : Fin 7) (j : Fin 10) :
    W1FeedbackMass i j ≤ 5 / 2 := by
  have h := singletonMass_le_three (W1Domain_subset i j)
  dsimp [W1FeedbackMass]
  linarith

theorem original70W1_feedback_mass_lt_twelve (i : Fin 7) (j : Fin 10) :
    W1FeedbackMass i j < 12 := by
  linarith [original70W1_feedback_mass_le_five_halves i j]

theorem W1FeedbackMass_eq_original (i : Fin 7) (j : Fin 10) :
    W1FeedbackMass i j = 1 +
      (∫ u in W1Domain i j, 1 / (u * (1 - u))) / 2 := by
  rw [W1FeedbackMass, singletonMass_eq_original measurableSet_Ioo (W1Domain_subset i j)]

theorem W1FeedbackValue_one (i : Fin 7) (j : Fin 10) :
    W1FeedbackValue i j (fun _ => 1) (fun _ => 1) = W1FeedbackMass i j := by
  simp only [W1FeedbackValue, W1FeedbackMass, singletonMass, mul_one]

theorem originalW1_parameter_count : Fintype.card (Fin 7 × Fin 10) = 70 := by norm_num

def buchstabUpperDomain (s : ℝ) : Set ℝ := Icc (max 2 (s - 1)) 5
def buchstabLowerDomain (s : ℝ) : Set ℝ := Icc (s - 1) 5

theorem buchstabUpperDomain_subset (s : ℝ) : buchstabUpperDomain s ⊆ buchstabAmbient := by
  intro w hw
  refine ⟨?_, hw.2⟩
  have h2 : (2 : ℝ) ≤ max 2 (s - 1) := le_max_left _ _
  linarith [hw.1]

theorem buchstabLowerDomain_subset {s : ℝ} (hs : 2 ≤ s) :
    buchstabLowerDomain s ⊆ buchstabAmbient := by
  intro w hw
  exact ⟨by linarith [hw.1], hw.2⟩

theorem originalBuchstab_upper_mass_lt_twelve (s : ℝ) :
    buchstabMass (buchstabUpperDomain s) < 12 := by
  linarith [buchstabMass_le_four (buchstabUpperDomain_subset s)]

theorem originalBuchstab_lower_mass_lt_twelve {s : ℝ} (hs : 2 ≤ s) :
    buchstabMass (buchstabLowerDomain s) < 12 := by
  linarith [buchstabMass_le_four (buchstabLowerDomain_subset hs)]

theorem originalBuchstab_upper_raw (s : ℝ) :
    buchstabMass (buchstabUpperDomain s) = ∫ w in buchstabUpperDomain s, 1 / w := by
  exact buchstabMass_eq_original measurableSet_Icc (buchstabUpperDomain_subset s)

theorem originalBuchstab_lower_raw {s : ℝ} (hs : 2 ≤ s) :
    buchstabMass (buchstabLowerDomain s) = ∫ w in buchstabLowerDomain s, 1 / w := by
  exact buchstabMass_eq_original measurableSet_Icc (buchstabLowerDomain_subset hs)

def originalW2At (j : Fin 36) : W2Parameters :=
  originalRepairedW2Bank[j.val]'(by simpa only [originalRepairedW2Bank_length] using j.isLt)

theorem originalW2At_mem (j : Fin 36) : originalW2At j ∈ originalRepairedW2Bank := by
  exact List.getElem_mem (by simpa only [originalRepairedW2Bank_length] using j.isLt)

abbrev Original106Action := (Fin 7 × Fin 10) ⊕ Fin 36

def original106Mass : Original106Action → ℝ
  | .inl (i, j) => W1FeedbackMass i j
  | .inr j => W2FeedbackMass (originalW2At j)

theorem original106Action_count : Fintype.card Original106Action = 106 := by
  norm_num [Original106Action]

theorem original106Mass_lt_twelve (a : Original106Action) : original106Mass a < 12 := by
  rcases a with ⟨i, j⟩ | j
  · exact original70W1_feedback_mass_lt_twelve i j
  · exact original36W2_feedback_mass_lt_twelve _ (originalW2At_mem j)

theorem original106Mass_nonneg (a : Original106Action) : 0 ≤ original106Mass a := by
  rcases a with ⟨i, j⟩ | j
  · have h := singletonMass_nonneg (W1Domain i j)
    dsimp [original106Mass, W1FeedbackMass]
    linarith
  · have hs2 := singletonMass_nonneg (W2Singleton2 (originalW2At j))
    have hs3 := singletonMass_nonneg (W2Singleton3 (originalW2At j))
    have hs4 := singletonMass_nonneg (W2Singleton4 (originalW2At j))
    have hp5 := pairMass_nonneg (W2Pair5 (originalW2At j))
    have hp6 := pairMass_nonneg (W2Pair6 (originalW2At j))
    have hp7 := pairMass_nonneg (W2Pair7 (originalW2At j))
    have hp8 := pairMass_nonneg (W2Pair8 (originalW2At j))
    dsimp [original106Mass, W2FeedbackMass]
    linarith

theorem original106Mass_le_twelve (a : Original106Action) : original106Mass a ≤ 12 :=
  (original106Mass_lt_twelve a).le

/-- Individual lower-enclosed atom weights on a genuine disjoint finite
subdivision inherit the real singleton mass bound. The hypotheses are
literal cell geometry and local integral comparisons, not an operator norm. -/
theorem singleton_finite_atom_sum_le_three {ι : Type*}
    (S : Finset ι) (cells : ι → Set ℝ) (weight : ι → ℝ)
    (hm : ∀ i ∈ S, MeasurableSet (cells i))
    (hd : Set.Pairwise (↑S) (fun i j => Disjoint (cells i) (cells j)))
    (hsub : ∀ i ∈ S, cells i ⊆ singletonAmbient)
    (hw : ∀ i ∈ S, weight i ≤ singletonMass (cells i)) :
    (∑ i ∈ S, weight i) ≤ 3 := by
  have hi : IntegrableOn singletonKernel singletonAmbient :=
    singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hu : (⋃ i ∈ S, cells i) ⊆ singletonAmbient := by
    intro u hu
    obtain ⟨i, hu⟩ := mem_iUnion.mp hu
    obtain ⟨hiS, hu⟩ := mem_iUnion.mp hu
    exact hsub i hiS hu
  calc
    (∑ i ∈ S, weight i) ≤ ∑ i ∈ S, singletonMass (cells i) :=
      Finset.sum_le_sum (fun i hiS => hw i hiS)
    _ = singletonMass (⋃ i ∈ S, cells i) := by
      exact (integral_biUnion_finset S hm hd
        (fun i hiS => hi.mono_set (hsub i hiS))).symm
    _ ≤ 3 := singletonMass_le_three hu

theorem pair_finite_atom_sum_le_45_fourths {ι : Type*}
    (S : Finset ι) (cells : ι → Set Point) (weight : ι → ℝ)
    (hm : ∀ i ∈ S, MeasurableSet (cells i))
    (hd : Set.Pairwise (↑S) (fun i j => Disjoint (cells i) (cells j)))
    (hsub : ∀ i ∈ S, cells i ⊆ pairAmbient)
    (hw : ∀ i ∈ S, weight i ≤ pairMass (cells i)) :
    (∑ i ∈ S, weight i) ≤ 45 / 4 := by
  have hi : IntegrableOn pairKernel pairAmbient :=
    pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hu : (⋃ i ∈ S, cells i) ⊆ pairAmbient := by
    intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hiS, hx⟩ := mem_iUnion.mp hx
    exact hsub i hiS hx
  calc
    (∑ i ∈ S, weight i) ≤ ∑ i ∈ S, pairMass (cells i) :=
      Finset.sum_le_sum (fun i hiS => hw i hiS)
    _ = pairMass (⋃ i ∈ S, cells i) := by
      exact (integral_biUnion_finset S hm hd
        (fun i hiS => hi.mono_set (hsub i hiS))).symm
    _ ≤ 45 / 4 := pairMass_le_45_fourths hu

def W2SingletonDomain (p : W2Parameters) : Fin 3 → Set ℝ :=
  ![W2Singleton2 p, W2Singleton3 p, W2Singleton4 p]
def W2PairDomain (p : W2Parameters) : Fin 4 → Set Point :=
  ![W2Pair5 p, W2Pair6 p, W2Pair7 p, W2Pair8 p]

theorem W2SingletonDomain_subset {p : W2Parameters} (hp : W2Geometry p) (j : Fin 3) :
    W2SingletonDomain p j ⊆ singletonAmbient := by
  fin_cases j
  · exact W2Singleton2_subset hp
  · exact W2Singleton3_subset hp
  · exact W2Singleton4_subset hp

theorem W2PairDomain_subset {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4) :
    W2PairDomain p j ⊆ pairAmbient := by
  fin_cases j
  · exact fun x hx => (W2Pair5_geometry hp hx).1
  · exact fun x hx => (W2Pair6_geometry hp hx).1
  · exact fun x hx => (W2Pair7_geometry hp hx).1
  · exact fun x hx => (W2Pair8_geometry hp hx).1

/-- The concrete finite-atom mass receiver for all original repaired W2
parameters. Any genuine inner subdivision and any downward enclosure of
its individual integrals fits12, with the fixed4/5+1/5 atoms included once. -/
theorem originalW2_finite_atom_row_mass_lt_twelve
    {ι κ : Type*} (p : W2Parameters) (hp : p ∈ originalRepairedW2Bank)
    (S : Fin 3 → Finset ι) (T : Fin 4 → Finset κ)
    (singletonCells : Fin 3 → ι → Set ℝ) (pairCells : Fin 4 → κ → Set Point)
    (singletonWeight : Fin 3 → ι → ℝ) (pairWeight : Fin 4 → κ → ℝ)
    (hsm : ∀ j i, i ∈ S j → MeasurableSet (singletonCells j i))
    (hpm : ∀ j i, i ∈ T j → MeasurableSet (pairCells j i))
    (hsd : ∀ j, Set.Pairwise (↑(S j)) (fun i k => Disjoint (singletonCells j i) (singletonCells j k)))
    (hpd : ∀ j, Set.Pairwise (↑(T j)) (fun i k => Disjoint (pairCells j i) (pairCells j k)))
    (hssub : ∀ j i, i ∈ S j → singletonCells j i ⊆ W2SingletonDomain p j)
    (hpsub : ∀ j i, i ∈ T j → pairCells j i ⊆ W2PairDomain p j)
    (hsw : ∀ j i, i ∈ S j → singletonWeight j i ≤ singletonMass (singletonCells j i))
    (hpw : ∀ j i, i ∈ T j → pairWeight j i ≤ pairMass (pairCells j i)) :
    (4 + 1 + (∑ j : Fin 3, ∑ i ∈ S j, singletonWeight j i) +
      (∑ j : Fin 4, ∑ i ∈ T j, pairWeight j i)) / 5 < 12 := by
  have hg := originalRepairedW2Bank_geometry p hp
  have hs : ∀ j, (∑ i ∈ S j, singletonWeight j i) ≤ 3 := by
    intro j
    exact singleton_finite_atom_sum_le_three (S j) (singletonCells j) (singletonWeight j)
      (hsm j) (hsd j)
      (fun i hi => (hssub j i hi).trans (W2SingletonDomain_subset hg j)) (hsw j)
  have ht : ∀ j, (∑ i ∈ T j, pairWeight j i) ≤ 45 / 4 := by
    intro j
    exact pair_finite_atom_sum_le_45_fourths (T j) (pairCells j) (pairWeight j)
      (hpm j) (hpd j)
      (fun i hi => (hpsub j i hi).trans (W2PairDomain_subset hg j)) (hpw j)
  have hsSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
  have htSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => ht j)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsSum htSum
  linarith only [hsSum, htSum]

theorem originalW1_finite_atom_row_mass_lt_twelve {ι : Type*}
    (i : Fin 7) (j : Fin 10) (S : Finset ι) (cells : ι → Set ℝ) (weight : ι → ℝ)
    (hm : ∀ a ∈ S, MeasurableSet (cells a))
    (hd : Set.Pairwise (↑S) (fun a b => Disjoint (cells a) (cells b)))
    (hsub : ∀ a ∈ S, cells a ⊆ W1Domain i j)
    (hw : ∀ a ∈ S, weight a ≤ singletonMass (cells a)) :
    1 + (∑ a ∈ S, weight a) / 2 < 12 := by
  have h := singleton_finite_atom_sum_le_three S cells weight hm hd
    (fun a ha => (hsub a ha).trans (W1Domain_subset i j)) hw
  linarith

def buchstabUpperFeedback (s : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ w in buchstabUpperDomain s, buchstabKernel w * h w
def buchstabLowerFeedback (s : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ w in buchstabLowerDomain s, buchstabKernel w * H w

theorem buchstabUpperFeedback_one (s : ℝ) :
    buchstabUpperFeedback s (fun _ => 1) = buchstabMass (buchstabUpperDomain s) := by
  simp only [buchstabUpperFeedback, buchstabMass, mul_one]

theorem buchstabLowerFeedback_one (s : ℝ) :
    buchstabLowerFeedback s (fun _ => 1) = buchstabMass (buchstabLowerDomain s) := by
  simp only [buchstabLowerFeedback, buchstabMass, mul_one]

theorem buchstab_finite_atom_sum_le_four {ι : Type*}
    (S : Finset ι) (cells : ι → Set ℝ) (weight : ι → ℝ)
    (hm : ∀ i ∈ S, MeasurableSet (cells i))
    (hd : Set.Pairwise (↑S) (fun i j => Disjoint (cells i) (cells j)))
    (hsub : ∀ i ∈ S, cells i ⊆ buchstabAmbient)
    (hw : ∀ i ∈ S, weight i ≤ buchstabMass (cells i)) :
    (∑ i ∈ S, weight i) ≤ 4 := by
  have hi : IntegrableOn buchstabKernel buchstabAmbient :=
    buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hu : (⋃ i ∈ S, cells i) ⊆ buchstabAmbient := by
    intro u hu
    obtain ⟨i, hu⟩ := mem_iUnion.mp hu
    obtain ⟨hiS, hu⟩ := mem_iUnion.mp hu
    exact hsub i hiS hu
  calc
    (∑ i ∈ S, weight i) ≤ ∑ i ∈ S, buchstabMass (cells i) :=
      Finset.sum_le_sum (fun i hiS => hw i hiS)
    _ = buchstabMass (⋃ i ∈ S, cells i) := by
      exact (integral_biUnion_finset S hm hd
        (fun i hiS => hi.mono_set (hsub i hiS))).symm
    _ ≤ 4 := buchstabMass_le_four hu

end
end ImbalancedChen.P5OriginalActionMassBound
