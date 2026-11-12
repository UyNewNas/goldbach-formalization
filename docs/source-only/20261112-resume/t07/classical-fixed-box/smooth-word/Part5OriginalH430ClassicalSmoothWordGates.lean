import ImbalancedChen.Part5OriginalH430ClassicalAllBoundaryCredit
import ImbalancedChen.P4BSmoothGateUpperStep

/-! One fixed finite program per original colour word and tail length.
The first coordinate is the external prefix p, the next s are the marked q
in their original order, and the last r are the canonical nondecreasing tail. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothWordGates
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open Part5UpperTables.OriginalU34 (clampStart)
open P4B
open scoped Classical Topology BigOperators ContDiff

abbrev Point (s r : ℕ) := ℝ × (Fin s → ℝ) × (Fin r → ℝ)

inductive Gate (s r : ℕ) where
  | outerLo | outerHi
  | primeLo (i : Fin s) | primeHi (i : Fin s)
  | colourLo (i : Fin s) (j : Fin 3) | colourHi (i : Fin s) (j : Fin 3)
  | primeOrder (i j : Fin s) | tailOrder (i j : Fin r)
  | penultimate (i : Fin s) (j : Fin r)
  deriving DecidableEq, Fintype

def colourPower : Fin 3 → ℝ := ![a1,a2,a3]

def active {s r : ℕ} (C : Fin s → ℕ) : Gate s r → Prop
  | .colourLo i j => j.val<C i
  | .colourHi i j => j.val=C i
  | .primeOrder i j => i<j
  | .tailOrder i j => i<j
  | .penultimate i _ => i.val=s-2
  | _ => True

def program {s : ℕ} (r : ℕ) (C : Fin s → ℕ) : Finset (Gate s r) :=
  univ.filter (active C)

def openFace {s r : ℕ} : Gate s r → Bool
  | .outerHi | .primeHi _ | .colourHi _ _ | .primeOrder _ _ => true
  | _ => false

def powerMargin (ν v x y : ℝ) : ℝ := v*x+y-v*ν

def margin {s r : ℕ} (ν : ℝ) (t : Point s r) : Gate s r → ℝ
  | .outerLo => t.1-clampStart
  | .outerHi => 1/3-t.1
  | .primeLo i => powerMargin ν a0 t.1 (t.2.1 i)
  | .primeHi i => -(powerMargin ν b t.1 (t.2.1 i))
  | .colourLo i j => powerMargin ν (colourPower j) t.1 (t.2.1 i)
  | .colourHi i j => -(powerMargin ν (colourPower j) t.1 (t.2.1 i))
  | .primeOrder i j => t.2.1 j-t.2.1 i
  | .tailOrder i j => t.2.2 j-t.2.2 i
  | .penultimate i j => t.2.2 j-t.2.1 i

def passed {s r : ℕ} (ν : ℝ) (t : Point s r) (g : Gate s r) : Prop :=
  if openFace g then 0<margin ν t g else 0≤margin ν t g

def accepted {s r : ℕ} (C : Fin s → ℕ) (ν : ℝ) (t : Point s r) : Prop :=
  ∀ g∈program r C,passed ν t g

def weight {s r : ℕ} (C : Fin s → ℕ) (ν δ : ℝ) (t : Point s r) : ℝ :=
  ∏ g∈program r C,smoothGateUpperStep δ (margin ν t g)

theorem mem_program {s r : ℕ} {C : Fin s → ℕ} {g : Gate s r} :
    g∈program r C ↔ active C g := by simp [program]

theorem weight_bounds {s r : ℕ} (C : Fin s → ℕ) (ν δ : ℝ) (t : Point s r) :
    0≤weight C ν δ t ∧ weight C ν δ t≤1 :=
  ⟨prod_nonneg (fun _ _ => smoothGateUpperStep_nonneg _ _),
    prod_le_one (fun _ _ => smoothGateUpperStep_nonneg _ _) (fun _ _ => smoothGateUpperStep_le_one _ _)⟩

theorem weight_one {s r : ℕ} {C : Fin s → ℕ} {ν δ : ℝ} (hd : 0<δ) {t : Point s r}
    (ht : accepted C ν t) : weight C ν δ t=1 := by
  apply prod_eq_one
  intro g hg
  have hh := ht g hg
  have hmargin : 0≤margin ν t g := by
    unfold passed at hh
    split at hh
    · exact hh.le
    · exact hh
  exact smoothGateUpperStep_eq_one hd hmargin

theorem failed_positive_strip {s r : ℕ} {C : Fin s → ℕ} {ν δ : ℝ} (hd : 0<δ) {t : Point s r}
    (ht : ¬accepted C ν t) (hw : weight C ν δ t≠0) :
    ∃ g∈program r C,|margin ν t g|≤δ := by
  unfold accepted at ht
  push_neg at ht
  obtain ⟨g,hg,hfail⟩ := ht
  have hNZ : smoothGateUpperStep δ (margin ν t g)≠0 := (Finset.prod_ne_zero_iff.mp hw) g hg
  have hlo := smoothGateUpperStep_nonzero_support hd hNZ
  have hhi : margin ν t g≤0 := by
    unfold passed at hfail
    split at hfail
    · exact le_of_not_gt hfail
    · exact (lt_of_not_ge hfail).le
  exact ⟨g,hg,abs_le.mpr ⟨hlo.le,hhi.trans hd.le⟩⟩

theorem contDiff_margin {s r : ℕ} (ν : ℝ) (g : Gate s r) {d : ℕ∞} :
    ContDiff ℝ d (fun t : Point s r => margin ν t g) := by
  cases g <;> simp only [margin,powerMargin] <;> fun_prop

theorem contDiff_weight {s r : ℕ} (C : Fin s → ℕ) (ν δ : ℝ) {d : ℕ∞} :
    ContDiff ℝ d (weight (r:=r) C ν δ) := by
  unfold weight
  apply contDiff_prod
  intro g _
  exact (contDiff_smoothGateUpperStep δ).comp (contDiff_margin ν g)

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothWordGates

