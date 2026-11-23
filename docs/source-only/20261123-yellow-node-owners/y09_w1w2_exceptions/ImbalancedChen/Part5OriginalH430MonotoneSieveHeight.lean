import ImbalancedChen.Part5OriginalH430SelectedFreshWindows
import ImbalancedChen.Part5OriginalH430RequestedOriginalRowFreeze

/-! Physical sieve heights along the actual U3 and U4 history. The comparison
uses the original arguments, including the moving pair and Buchstab boundary. -/
namespace ImbalancedChen.Part5OriginalH430MonotoneSieveHeight
noncomputable section
open Set Real
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2OriginalSingleChildWindowDictionary (W2Upper W2Upper_order)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430IntegerItineraries
open Part5OriginalH430CutoffCoherence Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedOriginalRowFreeze
open Part5OriginalH430BankSlotTargets Part5OriginalH430TaggedArithmeticReceivers
open scoped Classical BigOperators

def height (p : PhysicalNode) : ℝ := residual p / p.argument

private theorem argument_pos {p : PhysicalNode} (hL : 0<residual p)
    (hc : 0<p.ceiling) (hf : CutoffFits p) : 0<p.argument := by
  by_contra! h
  exact hL.not_ge (hf.trans (mul_nonpos_of_nonpos_of_nonneg h hc.le))

private theorem W2_last_le_target (j : Fin 36) : a3 (originalW2At j) ≤ b (originalW2At j) := by
  have ho := W2Upper_order j (2 : Fin 3)
  exact one_div_le_one_div_of_le (by linarith only [ho.1]) ho.2

theorem singleton_below_target (j : Fin 36) (s : Fin 3) {u : ℝ}
    (hu : u ∈ W2SingletonDomain (originalW2At j) s) : u < b (originalW2At j) := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hb := W2_last_le_target j
  fin_cases s
  · exact hu.2
  · exact hu.2.trans_le (hg.2.2.2.1.trans hb)
  · exact hu.2.trans_le hb

theorem pair_below_target (j : Fin 36) (s : Fin 4) {u : Point}
    (hu : u ∈ W2PairDomain (originalW2At j) s) : u 0 < b (originalW2At j) := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hb := W2_last_le_target j
  have h2 := hg.2.2.2.1.trans hb
  have h1 := hg.2.2.1.trans h2
  fin_cases s
  · exact (hu.2.1.trans hu.2.2.1).trans_le h2
  · exact hu.2.1.trans_le h1
  · exact (hu.2.1.trans hu.2.2).trans_le h1
  · exact hu.2.1.trans_le h1

private theorem marked_lt_height {x L s t : ℝ} (hL : 0<L) (hs : 0<s) (hst : s≤t)
    (hx : x/L<1/t) : x<L/s := by
  have he := (div_lt_div_iff₀ hL (hs.trans_le hst)).mp hx
  exact ((lt_div_iff₀ (hs.trans_le hst)).mpr (by simpa only [one_mul] using he)).trans_le
    (div_le_div_of_nonneg_left hL.le hs hst)

private theorem buchstab_le_height {x L s : ℝ} (hs : 0<s) (hx : 0<x)
    (hw : s-1≤L/x-1) : x≤L/s := by
  apply (le_div_iff₀ hs).mpr
  have h := (le_div_iff₀ hx).mp (show s≤L/x by linarith only [hw])
  simpa only [mul_comm] using h

/-- All nine original actions, with their own comparison target and both
physical square inequalities. Equality is allowed at the moving cutoff. -/
theorem perform_height_le {p : PhysicalNode} {r : StepShape} {z : Point}
    (hc : 0<p.ceiling) (hf : CutoffFits p) (h : LocalDomain p r z) :
    height (perform p r z) ≤ height p := by
  have hs := argument_pos h.1 hc hf
  have hc' := perform_ceiling_pos hc h
  have hf' := perform_cutoffFits hc hf h
  have hs' := argument_pos (perform_residual_pos h) hc' hf'
  change residual (perform p r z) ≤ (perform p r z).argument*(perform p r z).ceiling at hf'
  have hcfit : height (perform p r z) ≤ (perform p r z).ceiling :=
    (div_le_iff₀ hs').mpr (by simpa only [mul_comm] using hf')
  cases r with
  | retain => exact le_rfl
  | transport c => exact div_le_div_of_nonneg_left h.1.le hs h.2
  | buchstabUpper => exact hcfit.trans (buchstab_le_height hs h.2.1.1
      ((le_max_right 2 (p.argument-1)).trans h.2.2.1))
  | buchstabLower => exact hcfit.trans (buchstab_le_height hs h.2.2.1.1 h.2.2.2.1)
  | w1Fixed i j => exact div_le_div_of_nonneg_left h.1.le hs (h.2.1.trans (W1_target_le_anchor i j))
  | w2Fixed j v => exact div_le_div_of_nonneg_left h.1.le hs (h.2.1.trans (W2_target_le_fixed j v))
  | w1Singleton i j => exact hcfit.trans (marked_lt_height h.1 hs h.2.2.2.1 h.2.2.1.2).le
  | w2Singleton j v => exact hcfit.trans (marked_lt_height h.1 hs h.2.2.2.1
      (singleton_below_target j v h.2.2.1)).le
  | w2Pair j v => exact hcfit.trans (marked_lt_height h.1 hs h.2.2.2.1
      (pair_below_target j v h.2.2.1)).le

theorem realize_height_le {lo hi : ℝ} {mesh depth : ℕ} {p : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth} (hc : 0<p.physical.ceiling)
    (hf : CutoffFits p.physical) (hm : Member lo hi depth p code z) :
    height (realize depth p code z).physical ≤ height p.physical := by
  induction depth generalizing p with
  | zero => exact le_rfl
  | succ d ih => exact (ih (perform_ceiling_pos hc hm.2.2.1)
      (perform_cutoffFits hc hf hm.2.2.1) hm.2.2.2).trans (perform_height_le hc hf hm.2.2.1)

/-- Original U3/U4 root, all 430 requested levels and both branches. -/
theorem rootHistory_height_le {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (ho : o∈rootHistory N n k t p) :
    height o.current.node.physical ≤ a := by
  have hb := original_band_geometry hN hp
  have hm := rootHistory_member 0 (by omega : 1<N) ht hu hn (original_band_prime hp) hb ho
  have hc : 0 < (frozenRoot n k t (physicalPrime N p)).physical.ceiling :=
    (by norm_num [a] : (0:ℝ)<a).trans_le (rootBand_subset k hb).1
  have hh := realize_height_le hc (frozenRoot_cutoffFits n t hb) hm
  have hid := (rootHistory_realization 0 ho).1
  change height (historyNode N n k t p (pathCode 0 o.path) (pathPrimes o.path)).physical ≤ _ at hh
  rw [hid] at hh
  exact hh.trans ((frozen_cutoff_ratio ht hu hb hn).le.trans (min_le_left _ _))

theorem member_cutoff_le_original {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (ho : o∈rootHistory N n k t p) :
    cutoff (rootQ N n k t p) (parentProduct o.current.old) o.current.node.physical.argument ≤ (N:ℝ)^a := by
  have hs := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) ho
  rw [cutoff_eq_physical_power hs.1.2.1 hs.2.2.2.2.2,←hs.2.1]
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
    (rootHistory_height_le hN ht hu hn hp ho)

end
end ImbalancedChen.Part5OriginalH430MonotoneSieveHeight
