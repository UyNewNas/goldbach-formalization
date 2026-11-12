import ImbalancedChen.Part5OriginalH430ClassicalRootThetaPayment
import ImbalancedChen.P5ZU1011H248CommonPartition
import ImbalancedChen.ActualRosserInitialResidualSaving
import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

/-! The source query and its selected common endpoint both stay in
the constant part of the ordinary upper amplitude. The same actual p
is too large for any factor window of the original Wu improvement class. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRootPriceGeometry
noncomputable section
open Set Real Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P5OriginalFeedbackTableKernels (tableAtomSet)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenTableRootMass (frozenQuery)
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedReads
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430FrozenClassicalRootModuli

/-- The original source argument is at most 149/50. An actual closed
cell grows by exactly 1/50, even at either knot. This works for every
auxiliary mesh, including the coarsest one. -/
theorem actual_classical_queries {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    let s := frozenQuery n .U3 τ (physicalPrime N p)
    let w := queryAt (keyAt N n m .U3 τ p)
    2 ≤ s ∧ s ≤ 149/50 ∧ s ≤ w ∧ w ≤ 3 := by
  let t := physicalPrime N p
  let r := rootRequest N n .U3 τ p
  let c := keyAt N n m .U3 τ p
  let s := r.node.physical.argument
  obtain ⟨hb, ht⟩ := Finset.mem_filter.mp hp
  have htotal : (sourceRoot .U3 τ t).physical.total = 1/2-τ := by
    simp only [sourceRoot, sourceResidual, U3Residual, if_neg (not_lt.mpr ht), tailResidual]
    ring
  have hlevel := (frozenLevel_bounds (root_total_bounds hτ hτ' (original_band_geometry hN hb)) n).1
  have hs : 2 ≤ s := le_max_left _ _
  have hs' : s ≤ 149/50 := by
    change max 2 ((frozenLevel n (sourceRoot .U3 τ t).physical.total-t)/a) ≤ 149/50
    change frozenLevel n (sourceRoot .U3 τ t).physical.total ≤ (sourceRoot .U3 τ t).physical.total at hlevel
    rw [htotal] at hlevel ⊢
    apply max_le (by norm_num)
    apply (div_le_iff₀ (by norm_num [a] : 0<a)).mpr
    change tailCutoff ≤ t at ht
    dsimp [tailCutoff, a] at ht ⊢
    linarith
  obtain ⟨b, hbat⟩ := P5Z.U1011H248Partition.exists_upperAtom_of_mem
    (show s ∈ Icc (1:ℝ) 5 from ⟨by linarith, by linarith⟩)
  have hex : ∃ b, r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b := ⟨b,hbat⟩
  have hmode : r.mode = .scalar := rfl
  have hsome : ∃ i, resolve 430 r = some i := by
    unfold resolve
    rw [hmode, dif_pos hex]
    exact ⟨_, rfl⟩
  obtain ⟨i, hi⟩ := hsome
  have hcell : p ∈ rootFibre N n m .U3 τ c := Finset.mem_filter.mpr ⟨hb,rfl⟩
  have hg := original_fibre_geometry hN hτ hτ' hn hcell
  obtain ⟨hsCell, hwCell, _⟩ := hg.2.2.2.2.1 i hi
  have hleft : 1+(i.val:ℝ)/50 ≤ s := hsCell.1
  have hright : queryAt c ≤ 1+((i.val:ℝ)+1)/50 := hwCell.2
  exact ⟨hs, hs', hg.2.1, by linarith only [hleft, hright, hs']⟩

theorem actual_classical_amplitudes {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    upperAmplitude (frozenQuery n .U3 τ (physicalPrime N p)) = 1 ∧
      P5CanonicalUpperCancellation.upperA (queryAt (keyAt N n m .U3 τ p)) = 1 := by
  obtain ⟨hs, hs', hsw, hw⟩ := actual_classical_queries (m := m) hN hτ hτ' hn hp
  refine ⟨?_, P5CanonicalUpperCancellation.upperA_eq_one (by linarith) hw⟩
  unfold upperAmplitude
  rw [suzukiContinuousUpperFactor_eq_initial_of_actual_limits _ (by linarith) (by linarith)]
  field_simp [(by linarith : frozenQuery n .U3 τ (physicalPrime N p) ≠ 0), Real.exp_ne_zero]
  <;> ring

/-- At every original classical prime, p² exceeds even the full
half-level before the positive τ slack or downward freezing. -/
theorem external_prime_square_gt_half {N p : ℕ} (hN : 2 ≤ N) (hp : p ∈ classicalBand N) :
    (N:ℝ)^(1/2:ℝ) < (p:ℝ)^2 := by
  obtain ⟨hb, ht⟩ := Finset.mem_filter.mp hp
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpr : (0:ℝ)<p := Nat.cast_pos.mpr (original_band_prime hb).1.pos
  have hpw : (N:ℝ)^physicalPrime N p = (p:ℝ) := residual_rpow_log_div _ _ hNr hpr
  rw [pow_two, ← hpw, ← Real.rpow_add (zero_lt_one.trans hNr)]
  apply Real.rpow_lt_rpow_of_exponent_lt hNr
  dsimp [tailCutoff] at ht
  linarith

/-- No admissible old Wu convolution has this actual external root
prime in any of its displayed factor windows. Its nonzero gaps are
licensed on different source families. -/
theorem external_prime_outside_Wu_windows {N p k i : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hp : p ∈ classicalBand N) (hδ : 0 ≤ δ)
    (hbox : wuSourceBox k δ N i Δ V) (j : Fin i) :
    p ∉ convolutionWuWindows N Δ V j := by
  intro hj
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hv (l : Fin i) : 1 ≤ V l := (Real.one_le_rpow hNr (pow_nonneg hδ _)).trans
    (hbox.2.2.2.2.1 l)
  have hpref : 1 ≤ ∏ l ∈ Finset.univ.filter (fun l : Fin i => l < j), V l :=
    Finset.one_le_prod (fun l _ => hv l)
  have hsq : (V j)^2 ≤ (N:ℝ)^(1/2-δ) :=
    (le_mul_of_one_le_left (sq_nonneg _) hpref).trans (hbox.2.2.2.2.2 j)
  have hcap := Real.rpow_le_rpow_of_exponent_le hNr (show 1/2-δ ≤ (1/2:ℝ) by linarith)
  have hlt := (mem_convolutionWuWindows.mp hj).2.2.2
  have hmore := external_prime_square_gt_half hN hp
  nlinarith only [hsq.trans hcap, hmore, mul_nonneg (sub_nonneg.mpr hlt.le)
    (add_nonneg (Nat.cast_nonneg p) (zero_le_one.trans (hv j)))]

end
end ImbalancedChen.Part5OriginalH430ClassicalRootPriceGeometry
