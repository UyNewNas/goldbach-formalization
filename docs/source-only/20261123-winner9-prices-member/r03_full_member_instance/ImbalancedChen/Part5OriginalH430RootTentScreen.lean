import ImbalancedChen.Part5OriginalH430WholeMemberScreen
import ImbalancedChen.Part5OriginalH430EmittedSquareBuffer

/-! At fixed cumulative precision the largest-prime tent can contact a
physical level only on finitely many original root coordinates. One root
collar pays every descendant, including words with no fresh slots. -/
namespace ImbalancedChen.Part5OriginalH430RootTentScreen
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PrimeRegularGerms
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430SameQHistoryCells
open Part5OriginalH430FixedProgramL1 Part5OriginalH430FixedPrimeScreen Part5OriginalH430SharpPrimeBox Part5OriginalH430FullPrimeTheta
open Part5OriginalH430AllReceiverPrimePassage Part5OriginalH430ChangedPrefixDescendants
open Part5OriginalH430RequestedHistory Part5OriginalH430MixedNativeWalk Part5OriginalH430NativeQueryPaths
open Part5OriginalH430SquareStripPrimeMass (width width_pos)
open Part5OriginalH430EmittedSquareBuffer (letterFloor)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor_pos)

def collar (n j : ℕ) (t : ℝ) : Prop :=
  ∃ c : RootCode n, |VariableEnvelope.v t - codeLevel n c| ≤ width j

def radius (j : ℕ) : ℝ := min (1/100) (width j/4)

theorem radius_pos (j : ℕ) : 0 < radius j :=
  lt_min (by norm_num) (div_pos (width_pos j) (by norm_num))

private def hat (j : ℕ) (u : ℝ) := max 0 (min 1 (2-|u|/width j))

private theorem hat_one (j : ℕ) {u : ℝ} (hu : |u| ≤ width j) : hat j u = 1 := by
  have h := (div_le_one (width_pos j)).mpr hu
  simp only [hat,min_eq_left (by linarith : (1:ℝ) ≤ 2-|u|/width j),max_eq_right zero_le_one]

private theorem hat_tends {u : ℝ} (hu : u ≠ 0) : ∀ᶠ j in atTop, hat j u = 0 := by
  have hw : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hw.eventually (eventually_lt_nhds (half_pos (abs_pos.mpr hu)))] with j hj
  have h := (le_div_iff₀ (width_pos j)).mpr (by linarith : 2*width j ≤ |u|)
  exact max_eq_left ((min_le_right _ _).trans (by linarith : 2-|u|/width j ≤ 0))

private def cover (n j : ℕ) (t : ℝ) :=
  min 1 (∑ c : RootCode n, hat j (VariableEnvelope.v t-codeLevel n c))

private theorem cover_bounds (n j : ℕ) (t : ℝ) : 0 ≤ cover n j t ∧ cover n j t ≤ 1 :=
  ⟨le_min zero_le_one (Finset.sum_nonneg (fun _ _ => le_max_left _ _)),min_le_left _ _⟩

private theorem covered {n j : ℕ} {t : ℝ} (h : collar n j t) : cover n j t = 1 := by
  obtain ⟨c,hc⟩ := h
  apply min_eq_left
  calc
    (1:ℝ) = hat j (VariableEnvelope.v t-codeLevel n c) := (hat_one j hc).symm
    _ ≤ _ := Finset.single_le_sum (f:=fun b : RootCode n => hat j (VariableEnvelope.v t-codeLevel n b))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ c)

private theorem cover_continuous (n j : ℕ) : Continuous (cover n j) := by
  unfold cover hat VariableEnvelope.v VariableEnvelope.A VariableEnvelope.C
  fun_prop

private theorem tent_ae_ne (u : ℝ) : ∀ᵐ t : ℝ, VariableEnvelope.v t ≠ u := by
  filter_upwards [volume.ae_ne (2*u-1),volume.ae_ne ((57/64-u)*2/3)] with t hA hC
  rw [VariableEnvelope.v_eq_min]
  by_cases h : VariableEnvelope.A t ≤ VariableEnvelope.C t
  · rw [min_eq_left h]
    intro e
    apply hA
    dsimp [VariableEnvelope.A] at e
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    intro e
    apply hC
    dsimp [VariableEnvelope.C] at e
    linarith

private theorem cover_ae_zero (n : ℕ) {r : ℕ} (i : Fin r) :
    ∀ᵐ x : Space r, ∀ᶠ j in atTop, cover n j (x i) = 0 := by
  have h (c : RootCode n) := (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin r => (volume : Measure ℝ)) i).ae (tent_ae_ne (codeLevel n c))
  filter_upwards [Filter.eventually_all.mpr h] with x hx
  have allc (c : RootCode n) := hat_tends (sub_ne_zero.mpr (hx c))
  filter_upwards [Filter.eventually_all.mpr allc] with j hj
  simp [cover,hj]

/-- For any chosen chronological slot, in particular its actual root,
the harmonic mass of the entire cylinder shrinks with a preassigned width. -/
theorem tent_prime_mass (n : ℕ) {r : ℕ} (i : Fin r) {a eps : ℝ}
    (ha : 0<a) (hb : a<1) (he : 0<eps) :
    ∀ᶠ j in atTop, ∀ᶠ N in atTop, badMass N a {x : Space r | collar n j (x i)} < eps := by
  let B := box r a
  let f (j : ℕ) (x : Space r) := cover n j (x i)
  have hf (j : ℕ) : Continuous (f j) := (cover_continuous n j).comp (continuous_apply i)
  have hB : MeasurableSet B := measurableSet_logPrimeBox _ _
  have hk : Measurable (kernel (r:=r)) := Finset.measurable_prod _ (fun _ _ =>
    measurable_const.div (measurable_pi_apply _))
  have I : Tendsto (fun j => ∫ x in B, f j x * kernel x) atTop (𝓝 0) := by
    have H : Tendsto (fun j => ∫ x in B, f j x*kernel x) atTop (𝓝 (∫ _x in B, (0:ℝ))) := by
      apply tendsto_integral_of_dominated_convergence kernel
      · exact fun j => ((hf j).measurable.mul hk).aestronglyMeasurable
      · exact integrableOn_logPrimeBox_one_div _ _ (fun _=>ha)
      · intro j
        filter_upwards [ae_restrict_mem hB] with x hx
        have h0 := (kernel_bounds ha hx).1
        have hf0 := cover_bounds n j (x i)
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hf0.1 h0)]
        exact (mul_le_mul_of_nonneg_right hf0.2 h0).trans_eq (one_mul _)
      · filter_upwards [ae_restrict_of_ae (cover_ae_zero n i)] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [hx] with j hj
        simp [f,hj]
    simpa only [integral_zero] using H
  filter_upwards [I.eventually (eventually_lt_nhds he)] with j hj
  have hp := tendsto_actualPrimeBoxTestSum_cube ha hb (f j) (hf j).continuousOn
  filter_upwards [hp.eventually (eventually_lt_nhds hj)] with N hN
  apply lt_of_le_of_lt _ hN
  unfold badMass actualPrimeBoxTestSum
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
  by_cases h : collar n j ((actualPrimeTupleLog N p) i)
  · simpa only [Set.indicator_of_mem h,f,covered h]
  · simpa only [Set.indicator_of_notMem h] using (cover_bounds n j ((actualPrimeTupleLog N p) i)).1

private theorem one_width (n : ℕ) :
    ∃ j : ℕ, (∀ᶠ N in atTop,
      badMass N bottom {x : Space 1 | collar n j (x 0)} < width n) ∧
      ∀ r : Fin 881, ∀ᶠ N in atTop,
        badMass N letterFloor {x : Space (r.val+1) | collar n j (x 0)} < width n := by
  have H (r : Fin 881) := tent_prime_mass n (0:Fin (r.val+1))
    (lt_min (by norm_num) frozenLeafCutoffFloor_pos : 0<letterFloor)
    ((min_le_left _ _).trans_lt (by norm_num) : letterFloor<1) (width_pos n)
  exact ((tent_prime_mass n (0:Fin 1) bottom_pos bottom_lt_one (width_pos n)).and
    (Filter.eventually_all.mpr H)).exists

/-- Chosen once from the root geometry at n, prior to the prime target or
any child, submask, selected table row, or remaining coordinate. -/
def collarIndex (n : ℕ) := Classical.choose (one_width n)

theorem diagonal_mass {eps : ℝ} (he : 0<eps) :
    ∀ᶠ n in atTop, ∀ᶠ N in atTop,
      badMass N bottom {x : Space 1 | collar n (collarIndex n) (x 0)} < eps := by
  have hw : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hw.eventually (eventually_lt_nhds he)] with n hn
  filter_upwards [(Classical.choose_spec (one_width n)).1] with N hN
  exact hN.trans hn

theorem all_word_mass (n : ℕ) :
    ∀ᶠ N in atTop, ∀ r : Fin 881,
      badMass N letterFloor {x : Space (r.val+1) | collar n (collarIndex n) (x 0)} < width n :=
  Filter.eventually_all.mpr (Classical.choose_spec (one_width n)).2

def rootFirst {mesh d : ℕ} (code : Program mesh d) :
    Fin (1+Fintype.card (Slots (shapes code))) ≃ NativeSlot (shapes code) :=
  finSumFinEquiv.symm.trans (finOneEquiv.sumCongr (Fintype.equivFin (Slots (shapes code))).symm)

@[simp] theorem rootFirst_root {mesh d : ℕ} (code : Program mesh d) :
    (rootFirst code).symm (.inl ()) = Fin.castAdd (Fintype.card (Slots (shapes code))) 0 := by
  simp [rootFirst,finOneEquiv,Equiv.equivPUnit,Equiv.ofUnique]

/-- The actual additive-prime count on root-collar DESCENDANTS, summed
over all integer suffixes. Both overlapping roots use their own Q and
integer positions; arbitrary signed tests include inherited/rejected. -/
theorem all_root_tent_descendants (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : Programs mesh)
      (k : Root) (m : ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      descendants N n m k v.2 (rootFirst v.2)
        (fun p : Fin 1 → ℕ => collar n (collarIndex n) (actualPrimeTupleLog N p 0)) E f 0 < eps := by
  have H (v : Programs mesh) (k : Root) :=
    descendants_of_small_screen he v.2 (rootFirst v.2) k
      (fun n => {x : Space 1 | collar n (collarIndex n) (x 0)}) (fun _ h => diagonal_mass h)
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr (H v))] with n hn
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr (hn v))] with N hN
  exact fun hE v k => hN v k hE

end
end ImbalancedChen.Part5OriginalH430RootTentScreen
