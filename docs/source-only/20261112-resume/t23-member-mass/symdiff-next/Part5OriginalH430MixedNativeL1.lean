import ImbalancedChen.Part5OriginalH430MixedNativeWalk
import ImbalancedChen.Part5OriginalH430NativeMovingDensity

namespace ImbalancedChen.Part5OriginalH430MixedNativeL1
noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Classical BigOperators
open P5OriginalActionMassBound P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph Part5OriginalH430NativeQueryPaths
open Part5OriginalH430FreshAxis Part5OriginalH430MixedGateStability Part5OriginalH430MixedNativeWalk
open Part5OriginalH430NativeMovingDensity Part5OriginalH430FullMemberStrips
open Part5OriginalH430FullMemberMeasurable Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass
open Part5OriginalH430DescendantLimits Part5OriginalH430FullRootAmplitude
open Part5OriginalH430InheritedMemberL1 Part5OriginalUpsilon5CausalDictionary (a FloorAtom)

private theorem rootState {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (k : Root) :
    State (fun x : Chart ι => x j ∈ rootBand k) (fun x => sourceRoot k 0 (x j))
      (fun n x => frozenRoot n k (finiteTau n) (x j)) := by
  have h := sourceRoot_stateMeasurable k 0
  have hcoord := (measurable_pi_apply j : Measurable (fun x : Chart ι => x j))
  let emptyCode : Program 0 0 := Fin.elim0
  let emptyZ : Coordinates 0 := Fin.elim0
  refine ⟨⟨h.1.comp hcoord,h.2.1.comp hcoord,h.2.2.comp hcoord⟩,?_,?_,
    fun _ hx => sourceRoot_argument (by norm_num) (by norm_num) hx,
    fun _ hx => frozenDescendant_residual_tendsto hx emptyCode emptyZ,
    fun _ hx => frozenQuery_tendsto hx,?_,fun _ _ => rfl,fun _ _ => rfl,?_⟩
  · intro x hx
    rw [sourceRoot_residual]
    exact (by norm_num : (0:ℝ)<11/192).trans_le (sourceResidual_bounds (by norm_num) (by norm_num) hx).1
  · intro x hx
    exact (by norm_num [a] : (0:ℝ)<a).trans_le (rootBand_subset k hx).1
  · intro x hx n
    have hl := (rootLoss_bounds (n := n) (finiteTau_pos n).le (finiteTau_le n) hx).1
    rw [← actual_descendant_residual_loss n k (finiteTau n) (x j) emptyCode emptyZ] at hl
    exact sub_nonneg.mp hl
  · intro c
    suffices hsign : ∀ᵐ t : ℝ, t ∈ rootBand k → ∀ᶠ n : ℕ in atTop,
        Compares (frozenQuery n k (finiteTau n) t) (idealQuery k t) c by
      exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℝ)) j).ae hsign
    filter_upwards [volume.ae_ne (1-2*a*c),volume.ae_ne ((57/64-a*c)*2/5),
      volume.ae_ne (1/2-a*c)] with t ha hb hd
    intro ht
    by_cases he : idealQuery k t = 2
    · exact .of_forall (fun n => by
        change Compares (frozenQuery n k (finiteTau n) t) (idealQuery k t) c
        rw [ideal_clamp_preserved (finiteTau_pos n).le (finiteTau_le n) ht he,he]
        exact ⟨Iff.rfl,Iff.rfl⟩)
    · apply cmp_of_ne (frozenQuery_tendsto ht)
      intro hq
      exact (proper_root_fibre he hq).elim ha (fun h' => h'.elim hb hd)

/-- All original cells can be fixed to a specified Program or assigned
by the native canonical owner. Both roots see the identical labelled
coordinates and the same code. -/
theorem full_program_eventually {mesh d : ℕ} {lo hi : ℝ} (k : Root)
    (s : Fin d → StepShape) (code : Chart (NativeSlot s) → Program mesh d)
    (hcode : ∀ x i, (code x i).1 = s i) (lower : Bool) (atom : FloorAtom) :
    ∀ᵐ x : Chart (NativeSlot s), nativeRootCoordinate x ∈ rootBand k → ∀ᶠ n : ℕ in atTop,
      (QueryMember lo hi (frozenRoot n k (finiteTau n) (nativeRootCoordinate x))
          (code x) (nativeCoordinates s x) lower atom ↔
        QueryMember lo hi (sourceRoot k 0 (nativeRootCoordinate x))
          (code x) (nativeCoordinates s x) lower atom) := by
  apply walk (rootState (Sum.inl () : NativeSlot s) k) s (fun i => Sum.inr i)
    (fun _ _ e => Sum.inr.inj e) _ code hcode lower atom
  intro j x
  change sourceRoot k 0 (update x (.inr j) 0 (.inl ())) = sourceRoot k 0 (x (.inl ()))
  rw [update_of_ne (by simp : (Sum.inl () : NativeSlot s) ≠ Sum.inr j)]

theorem nativeSet_eventually {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) :
    ∀ᵐ x : NativeSlot s → ℝ, nativeRootCoordinate x ∈ rootBand k → ∀ᶠ n : ℕ in atTop,
      x ∈ nativeSet mesh k s lower atom (some n) ↔ x ∈ nativeSet mesh k s lower atom none :=
  full_program_eventually k s (nativeProgram mesh s) (fun _ _ => rfl) lower atom

def difference {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) : Set (NativeSlot s → ℝ) :=
  let I := nativeSet mesh k s lower atom none
  let S := nativeSet mesh k s lower atom (some n)
  (I \ S) ∪ (S \ I)

theorem difference_measurable {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) :
    MeasurableSet (difference mesh k s lower atom n) := by
  have hi := nativeSet_measurable mesh k s lower atom none
  have hs := nativeSet_measurable mesh k s lower atom (some n)
  exact (hi.diff hs).union (hs.diff hi)

/-- Ordinary volume of the entire mixed active/inherited symmetric
difference in the genuine finite cube. No mass premise. -/
theorem mixed_difference_volume {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) :
    Tendsto (fun n : ℕ => volume.real (region k s ∩ difference mesh k s lower atom n))
      atTop (𝓝 0) := by
  let B := region k s
  let D := difference mesh k s lower atom
  let F (n : ℕ) := (D n).indicator (fun _ => (1:ℝ))
  have hm : MeasurableSet B := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  have hb : volume B < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (difference_measurable _ _ _ _ _ _)
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict B, ‖F n x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    by_cases h : x ∈ D n <;> simp [F,h]
  have hlim : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => F n x) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem hm,
      ae_restrict_of_ae (nativeSet_eventually mesh k s lower atom)] with x hx hh
    apply tendsto_const_nhds.congr'
    filter_upwards [hh hx.2] with n hn
    have hout : x ∉ D n := by
      change ¬((x ∈ _ ∧ x ∉ _) ∨ (x ∈ _ ∧ x ∉ _))
      tauto
    simp [F,hout]
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict B) (f := fun _ : NativeSlot s → ℝ => (0:ℝ))
    (fun _ => (1:ℝ)) (fun n => (hF n).aestronglyMeasurable)
    (integrableOn_const hb.ne) hbound hlim
  have he (n : ℕ) : (∫ x in B, F n x) = volume.real (B ∩ D n) := by
    rw [show F n = (D n).indicator (fun _ => (1:ℝ)) from rfl,
      setIntegral_indicator (difference_measurable _ _ _ _ _ _),setIntegral_const,smul_eq_mul,mul_one]
  simpa only [integral_zero,he] using h

/-- Shared owner restrictions can even vary with the precision. The
estimate is absolute with respect to the full native cube. -/
theorem shared_owner_difference {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (O : ℕ → Set (NativeSlot s → ℝ)) :
    Tendsto (fun n : ℕ => volume.real ((region k s ∩ difference mesh k s lower atom n) ∩ O n))
      atTop (𝓝 0) := by
  have hb : volume (region k s) < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (mixed_difference_volume mesh k s lower atom)
  · exact .of_forall (fun _ => ENNReal.toReal_nonneg)
  · exact .of_forall (fun _ => ENNReal.toReal_mono
      (ne_top_of_le_ne_top hb.ne (measure_mono inter_subset_left)) (measure_mono inter_subset_left))

def nativeError {d : ℕ} (mesh : ℕ) (k : Root) (s : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (n : ℕ) : ℝ :=
  ∫ x in region k s, |(nativeSet mesh k s lower atom none).indicator
      (density mesh k s none) x -
    (nativeSet mesh k s lower atom (some n)).indicator (density mesh k s (some n)) x|

/-- Each of the actual zero extensions is integrable on the full
original region at every sufficiently fine precision. -/
theorem fine_extended_integrable {d : ℕ} (hd : d ≤ 440) (mesh : ℕ) (k : Root)
    (s : Fin d → StepShape) (lower : Bool) (atom : FloorAtom) {n : ℕ}
    (hn : meshError n ≤ 11/384) :
    IntegrableOn ((nativeSet mesh k s lower atom none).indicator (density mesh k s none)) (region k s) ∧
    IntegrableOn ((nativeSet mesh k s lower atom (some n)).indicator (density mesh k s (some n))) (region k s) := by
  let B := region k s
  have hm : MeasurableSet B := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  have hb : volume B < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hconst : Integrable (fun _ : NativeSlot s → ℝ => envelope) (volume.restrict B) :=
    integrableOn_const hb.ne
  have hpos : 0 ≤ envelope := div_nonneg (by norm_num) (mul_nonneg productFloor_pos.le frozenResidualFloor_pos.le)
  have each (v : Option ℕ)
      (h : ∀ x ∈ B, x ∈ nativeSet mesh k s lower atom v → |density mesh k s v x| ≤ envelope) :
      IntegrableOn ((nativeSet mesh k s lower atom v).indicator (density mesh k s v)) B := by
    apply hconst.mono' (((density_measurable mesh k s v).indicator
      (nativeSet_measurable mesh k s lower atom v)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hm] with x hx
    by_cases hg : x ∈ nativeSet mesh k s lower atom v
    · simpa only [indicator_of_mem hg,Real.norm_eq_abs] using h x hx hg
    · simpa only [indicator_of_notMem hg,norm_zero] using hpos
  exact ⟨each none (fun _ hx hg => ideal_weight_bound hx.2 hd hg.1),
    each (some n) (fun _ hx hg => frozen_weight_bound hx.2 hd hn hg.1)⟩

/-- Both physical weights extended by zero on their own original sets
in the same native coordinates. Every prefix can mix all nine shapes. -/
theorem mixed_full_native_L1 {d : ℕ} (hd : d ≤ 440) (mesh : ℕ) (k : Root)
    (s : Fin d → StepShape) (lower : Bool) (atom : FloorAtom) :
    Tendsto (nativeError mesh k s lower atom) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => rate n * volume.real (region k s) +
      volume.real (region k s ∩ difference mesh k s lower atom n)*envelope) atTop (𝓝 0) := by
    simpa only [zero_mul,add_zero] using (rate_tendsto.mul_const (volume.real (region k s))).add
      ((mixed_difference_volume mesh k s lower atom).mul_const envelope)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact .of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  · exact eventually_fine_mesh.mono (fun _ hn => all_shapes_integral_bound hd mesh k s lower atom hn)

abbrev Family := (d : Fin 441) × (Fin d.val → StepShape)

/-- A single continuous precision threshold simultaneously controls all
original finite itineraries, polarities and 401 atoms at the chosen
mesh. No arithmetic N or future selected-count normalization is used. -/
theorem finite_mixed_native_threshold (mesh : ℕ) {eps : ℝ} (he : 0 < eps) :
    ∃ T : ℕ, ∀ n ≥ T, ∀ v : Family, ∀ k : Root, ∀ lower : Bool, ∀ atom : FloorAtom,
      nativeError mesh k v.2 lower atom n < eps ∧
      volume.real (region k v.2 ∩ difference mesh k v.2 lower atom n) < eps := by
  have each (v : Family) (k : Root) (lower : Bool) (atom : FloorAtom) :
      ∀ᶠ n : ℕ in atTop, nativeError mesh k v.2 lower atom n < eps ∧
        volume.real (region k v.2 ∩ difference mesh k v.2 lower atom n) < eps :=
    ((mixed_full_native_L1 (by have hv := v.1.isLt; omega : v.1.val ≤ 440) mesh k v.2 lower atom).eventually
      (eventually_lt_nhds he)).and
      ((mixed_difference_volume mesh k v.2 lower atom).eventually (eventually_lt_nhds he))
  exact eventually_atTop.1 (Filter.eventually_all.mpr (fun v : Family =>
    Filter.eventually_all.mpr (fun k : Root => Filter.eventually_all.mpr (fun lower : Bool =>
      Filter.eventually_all.mpr (each v k lower)))))

end
end ImbalancedChen.Part5OriginalH430MixedNativeL1

