import ImbalancedChen.Part5OriginalH430NativePrefixFubini
import ImbalancedChen.Part5OriginalH430OwnedMemberMass
import ImbalancedChen.Part5OriginalH430FullRootAmplitude

/-! Uniform compact physical weights for the complete original native
itinerary. Integrate the absolute density displacement on the entire
moving frozen Member, including the part rejected by the ideal path. -/
namespace ImbalancedChen.Part5OriginalH430NativeMovingDensity
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open P5OriginalActionMassBound P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph Part5OriginalH430NativeProperSections
open Part5OriginalH430NativeQueryPaths Part5OriginalH430OwnedMemberMass
open Part5OriginalH430NativePrefixFubini Part5OriginalH430FullMemberMeasurable
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430FullRootAmplitude Part5OriginalH430FullMemberStrips
open Part5OriginalUpsilon5CausalDictionary (a FloorAtom)

def slotFloor : ℝ := min 1 (min a (frozenResidualFloor/6))
theorem slotFloor_pos : 0 < slotFloor := lt_min zero_lt_one
  (lt_min (by norm_num [a]) (div_pos frozenResidualFloor_pos (by norm_num)))
def productFloor : ℝ := slotFloor^881
theorem productFloor_pos : 0 < productFloor := pow_pos slotFloor_pos _
def envelope : ℝ := 4/(productFloor*frozenResidualFloor)
def rate (n : ℕ) : ℝ := (4/productFloor)*levelError n (finiteTau n)/(frozenResidualFloor*frozenResidualFloor)

private def Above (b : ℝ) (p : PhysicalNode) : Prop := ∀ x ∈ word p, b ≤ x

private theorem one_above {b x s : ℝ} {p : PhysicalNode} (hp : Above b p) (hx : b ≤ x) :
    Above b (appendOne p x s) := by
  intro v hv
  simp only [word_appendOne,List.mem_append,List.mem_singleton] at hv
  exact hv.elim (hp v) (fun he => he.symm ▸ hx)

private theorem pair_above {b x y s : ℝ} {p : PhysicalNode} (hp : Above b p)
    (hx : b ≤ x) (hy : b ≤ y) : Above b (appendPair p x y s) := by
  intro v hv
  simp only [word_appendPair,List.mem_append,List.mem_cons,List.mem_singleton] at hv
  rcases hv with h | he | he
  · exact hp v h
  · exact he.symm ▸ hy
  · exact he.symm ▸ hx

private theorem first_step_floor {b : ℝ} {p : PhysicalNode} {s : StepShape} {z : Point}
    (hp : Above b p) (hL : b ≤ residual p/6) (hz : LocalDomain p s z) :
    Above b (perform p s z) := by
  have hx (j : Fin 2) (hj : j.val < arity s) := hL.trans (fresh_coordinate_floor hz hj)
  cases s with
  | buchstabUpper | buchstabLower | w1Singleton _ _ | w2Singleton _ _ =>
    exact one_above hp (hx 0 (by decide))
  | w2Pair i j => exact pair_above hp (hx 0 (by decide)) (hx 1 (by decide))
  | _ => exact hp

private theorem full_floor {b lo hi : ℝ} {mesh d : ℕ} {p : TypedNode}
    {code : Program mesh d} {z : Coordinates d} (hp : Above b p.physical)
    (hz : Member lo hi d p code z)
    (hL : 6*b ≤ residual (realize d p code z).physical) :
    Above b (realize d p code z).physical := by
  induction d generalizing p with
  | zero => exact hp
  | succ d ih =>
    apply ih _ hz.2.2.2 hL
    apply first_step_floor hp _ hz.2.2.1
    linarith only [hL.trans (member_residual_le_root hz)]

private theorem prod_floor {w : List ℝ} (hw : ∀ x ∈ w, slotFloor ≤ x)
    (hlen : w.length ≤ 881) : productFloor ≤ w.prod := by
  have lower (v : List ℝ) (h : ∀ x ∈ v, slotFloor ≤ x) : slotFloor^v.length ≤ v.prod := by
    induction v with
    | nil => simp
    | cons x xs ih =>
      rw [List.length_cons,pow_succ,List.prod_cons,mul_comm (slotFloor^xs.length)]
      exact mul_le_mul (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))) (pow_nonneg slotFloor_pos.le _)
        (slotFloor_pos.le.trans (h x (List.mem_cons_self ..)))
  exact (pow_le_pow_of_le_one slotFloor_pos.le (min_le_left _ _) hlen).trans (lower w hw)

private theorem root_product {lo hi t : ℝ} {mesh d : ℕ} {p : TypedNode}
    (code : Program mesh d) (z : Coordinates d) (hd : d ≤ 440)
    (hroot : word p.physical = [t]) (ht : a ≤ t) (hz : Member lo hi d p code z)
    (hL : frozenResidualFloor ≤ residual (realize d p code z).physical) :
    productFloor ≤ (word (realize d p code z).physical).prod := by
  have hp : Above slotFloor p.physical := by
    intro x hx
    rw [hroot,List.mem_singleton] at hx
    rw [hx]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans ht
  have hg : slotFloor ≤ frozenResidualFloor/6 := (min_le_right _ _).trans (min_le_right _ _)
  apply prod_floor (full_floor hp hz (by linarith only [hg,hL]))
  have h0 := congrArg List.length hroot
  simp only [word,List.length_map,List.length_cons,List.length_nil] at h0
  have hk := realize_rank p code z
  simp only [word,List.length_map]
  omega

private theorem ideal_floor {lo hi t : ℝ} {k : Root} {mesh d : ℕ} {code : Program mesh d}
    {z : Coordinates d} (ht : t ∈ rootBand k) (hd : d ≤ 440)
    (hz : Member lo hi d (sourceRoot k 0 t) code z) :
    frozenResidualFloor ≤ residual (realize d (sourceRoot k 0 t) code z).physical := by
  apply le_trans _ (actual430_residual_floor (by norm_num) (by norm_num) ht hd hz)
  unfold frozenResidualFloor residualFloor
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

private theorem weight_bound_of_floor {p : PhysicalNode} (hw : productFloor ≤ (word p).prod)
    (hL : frozenResidualFloor ≤ residual p) : |physicalWeight p| ≤ envelope := by
  have hden := mul_le_mul hw hL frozenResidualFloor_pos.le (productFloor_pos.le.trans hw)
  have h0 := mul_pos productFloor_pos frozenResidualFloor_pos
  change |4/((word p).prod*residual p)| ≤ _
  rw [abs_of_pos (div_pos (by norm_num) (h0.trans_le hden))]
  exact div_le_div_of_nonneg_left (by norm_num) h0 hden

theorem ideal_weight_bound {lo hi t : ℝ} {k : Root} {mesh d : ℕ} {code : Program mesh d}
    {z : Coordinates d} (ht : t ∈ rootBand k) (hd : d ≤ 440)
    (hz : Member lo hi d (sourceRoot k 0 t) code z) :
    |physicalWeight (realize d (sourceRoot k 0 t) code z).physical| ≤ envelope := by
  have hL := ideal_floor ht hd hz
  exact weight_bound_of_floor (root_product code z hd rfl (rootBand_subset k ht).1 hz hL) hL

theorem frozen_weight_bound {lo hi t : ℝ} {n : ℕ} {k : Root} {mesh d : ℕ} {code : Program mesh d}
    {z : Coordinates d} (ht : t ∈ rootBand k) (hd : d ≤ 440) (hn : meshError n ≤ 11/384)
    (hz : Member lo hi d (frozenRoot n k (finiteTau n) t) code z) :
    |physicalWeight (realize d (frozenRoot n k (finiteTau n) t) code z).physical| ≤ envelope := by
  have hL := frozen430_residual_floor (finiteTau_pos n).le (finiteTau_le n) ht hn hd hz
  exact weight_bound_of_floor (root_product code z hd rfl (rootBand_subset k ht).1 hz hL) hL

theorem frozen_admitted_density_error {lo hi t : ℝ} {n : ℕ} {k : Root} {mesh d : ℕ}
    {code : Program mesh d} {z : Coordinates d} (ht : t ∈ rootBand k) (hd : d ≤ 440)
    (hn : meshError n ≤ 11/384) (hz : Member lo hi d (frozenRoot n k (finiteTau n) t) code z) :
    |physicalWeight (realize d (sourceRoot k 0 t) code z).physical -
        physicalWeight (realize d (frozenRoot n k (finiteTau n) t) code z).physical| ≤ rate n := by
  have hL := frozen430_residual_floor (finiteTau_pos n).le (finiteTau_le n) ht hn hd hz
  have hw := root_product code z hd rfl (rootBand_subset k ht).1 hz hL
  have he := descendant_physicalWeight_error (finiteTau_pos n).le (finiteTau_le n) ht hn hd hz
  have hword := congrArg (List.map Slot.exponent)
    (realize_slots_eq (p := sourceRoot k 0 t) (q := frozenRoot n k (finiteTau n) t) rfl code z)
  change word _ = word _ at hword
  apply he.trans
  rw [hword,abs_of_pos (div_pos (by norm_num) (productFloor_pos.trans_le hw))]
  apply div_le_div_of_nonneg_right _ (mul_nonneg frozenResidualFloor_pos.le frozenResidualFloor_pos.le)
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) productFloor_pos hw)
    (add_nonneg (finiteTau_pos n).le (meshError_pos n).le)

def nativeSet {d : ℕ} (mesh : ℕ) (k : Root) (shape : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (prec : Option ℕ) : Set (NativeSlot shape → ℝ) := {x |
  let t := nativeRootCoordinate x
  let p := match prec with | none => sourceRoot k 0 t | some n => frozenRoot n k (finiteTau n) t
  QueryMember 0 1 p (nativeProgram mesh shape x) (nativeCoordinates shape x) lower atom}

def density {d : ℕ} (mesh : ℕ) (k : Root) (shape : Fin d → StepShape) (prec : Option ℕ)
    (x : NativeSlot shape → ℝ) : ℝ :=
  physicalWeight (nativeParent mesh k (match prec with | none => 0 | some n => finiteTau n) prec shape x)

def region {d : ℕ} (k : Root) (shape : Fin d → StepShape) : Set (NativeSlot shape → ℝ) :=
  Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) ∩ nativeRootCoordinate ⁻¹' rootBand k

private theorem member_coordinate {d mesh : ℕ} {lo hi : ℝ} {p : TypedNode}
    {code : Program mesh d} {z : Coordinates d} (hz : Member lo hi d p code z) :
    ∀ i j, z i j ∈ Icc lo hi := by
  induction d generalizing p with
  | zero => intro i; exact Fin.elim0 i
  | succ d ih =>
    apply Fin.cases _ (ih hz.2.2.2)
    intro j
    fin_cases j
    · exact hz.1.1
    · exact hz.1.2.1

/-- The bounding box used by the joint integral includes the complete
admitted path above the original root band, for both densities. -/
theorem nativeSet_in_region {d mesh : ℕ} {k : Root} {shape : Fin d → StepShape}
    {lower : Bool} {atom : FloorAtom} {prec : Option ℕ} {x : NativeSlot shape → ℝ}
    (ht : nativeRootCoordinate x ∈ rootBand k) (hx : x ∈ nativeSet mesh k shape lower atom prec) :
    x ∈ region k shape := by
  have hr := rootBand_subset k ht
  have hroot : nativeRootCoordinate x ∈ Icc (0:ℝ) 1 :=
    ⟨(by norm_num [a] : (0:ℝ) ≤ a).trans hr.1,hr.2.trans (by norm_num)⟩
  have hcoord := member_coordinate hx.1
  have hall (i : NativeSlot shape) : x i ∈ Icc (0:ℝ) 1 := by
    rcases i with u | ⟨t,j⟩
    · cases u; exact hroot
    · let s : Fin 2 := ⟨j.val,j.isLt.trans_le (arity_le_two (shape t))⟩
      simpa [nativeCoordinates,s,j.isLt] using hcoord t s
  exact ⟨⟨fun i => (hall i).1,fun i => (hall i).2⟩,ht⟩

theorem rate_tendsto : Tendsto rate atTop (𝓝 0) := by
  simpa [rate] using (levelError_finiteTau_tendsto.const_mul (4/productFloor)).div_const
    (frozenResidualFloor*frozenResidualFloor)

theorem nativeSet_measurable {d : ℕ} (mesh : ℕ) (k : Root) (shape : Fin d → StepShape)
    (lower : Bool) (atom : FloorAtom) (prec : Option ℕ) :
    MeasurableSet (nativeSet mesh k shape lower atom prec) := by
  cases prec with
  | none => exact (actual_native_QueryMember_measurable 0 mesh k 0 shape lower atom).1
  | some n => exact (actual_native_QueryMember_measurable n mesh k (finiteTau n) shape lower atom).2

private theorem wordprod_meas {X : Type*} [MeasurableSpace X] {d mesh : ℕ} {p : X → TypedNode}
    (hp : Measurable (fun x => (word (p x).physical).prod)) (code : Program mesh d)
    {z : X → Coordinates d} (hz : ∀ i j, Measurable (fun x => z x i j)) :
    Measurable (fun x => (word (realize d (p x) code (z x)).physical).prod) := by
  induction d generalizing p with
  | zero => exact hp
  | succ d ih =>
    apply ih _ (tail code) (fun i j => hz i.succ j)
    change Measurable (fun x => (word (perform (p x).physical (code 0).1 (z x 0))).prod)
    cases (code 0).1 <;>
      simp only [perform,word_appendOne,word_appendPair,List.prod_append,List.prod_cons,List.prod_nil,mul_one]
    all_goals first | exact hp | exact hp.mul (hz 0 0) | exact hp.mul ((hz 0 1).mul (hz 0 0))

theorem density_measurable {d : ℕ} (mesh : ℕ) (k : Root) (shape : Fin d → StepShape)
    (prec : Option ℕ) : Measurable (density mesh k shape prec) := by
  let tau := match prec with | none => 0 | some n => finiteTau n
  let base := fun x : NativeSlot shape → ℝ => match prec with
    | none => sourceRoot k 0 (nativeRootCoordinate x)
    | some n => frozenRoot n k tau (nativeRootCoordinate x)
  have ht : Measurable (nativeRootCoordinate : (NativeSlot shape → ℝ) → ℝ) := measurable_pi_apply (.inl ())
  have hroot (x) : word (base x).physical = [nativeRootCoordinate x] := by cases prec <;> rfl
  have hprod : Measurable (fun x => (word (base x).physical).prod) := by simpa only [hroot,List.prod_singleton] using ht
  have hz (i : Fin d) (j : Fin 2) : Measurable (fun x : NativeSlot shape → ℝ => nativeCoordinates shape x i j) := by
    unfold nativeCoordinates
    split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const
  let code := canonicalProgram 0 1 mesh shape (fun _ _ => 0)
  have he (x : NativeSlot shape → ℝ) : nativeParent mesh k tau prec shape x =
      (realize d (base x) code (nativeCoordinates shape x)).physical :=
    congrArg TypedNode.physical (realize_eq_of_shapes (base x) _ code _ (fun _ => rfl))
  have hprod' : Measurable (fun x => (word (nativeParent mesh k tau prec shape x)).prod) := by
    simp only [he]; exact wordprod_meas hprod code hz
  exact measurable_const.div (hprod'.mul (nativeParent_measurable mesh k tau prec shape).1)

/-- The full native query mask may vary with n and may lose or gain
points. The density displacement is paid on its entire frozen support. -/
theorem all_shapes_frozen_density_L1 {d : ℕ} (hd : d ≤ 440) (mesh : ℕ)
    (k : Root) (shape : Fin d → StepShape) (lower : Bool) (atom : FloorAtom) :
    Tendsto (fun n : ℕ => ∫ x in region k shape,
      (nativeSet mesh k shape lower atom (some n)).indicator
        (fun y => |density mesh k shape none y-density mesh k shape (some n) y|) x)
      atTop (𝓝 0) := by
  let B := region k shape
  let err (n : ℕ) := (nativeSet mesh k shape lower atom (some n)).indicator
    (fun y => |density mesh k shape none y-density mesh k shape (some n) y|)
  have hB : volume B < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hrate (n : ℕ) : 0 ≤ rate n := by
    unfold rate levelError
    exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) productFloor_pos.le)
      (add_nonneg (finiteTau_pos n).le (meshError_pos n).le)) (mul_self_nonneg _)
  have hlim : Tendsto (fun n => rate n * volume.real B) atTop (𝓝 0) := by
    simpa only [zero_mul] using rate_tendsto.mul_const (volume.real B)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall (fun n => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun y _ => abs_nonneg _) x))
  · filter_upwards [eventually_fine_mesh] with n hn
    have hb (x) (hx : x ∈ B) : ‖err n x‖ ≤ rate n := by
      by_cases hg : x ∈ nativeSet mesh k shape lower atom (some n)
      · simp only [err,indicator_of_mem hg,Real.norm_eq_abs,abs_abs]
        exact frozen_admitted_density_error hx.2 hd hn hg.1
      · simpa only [err,indicator_of_notMem hg,norm_zero] using hrate n
    exact (le_abs_self _).trans (norm_setIntegral_le_of_norm_le_const hB hb)

/-- Two-sided zero extensions on precisely the same native coordinates.
Only the true changing query-set indicator remains outside the uniform
rate; both one-sided weights are bounded even when the other path fails. -/
theorem all_shapes_zero_extended_bound {d : ℕ} (hd : d ≤ 440) (mesh : ℕ)
    (k : Root) (shape : Fin d → StepShape) (lower : Bool) (atom : FloorAtom)
    {n : ℕ} (hn : meshError n ≤ 11/384) {x : NativeSlot shape → ℝ} (hx : x ∈ region k shape) :
    let I := nativeSet mesh k shape lower atom none
    let S := nativeSet mesh k shape lower atom (some n)
    |I.indicator (density mesh k shape none) x - S.indicator (density mesh k shape (some n)) x| ≤
      S.indicator (fun y => |density mesh k shape none y - density mesh k shape (some n) y|) x +
      ((I \ S) ∪ (S \ I)).indicator (fun _ => envelope) x := by
  dsimp only
  let I := nativeSet mesh k shape lower atom none
  let S := nativeSet mesh k shape lower atom (some n)
  change |I.indicator _ x-S.indicator _ x| ≤ S.indicator _ x+((I \ S)∪(S \ I)).indicator _ x
  by_cases hi : x ∈ I <;> by_cases hs : x ∈ S
  · simp [hi,hs]
  · have hw : |density mesh k shape none x| ≤ envelope := ideal_weight_bound hx.2 hd hi.1
    simpa [hi,hs] using hw
  · have hw : |density mesh k shape (some n) x| ≤ envelope := frozen_weight_bound hx.2 hd hn hs.1
    have h0 := abs_nonneg (density mesh k shape none x - density mesh k shape (some n) x)
    simp [hi,hs] <;> linarith only [hw,h0]
  · simp [hi,hs]

/-- The remaining geometric term has the ordinary volume of the exact
symmetric difference. There is no normalization by a selected subfamily. -/
theorem all_shapes_integral_bound {d : ℕ} (hd : d ≤ 440) (mesh : ℕ)
    (k : Root) (shape : Fin d → StepShape) (lower : Bool) (atom : FloorAtom)
    {n : ℕ} (hn : meshError n ≤ 11/384) :
    let B := region k shape
    let I := nativeSet mesh k shape lower atom none
    let S := nativeSet mesh k shape lower atom (some n)
    (∫ x in B, |I.indicator (density mesh k shape none) x -
        S.indicator (density mesh k shape (some n)) x|) ≤
      rate n * volume.real B + volume.real (B ∩ ((I \ S) ∪ (S \ I))) * envelope := by
  dsimp only
  let B := region k shape
  let I := nativeSet mesh k shape lower atom none
  let S := nativeSet mesh k shape lower atom (some n)
  let D := (I \ S) ∪ (S \ I)
  have hB : MeasurableSet B := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  have hfinite : volume B < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hi := nativeSet_measurable mesh k shape lower atom none
  have hs := nativeSet_measurable mesh k shape lower atom (some n)
  have hD : MeasurableSet D := (hi.diff hs).union (hs.diff hi)
  have hrate : 0 ≤ rate n := by
    unfold rate levelError
    exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) productFloor_pos.le)
      (add_nonneg (finiteTau_pos n).le (meshError_pos n).le)) (mul_self_nonneg _)
  have hconst : IntegrableOn (fun _ : NativeSlot shape → ℝ => rate n) B :=
    integrableOn_const hfinite.ne
  have hdelta : IntegrableOn (D.indicator (fun _ => envelope)) B :=
    (integrableOn_const hfinite.ne : IntegrableOn (fun _ : NativeSlot shape → ℝ => envelope) B).indicator hD
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    (hconst.add hdelta) ((ae_restrict_mem hB).mono (fun x hx => by
      have hpoint := all_shapes_zero_extended_bound hd mesh k shape lower atom hn hx
      apply hpoint.trans
      apply add_le_add_right
      by_cases hm : x ∈ S
      · rw [indicator_of_mem hm]
        exact frozen_admitted_density_error hx.2 hd hn hm.1
      · simpa only [indicator_of_notMem hm] using hrate))
  rw [integral_add hconst hdelta,setIntegral_indicator hD] at h
  simpa only [setIntegral_const,smul_eq_mul,mul_comm (volume.real B),Pi.add_apply] using h

end
end ImbalancedChen.Part5OriginalH430NativeMovingDensity

