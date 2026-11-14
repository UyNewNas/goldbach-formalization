import ImbalancedChen.P5OriginalWRealEndpointCapacities
import ImbalancedChen.P5SelectedRealEndpointSupport
import ImbalancedChen.Part3ActualWResidualCompletion

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- The W16 tuplewise natural completion does not fix its partition on a
-- WHOLE atom. This source instead runs the same original W algorithm on
-- real upper endpoint occurrences, once per box and medium HB length.
namespace ImbalancedChen.P5Z.OriginalWWholeBoxRealRun
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalNearCapRealEndpointGeometry OriginalWRealEndpointCapacities
open SelectedRealEndpointSupport
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

abbrev Occ (r : ℕ) := Fin 4 ⊕ Fin r

def wWeight {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (i : Occ r) : ℝ :=
  (N : ℝ) ^ exponent u v i

def wSeed {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (A : ℝ) : Bins (Occ r) :=
  if wWeight N u v (Sum.inl 1) ≤ A then
    ⟨[Sum.inl 1], [Sum.inl 0], []⟩
  else
    ⟨[], [Sum.inl 0], [Sum.inl 1]⟩

def wInput (r : ℕ) : List (Occ r) :=
  [Sum.inl 2, Sum.inl 3] ++ (List.finRange r).map Sum.inr

def wGroups {r : ℕ} (N : ℕ) (B : Box) (eta : ℚ)
    (u : LogFour) (v : Fin r → ℝ) (A : ℝ) : Bins (Occ r) :=
  complete (wWeight N u v) A (middleCapacity B eta N)
    (rightCapacity B eta N A) (wSeed N u v A) (wInput r)

theorem wSeed_total {r N : ℕ} (u : LogFour) (v : Fin r → ℝ) (A : ℝ) :
    total (wWeight N u v) (wSeed N u v A) =
      wp (wWeight N u v) [Sum.inl 0, Sum.inl 1] := by
  unfold wSeed
  split_ifs <;> simp [total,wp,wWeight] <;> ring

theorem wSeed_bounded {r N : ℕ} (hN : 1 < N) (B : Box) (eta : ℚ)
    (u : LogFour) (v : Fin r → ℝ) (A : ℝ)
    (hA : 1 ≤ A)
    (hfirst : wWeight N u v (Sum.inl 0) ≤ middleCapacity B eta N)
    (hsecond : wWeight N u v (Sum.inl 1) ^ 2 ≤ A * rightCapacity B eta N A)
    (hC : 1 ≤ rightCapacity B eta N A) :
    Bounded (wWeight N u v) A (middleCapacity B eta N)
      (rightCapacity B eta N A) (wSeed N u v A) := by
  have hwpos : 0 < wWeight N u v (Sum.inl 1) := by
    unfold wWeight
    exact Real.rpow_pos_of_pos (by exact_mod_cast (zero_lt_one.trans hN)) _
  unfold wSeed
  split_ifs with hfit
  · simpa [Bounded,wp] using (show
      wWeight N u v (Sum.inl 1) ≤ A ∧
      wWeight N u v (Sum.inl 0) ≤ middleCapacity B eta N ∧
      1 ≤ rightCapacity B eta N A from ⟨hfit,hfirst,hC⟩)
  · have hright := (append_fits_one_box hA hC hsecond).resolve_left hfit
    simpa [Bounded,wp] using (show
      1 ≤ A ∧ wWeight N u v (Sum.inl 0) ≤ middleCapacity B eta N ∧
      wWeight N u v (Sum.inl 1) ≤ rightCapacity B eta N A from
      ⟨hA,hfirst,hright⟩)

theorem wSeed_positive {r N : ℕ} (hN : 1 < N) (u : LogFour)
    (v : Fin r → ℝ) (A : ℝ) :
    Positive (wWeight N u v) (wSeed N u v A) := by
  have hw (i : Occ r) : 0 < wWeight N u v i :=
    Real.rpow_pos_of_pos (by exact_mod_cast (zero_lt_one.trans hN)) _
  unfold wSeed
  split_ifs <;> simp [Positive,wp,hw]

-- The full W square and residual budget come from the genuine padded
-- WHOLE-box certificate; the rough word retains its original even cubes.
theorem fixed_W_real_endpoint_run {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0) (hu32 : u 3 ≤ u 2)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hvlate : ∀ i, v i ≤ u 2) (roughWidth : ℝ)
    (hrw : roughWidth ≤ (delta wPolicy B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → PresievedRoughSlotAffineGates.cube v i <
      (physicalResidual wPolicy B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let out := wGroups N B eta u v A
    Trace (wSeed N u v A) (wInput r) out ∧
      total (wWeight N u v) out =
        wp (wWeight N u v) (wholeLabels r) ∧
      (Bounded (wWeight N u v) A (middleCapacity B eta N)
          (rightCapacity B eta N A) out ∨
        (middleCapacity B eta N < wp (wWeight N u v) out.middle ∧
          wp (wWeight N u v) out.middle ≤
            middleCapacity B eta N * (N : ℝ) ^ (u 2) ∧
          wp (wWeight N u v) out.left ≤ A ∧
          wp (wWeight N u v) out.right ≤
            runCapacity B eta N / (A * wp (wWeight N u v) out.middle))) := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hd : 0 < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  let level := (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)
  let ell := (physicalResidual wPolicy B eta : ℝ) + roughWidth
  let w := wWeight N u v
  let initial := wSeed N u v A
  let input := wInput r
  have hr := actual_padded_endpoint_reserves wPolicy B eta hv hw hc heta u hlo hhi hrw
  have hfull : ∀ i : Fin 4, fullSquare i u ≤ level := by
    intro i
    dsimp [level]
    linarith [hr.2.1 i]
  have hbudget : (∑ i : Fin 4, u i) + ell ≤ level := by
    dsimp [ell,level]
    linarith [hr.2.2.1]
  have hnone (i : Fin 4) : ¬Selected wPolicy i := by
    simp [Selected,wPolicy]
  have hselected : ∀ i : Fin 4, ¬Selected wPolicy i →
      selectedSquare wPolicy i u ≤ level := by
    intro i _
    simpa [selectedSquare,selectedMass,hnone,fullSquare] using hfull i
  have hwhole := (original_endpoint_append_support hN wPolicy u v level ell
    hfull hselected hv0 hvanti hcubes hbudget).1
  have hwhole' : PrefixSquareBound w (runCapacity B eta N) (wholeLabels r) := by
    simpa only [w,wWeight,runCapacity,level] using hwhole
  obtain ⟨hB,hC,hcap,hfirst,hsecond,_⟩ :=
    actual_W_real_capacity_inputs hN B eta hv hw hc heta u hlo hhi hu2 hu10
      A hA hAupper (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith : (0 : ℝ) ≤ (delta wPolicy B eta : ℝ) / 64)
  have hinit := wSeed_bounded hN B eta u v A hA hfirst hsecond hC
  have hpositive := wSeed_positive hN u v A
  have hslots : ∀ q ∈ input, 0 < w q ∧ w q ≤ (N : ℝ) ^ (u 2) := by
    intro q hq
    change q ∈ [Sum.inl 2, Sum.inl 3] ++ (List.finRange r).map Sum.inr at hq
    have hpos : 0 < w q := Real.rpow_pos_of_pos hNpos _
    have hexp : exponent u v q ≤ u 2 := by
      rcases List.mem_append.mp hq with hs | ht
      · simp only [List.mem_cons,List.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact le_refl _
        · exact hu32
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
        exact hvlate i
    exact ⟨hpos,Real.rpow_le_rpow_of_exponent_le hNreal.le hexp⟩
  have hseed := wSeed_total (N:=N) u v A
  have hsupport : PrefixSquareBound w (runCapacity B eta N)
      ([Sum.inl 0, Sum.inl 1] ++ input) := by
    simpa only [input,wInput,wholeLabels,front,List.append_assoc] using hwhole'
  have hout := complete_correct w (zero_lt_one.trans_le hA) hinit hpositive
    hslots hseed hsupport
  simpa [wGroups,wholeLabels,front,wInput,w,input,initial] using hout

theorem wSeed_total_any {r N : ℕ} (u : LogFour) (v : Fin r → ℝ)
    (A : ℝ) (f : Occ r → ℝ) :
    total f (wSeed N u v A) = wp f [Sum.inl 0, Sum.inl 1] := by
  unfold wSeed
  split_ifs <;> simp [total,wp] <;> ring

/-- The real endpoint run is frozen before this arbitrary positive tuple.
Its structural trace preserves the literal original occurrence product, and
each actual group is bounded by its precomputed whole-box endpoint product. -/
theorem fixed_W_real_groups_all_tuples {r N : ℕ} (B : Box) (eta : ℚ)
    (u : LogFour) (v : Fin r → ℝ) (A : ℝ)
    (htrace : Trace (wSeed N u v A) (wInput r)
      (wGroups N B eta u v A))
    (actual : Occ r → ℕ) (hactualPos : ∀ i, 0 < actual i)
    (hsize : ∀ i, (actual i : ℝ) ≤ wWeight N u v i)
    (e : ℕ) (hepos : 0 < e) :
    let out := wGroups N B eta u v A
    let a := (out.left.map actual).prod
    let b := (out.middle.map actual).prod
    let c := e * (out.right.map actual).prod
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
      a * b * c = e * ((wholeLabels r).map actual).prod ∧
      (a : ℝ) ≤ wp (wWeight N u v) out.left ∧
      (b : ℝ) ≤ wp (wWeight N u v) out.middle ∧
      (c : ℝ) ≤ (e : ℝ) * wp (wWeight N u v) out.right := by
  let out := wGroups N B eta u v A
  let a := (out.left.map actual).prod
  let b := (out.middle.map actual).prod
  let c₀ := (out.right.map actual).prod
  let c := e * c₀
  have hp (l : List (Occ r)) : 0 < (l.map actual).prod := by
    apply List.prod_pos
    intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    exact hactualPos i
  have haPos : 1 ≤ a := by
    have h := hp out.left
    change 1 ≤ (out.left.map actual).prod
    omega
  have hbPos : 1 ≤ b := by
    have h := hp out.middle
    change 1 ≤ (out.middle.map actual).prod
    omega
  have hcPos : 1 ≤ c := by
    have h := Nat.mul_pos hepos (hp out.right)
    change 1 ≤ e * (out.right.map actual).prod
    omega
  have hseed := wSeed_total_any (N:=N) u v A (fun i => (actual i : ℝ))
  have hreal := htrace.product (fun i => (actual i : ℝ))
  rw [hseed] at hreal
  have hprod : a * b * c = e * ((wholeLabels r).map actual).prod := by
    have heq : a * b * c₀ = ((wholeLabels r).map actual).prod := by
      have hcast : ((a * b * c₀ : ℕ) : ℝ) =
          (((wholeLabels r).map actual).prod : ℝ) := by
        simpa [out,a,b,c₀,total,wp,actualNatList_cast_prod,
          wholeLabels,front,wInput,List.append_assoc,Nat.cast_mul] using hreal
      exact_mod_cast hcast
    dsimp [c]
    rw [← heq]
    ring
  have hbound (l : List (Occ r)) :
      ((l.map actual).prod : ℝ) ≤ wp (wWeight N u v) l := by
    rw [← actualNatList_cast_prod]
    simpa only [wp,List.map_map,Function.comp_def] using
      List.prod_map_le_prod_map₀ (fun i => (actual i : ℝ))
        (wWeight N u v) (fun i hi => Nat.cast_nonneg _) (fun i hi => hsize i)
  have ha : (a : ℝ) ≤ wp (wWeight N u v) out.left := hbound out.left
  have hb : (b : ℝ) ≤ wp (wWeight N u v) out.middle := hbound out.middle
  have hc : (c : ℝ) ≤ (e : ℝ) * wp (wWeight N u v) out.right := by
    change ((e * c₀ : ℕ) : ℝ) ≤ (e : ℝ) * wp (wWeight N u v) out.right
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (hbound out.right) (Nat.cast_nonneg _)
  exact ⟨haPos,hbPos,hcPos,hprod,ha,hb,hc⟩

end
end ImbalancedChen.P5Z.OriginalWWholeBoxRealRun
