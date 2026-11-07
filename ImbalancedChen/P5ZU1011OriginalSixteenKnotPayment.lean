import ImbalancedChen.P5ZU1011OriginalSixteenResidualWalls
import ImbalancedChen.P5ZU1011OriginalSixteenOscillation
import ImbalancedChen.AffinePrimeWallReserve

/-!
The ORIGINAL16 knot family has exactly31 cap branches: two for each
selected mask1..15, and one W branch. Each branch has151 literal boundary
walls, knots50..200. Knot50 here means ONLY R=2w, never the full R<=2w
clamp cell. Actual prime thin strips are paid before any moving tuple
mask or any range-bounded table-step replacement is chosen.

The nonlinear finite minimum uses one boundary error, independently of
the number of policies. No per-policy mean is exchanged with a minimum.
Replacement inputs are literal scalar range and off-strip lookup
agreement; no arithmetic wall-mass or final mean supplier is requested.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenKnotPayment

open Set Filter Topology
open Classical
open U11Integral U11H248 U1011OriginalSixteenPolicyBank U1011OriginalSixteenResidualWalls
open U1011OriginalSixteenOscillation U1011AdaptivePrimeError
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

noncomputable section

abbrev Branch := (Fin 15×Bool) ⊕ Unit

def branchPolicy : Branch → Policy
  | .inl (p,_) => ⟨p.val,by omega⟩
  | .inr _ => wPolicy

def branchSide : Branch → Bool
  | .inl (_,b) => b
  | .inr _ => true

theorem branch_card : Fintype.card Branch=31 := by norm_num [Branch]

/-- Every actual cap value has a branch in the deduplicated31-bank. -/
theorem exists_actual_branch (p : Policy) (v : LogFour) :
    ∃ b : Branch, branchPolicy b=p ∧ cap p v=affineCap p (branchSide b) v := by
  by_cases hp : p.val<15
  · let q : Fin 15 := ⟨p.val,hp⟩
    by_cases h : affineCap p true v≤affineCap p false v
    · refine ⟨.inl (q,true),?_,?_⟩
      · exact Fin.ext rfl
      · simpa only [cap_eq_affine_circuit,hp,if_true,min_eq_left h,branchSide]
    · refine ⟨.inl (q,false),?_,?_⟩
      · exact Fin.ext rfl
      · simpa only [cap_eq_affine_circuit,hp,if_true,min_eq_right (le_of_not_ge h),branchSide]
  · have hpW : p=wPolicy := by apply Fin.ext; dsimp [wPolicy]; omega
    refine ⟨.inr (),hpW.symm,?_⟩
    simpa only [cap_eq_affine_circuit,hp,if_false,branchSide]

def tableKnot (i : Fin 151) : Fin 201 := ⟨i.val+50,by omega⟩
abbrev Wall := Branch×Fin 151

theorem wall_card : Fintype.card Wall=31*151 := by norm_num [Wall,Branch]

def wallForm (i : Wall) : LogFour →L[ℝ] ℝ :=
  queryGate (branchPolicy i.1) (branchSide i.1) (floorGrid (tableKnot i.2).val)

def wallBound (i : Wall) : ℝ := -capOffset (branchPolicy i.1) (branchSide i.1)

def wallForms (i : Fin (Fintype.card Wall)) : LogFour →L[ℝ] ℝ :=
  wallForm ((Fintype.equivFin Wall).symm i)

def wallBounds (i : Fin (Fintype.card Wall)) : ℝ :=
  wallBound ((Fintype.equivFin Wall).symm i)

theorem wallForms_ne_zero (i : Fin (Fintype.card Wall)) : wallForms i≠0 :=
  queryGate_ne_zero _ _ _

/-- The union includes the knot50 equality boundary, not its half-space. -/
def knotStrip (delta : ℝ) : Set LogFour := primeAffineWallStrip wallForms wallBounds delta

def maskedStripMass (N : ℕ) (keep : (Fin 4→ℕ)→Prop) (delta : ℝ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
    (fun _ => (59/250:ℝ))).filter
      (fun p => keep p ∧ actualPrimeTupleLog N p∈knotStrip delta),
        ∏ i,1/((p i:ℝ)-1)

theorem maskedStripMass_le (N : ℕ) (keep : (Fin 4→ℕ)→Prop) {d delta : ℝ}
    (hd : d≤delta) :
    maskedStripMass N keep d≤actualPrimeAffineWallStripMass N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) wallForms wallBounds delta := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hkeep,hstrip⟩ := Finset.mem_filter.mp hp
    obtain ⟨j,hj⟩ := hstrip
    exact Finset.mem_filter.mpr ⟨hp,j,hj.trans hd⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Width first, then ONE target threshold, then EVERY arbitrary moving
keep mask and every narrower strip. This uses actual prime weights. -/
theorem exists_uniform_masked_strip_reserve (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ, 0<delta ∧ ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N →
      ∀ (keep : (Fin 4→ℕ)→Prop) (d : ℝ), 0≤d → d≤delta →
        maskedStripMass N keep d<epsilon := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<417/5000) (by norm_num : (417/5000:ℝ)<59/250)
    wallForms wallBounds wallForms_ne_zero epsilon he
  exact ⟨delta,hd,N0,hN0,fun N hN keep d _ hsmall =>
    (maskedStripMass_le N keep hsmall).trans_lt (hpay N hN)⟩

/-- Each actual policy/knot near equality lies in the SAME global strip;
there is no threshold or strip choice after selecting a policy/state. -/
theorem actual_gap_mem_knotStrip (p : Policy) (v : LogFour) (i : Fin 151)
    (delta : ℝ) (hnear : |typedResidual p v-floorGrid (tableKnot i).val*v 3|≤delta) :
    v∈knotStrip delta := by
  obtain ⟨b,hp,hbranch⟩ := exists_actual_branch p v
  let z : Wall := (b,i)
  refine ⟨(Fintype.equivFin Wall) z,?_⟩
  have heq : wallForm z v-wallBound z=
      typedResidual p v-floorGrid (tableKnot i).val*v 3 := by
    simp only [wallForm,wallBound,z,hp,queryGate,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,sumLinear_apply]
    simp only [typedResidual,hbranch,affineCap]
    ring
  simpa only [wallForms,wallBounds,Equiv.symm_apply_apply,heq] using hnear

def policyGap (p : Policy) (i : Fin 151) (v : LogFour) : ℝ :=
  typedResidual p v-floorGrid (tableKnot i).val*v 3

/-- Actual residual oscillation and the literal grid range [2,5]
control every policy/knot gap before any branch or atom is selected. -/
theorem policyGap_abs_sub_le (p : Policy) (i : Fin 151) (v w : LogFour) :
    |policyGap p i v-policyGap p i w|≤(15/2:ℝ)*l1Delta v w := by
  have hd := l1Delta_nonneg v w
  have hr := typedResidual_abs_sub_le p v w
  have hc := coordinate_abs_sub_le_l1Delta v w 3
  have hi : (i.val:ℝ)≤150 := by exact_mod_cast (show i.val≤150 by omega)
  have hg0 : 0≤floorGrid (tableKnot i).val := by
    simp only [floorGrid,tableKnot,Nat.cast_add,Nat.cast_ofNat]
    positivity
  have hg5 : floorGrid (tableKnot i).val≤5 := by
    simp only [floorGrid,tableKnot,Nat.cast_add,Nat.cast_ofNat]
    linarith
  have hmul : floorGrid (tableKnot i).val*|v 3-w 3|≤5*l1Delta v w :=
    mul_le_mul hg5 hc (abs_nonneg _) (by norm_num)
  unfold policyGap
  calc
    _ = |(typedResidual p v-typedResidual p w)+
        -(floorGrid (tableKnot i).val*(v 3-w 3))| := by congr 1; ring
    _ ≤ |typedResidual p v-typedResidual p w|+
        |-(floorGrid (tableKnot i).val*(v 3-w 3))| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg,abs_mul,abs_of_nonneg hg0]; linarith

theorem actual_gap_separated_of_not_strip (p : Policy) (v : LogFour) (i : Fin 151)
    (delta : ℝ) (hoff : v∉knotStrip delta) : delta<|policyGap p i v| := by
  apply lt_of_not_ge
  intro hnear
  exact hoff (actual_gap_mem_knotStrip p v i delta hnear)

def ordinaryBound : ℝ := 20000/417

/-- The replacement is a scalar table value, evaluated at the original
point and original actual residual, with arbitrary policy dependence. -/
def profileOrdinary (F : Policy→LogFour→ℝ) (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j<16 then 4*(1-F ⟨j,hj⟩ v)/residual j v else 0

def originalEnvelope (switched : LogFour→ℝ) : LogFour→ℝ :=
  envelope bank (guarded eligible switched (ordinaryKernel H248 residual))

def replacementEnvelope (F : Policy→LogFour→ℝ) (switched : LogFour→ℝ) : LogFour→ℝ :=
  envelope bank (guarded eligible switched (profileOrdinary F))

theorem profileOrdinary_bounds (F : Policy→LogFour→ℝ)
    (hF : ∀ p v,0≤F p v ∧ F p v≤1) (mask : Set (ℝ×ℝ)) (j : ℕ) (v : LogFour)
    (hv : v∈originalDomain mask) (he : eligible j v) :
    0≤profileOrdinary F j v ∧ profileOrdinary F j v≤ordinaryBound := by
  have hj : j<16 := by
    by_contra hn
    simp only [eligible,dif_neg hn] at he
  have he' : TypedEligible ⟨j,hj⟩ v := by simpa only [eligible,dif_pos hj] using he
  have hres := typedEligible_residual_gt_smallest ⟨j,hj⟩ v he'
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hr : v 3<residual j v := by simpa only [residual,dif_pos hj] using hres
  have hp : 0<residual j v := hw.trans hr
  have ha : (417/5000:ℝ)≤v 3 := hv.1
  have hval := hF ⟨j,hj⟩ v
  simp only [profileOrdinary,dif_pos hj]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hval.2)) hp.le
  · apply (div_le_iff₀ hp).2
    dsimp [ordinaryBound]
    nlinarith [hval.1]

/-- Only local scalar range and off-strip table agreement are inputs.
The same eligibility is retained, so the finite minimum pays one error. -/
theorem envelope_strip_error (F : Policy→LogFour→ℝ)
    (hF : ∀ p v,0≤F p v ∧ F p v≤1) (delta : ℝ)
    (hagree : ∀ p v,v∉knotStrip delta →
      F p v=H248 (max 2 (typedResidual p v/v 3)))
    (switched : LogFour→ℝ) (mask : Set (ℝ×ℝ)) (v : LogFour)
    (hv : v∈originalDomain mask) :
    |originalEnvelope switched v-replacementEnvelope F switched v|≤
      (knotStrip delta).indicator (fun _ => ordinaryBound) v := by
  apply guarded_envelope_abs_sub_le
  · have hn : 0≤(knotStrip delta).indicator (fun _ => ordinaryBound) v := by
      by_cases hs : v∈knotStrip delta
      · rw [indicator_of_mem hs]; norm_num [ordinaryBound]
      · simp only [indicator_of_notMem hs,le_refl]
    simpa only [sub_self,abs_zero] using hn
  · intro j hj he
    have hj16 : j<16 := Finset.mem_range.mp hj
    have ho := ordinary_actual_bounds mask j v hv he
    have hf := profileOrdinary_bounds F hF mask j v hv he
    by_cases hs : v∈knotStrip delta
    · rw [indicator_of_mem hs]
      apply abs_le.mpr
      constructor <;> dsimp [ordinaryBound] at * <;> linarith
    · rw [indicator_of_notMem hs]
      have hr : residual j v=typedResidual ⟨j,hj16⟩ v := by
        simp only [residual,dif_pos hj16]
      simp only [ordinaryKernel,profileOrdinary,dif_pos hj16,hr,
        hagree ⟨j,hj16⟩ v hs,sub_self,abs_zero,le_refl]

theorem masked_envelope_strip_error (N : ℕ) (F : Policy→LogFour→ℝ)
    (hF : ∀ p v,0≤F p v ∧ F p v≤1) (delta : ℝ)
    (hagree : ∀ p v,v∉knotStrip delta →
      F p v=H248 (max 2 (typedResidual p v/v 3)))
    (switched : LogFour→ℝ) (mask : Set (ℝ×ℝ)) (keep : (Fin 4→ℕ)→Prop)
    (hkeep : ∀ p∈actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
      (fun _ => (59/250:ℝ)),keep p → actualPrimeTupleLog N p∈originalDomain mask) :
    |maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
        (originalEnvelope switched)-
      maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
        (replacementEnvelope F switched)|≤ordinaryBound*maskedStripMass N keep delta := by
  unfold maskedTestSum maskedStripMass
  rw [←Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  by_cases hk : keep p
  · have herror := envelope_strip_error F hF delta hagree switched mask _ (hkeep p hp hk)
    simp only [hk,if_true,←mul_sub,abs_mul,abs_of_nonneg hw,true_and]
    by_cases hs : actualPrimeTupleLog N p∈knotStrip delta
    · simpa only [if_pos hs,indicator_of_mem hs,mul_comm ordinaryBound] using
        mul_le_mul_of_nonneg_left herror hw
    · simpa only [if_neg hs,indicator_of_notMem hs,mul_zero,mul_comm ordinaryBound] using
        mul_le_mul_of_nonneg_left herror hw
  · simp only [hk,if_false,false_and,sub_self,abs_zero,mul_zero,le_refl]

/-- ONE width/threshold is fixed before every moving keep mask and every
range-bounded snapped/step table profile agreeing off its narrower strip. -/
theorem exists_uniform_masked_replacement_reserve (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ (d : ℝ),0≤d → d≤delta → ∀ (F : Policy→LogFour→ℝ)
        (switched : LogFour→ℝ) (mask : Set (ℝ×ℝ)) (keep : (Fin 4→ℕ)→Prop),
        (∀ p v,0≤F p v ∧ F p v≤1) →
        (∀ p v,v∉knotStrip d → F p v=H248 (max 2 (typedResidual p v/v 3))) →
        (∀ p∈actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
          (fun _ => (59/250:ℝ)),keep p → actualPrimeTupleLog N p∈originalDomain mask) →
        |maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
            (originalEnvelope switched)-
          maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
            (replacementEnvelope F switched)|<epsilon := by
  have hB : 0<ordinaryBound+1 := by norm_num [ordinaryBound]
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_uniform_masked_strip_reserve
    (epsilon/(ordinaryBound+1)) (div_pos he hB)
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN d hd0 hsmall F switched mask keep hF hagree hkeep
  have hmass := hpay N hN keep d hd0 hsmall
  have hmass0 : 0≤maskedStripMass N keep d := by
    apply Finset.sum_nonneg
    intro p hp
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  have hstrict := mul_lt_mul_of_pos_left hmass hB
  have hcancel : (ordinaryBound+1)*(epsilon/(ordinaryBound+1))=epsilon := by
    field_simp [hB.ne']
  rw [hcancel] at hstrict
  exact (masked_envelope_strip_error N F hF d hagree switched mask keep hkeep).trans_lt
    ((mul_le_mul_of_nonneg_right (show ordinaryBound≤ordinaryBound+1 by linarith) hmass0).trans_lt hstrict)

end

end ImbalancedChen.P5Z.U1011OriginalSixteenKnotPayment
