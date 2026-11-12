import ImbalancedChen.Part5OriginalH430ChildSmoothPrimeTests
import ImbalancedChen.Part5OriginalH430RefinedFeedbackBudget

/-! A child-labelled estimate on the STRICT original selected Buchstab carrier.
Reuse its original finite prefix deletion and strict equality-fibre charge.
The pre-N budget sums absolute errors over the native labels and original
atoms with their actual immutable predecessor. Source only. -/
namespace ImbalancedChen.Part5OriginalH430StrictChildBuchstab
noncomputable section
open Set Filter MeasureTheory Wu2008DoubleSieve
open scoped Classical BigOperators Topology Pointwise
open Part5OriginalCausalSmoothAtlas Part5OriginalH430ChildSmoothPrimeTests
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactThetaMass P2OriginalPrefixMaskMass P2OriginalHalfOpenProfileCarrier
open P2OriginalPhysicalOldProfileMass P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission Part5OriginalH430BuchstabCeilingDictionary
open Part5OriginalH430BuchstabCeilingPayment Part5OriginalBuchstabActualRowLimits
open Part5OriginalH430BuchstabPhysicalBudget Part5OriginalBuchstabCompactAtoms
open Part5OriginalBuchstabTrueAtomLimits Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalUpsilon5CausalDictionary
open Part5UpperTables P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open P2Selected430CausalOccurrenceExporter Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedNonbankSupply
open Part5OriginalH430RefinedFeedbackBudget

abbrev I (P : Plan) := FloorAtom × Box P 1

def phys (N : ℕ) (L : ℝ) (q : ℕ) : Coord 1 := L • primeCoord N L q

theorem phys_eq (N q : ℕ) {L : ℝ} (hL : L ≠ 0) : phys N L q = fun _ => physicalPrime N q := by
  unfold phys primeCoord normalizedLog
  rw [smul_smul,mul_inv_cancel₀ hL,one_smul]
  rfl

def childIntegral (P : Plan) (up : Bool) (L c : ℝ) (i : I P) : ℝ :=
  ∫ x in atomDomain up i.1 c, childTest P i.2 L residualSingle x * ∏ a, 1/x a

def masked (P : Plan) (N d : ℕ) (up : Bool) (L c : ℝ) (i : I P) : ℝ :=
  ∑ q ∈ primeWindow (d*N) ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5)),
    localPrimeFactor d q * (atomDomain up i.1 c).indicator
      (childTest P i.2 L residualSingle) (primeCoord N L q)

theorem masked_limit (P : Plan) (up : Bool) (i : I P) {F G e : ℝ}
    (hF : 0 < F) (hG : F ≤ G) (he : 0 < e) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc F G, ∀ c ∈ Icc (1:ℝ) 6,
      ∀ d : ℕ, 0 < d → d ≤ N → |masked P N d up L c i - childIntegral P up L c i| < e := by
  obtain ⟨T₁,h₁⟩ := buchstab_child_limit P (up,i.1,i.2) hF hG (by positivity : 0 < e/2)
  obtain ⟨T₂,h₂⟩ := compact_uniform_prefixMask_difference (a := F/10) (by positivity)
    (by norm_num : (0:ℝ) ≤ 10) (by positivity : 0 < e/2)
  refine ⟨max 2 (max T₁ T₂),?_⟩
  intro N hN L hL c hc d hd hdN
  let D := atomDomain up i.1 c
  let f := childTest P i.2 L residualSingle
  have hb (x : Coord 1) : |f x| ≤ 10 := childTest_bound P i.2 L residualSingle
    (fun v => by rw [abs_of_nonneg (residualSingle_bounds v).1]; exact (residualSingle_bounds v).2) x
  have ha := h₂ N (by omega) d hd hdN _ _ (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (show F/10 ≤ L/10 by linarith [hL.1]))
    (fun q => D.indicator f (primeCoord N L q)) (fun q _ => indicator_abs_bound D f (by norm_num) hb _)
  rw [← trueSingleTest_eq_window N L d D f] at ha
  change |masked P N d up L c i - trueSingleTest N L d D f| < e/2 at ha
  have hb' := h₁ N (by omega) L hL c hc d
  change |trueSingleTest N L d D f - childIntegral P up L c i| < e/2 at hb'
  linarith [abs_sub_le (masked P N d up L c i) (trueSingleTest N L d D f) (childIntegral P up L c i)]

def onAtom (P : Plan) (N : ℕ) (Q : ℝ) (old : List ℕ) (up : Bool) (i : I P)
    (q : Fin (N+1)) : ℝ :=
  if P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up i.1
    then atom P i.2 (phys N (physicalLevel N Q old) q.val) else 0

def actual (P : Plan) (N : ℕ) (Q : ℝ) (old : List ℕ) (up : Bool) (i : I P)
    (S : Finset (Fin (N+1))) : ℝ :=
  ∑ q ∈ S, thetaAtom N Q (parentProduct old*q.val) * onAtom P N Q old up i q

theorem closed_exact (P : Plan) (i : I P) {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hg : directionGuard up p) (hA : 4 ≤ (N:ℝ)^(physicalLevel N Q old/10)) :
    actual P N Q old up i (closedChildren up N old p) =
    thetaAtom N Q (parentProduct old) *
       masked P N (parentProduct old) up (physicalLevel N Q old) (physicalStart up p) i := by
  let L := physicalLevel N Q old
  let d := parentProduct old
  let c := physicalStart up p
  let D := atomDomain up i.1 c
  let B (q : Fin (N+1)) := P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up i.1
  let S := primeWindow (d*N) ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5))
  calc
    _ = ∑ q ∈ (closedChildren up N old p).filter B,
        thetaAtom N Q (d*q.val)*atom P i.2 (phys N L q.val) := by
      rw [Finset.sum_filter]; unfold actual; apply Finset.sum_congr rfl; intro q _
      change thetaAtom N Q (d*q.val)*(if B q then atom P i.2 (phys N L q.val) else 0) = _
      by_cases h : B q <;> simp only [h,if_true,if_false,mul_zero]
    _ = ∑ q ∈ S.filter (fun q => primeCoord N L q ∈ D),
        thetaAtom N Q d*(localPrimeFactor d q *
          childTest P i.2 L residualSingle (primeCoord N L q)) := by
      refine Finset.sum_bij (fun q _ => q.val) ?_ ?_ ?_ ?_
      · intro q hq
        obtain ⟨hq,hb⟩ := Finset.mem_filter.mp hq
        obtain ⟨hp,hl⟩ := mem_closedChildren.mp hq
        exact Finset.mem_filter.mpr ⟨local_mem_primeWindow hw hp.1 hp.2 hL hl,
          (natural_atom_iff hw hp.1 hL hC hg i.1).mpr ⟨hl,hb⟩⟩
      · intro q _ r _ he; exact Fin.ext he
      · intro q hq
        obtain ⟨hwq,hx⟩ := Finset.mem_filter.mp hq
        have hp := (mem_primeWindow.mp hwq).1
        obtain ⟨hl,hb⟩ := (natural_atom_iff hw hp hL hC hg i.1).mp hx
        let r : Fin (N+1) := ⟨q,by have h := local_prime_le_target hw hL hl; omega⟩
        exact ⟨r,Finset.mem_filter.mpr ⟨mem_closedChildren.mpr ⟨⟨hp,by
          simpa only [Nat.mul_comm] using (mem_primeWindow.mp hwq).2.1⟩,hl⟩,hb⟩,rfl⟩
      · intro q hq
        have hh := (Finset.mem_filter.mp hq).1
        obtain ⟨hp,hl⟩ := mem_closedChildren.mp hh
        have hq4 := hA.trans (mem_primeWindow.mp (local_mem_primeWindow hw hp.1 hp.2 hL hl)).2.2.1
        have hq2 : 2 < q.val := by exact_mod_cast (show (2:ℝ) < q.val by linarith)
        have hθ := thetaAtom_single (by omega) hw.2.1 hp.1 hq2
          (Nat.coprime_mul_iff_right.mp hp.2).1 (parentWindow_logs hw).2.1
        change thetaAtom N Q (d*q.val) = thetaAtom N Q d *
          (localPrimeFactor d q.val/(1-relativePrime Q old q.val)) at hθ
        have hu := relativePrime_le_half hw hL hh
        rw [← primeCoord_eq_relative hw] at hu hθ
        rw [hθ]
        simp only [childTest,phys,residualSingle,max_eq_right (show (1/10:ℝ) ≤ 1 -
          primeCoord N L q.val 0 by linarith)]
        ring
    _ = _ := by
      rw [Finset.sum_filter,masked,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      by_cases h : primeCoord N L q ∈ D
      · simp only [if_pos h,Set.indicator_of_mem h]
      · simp only [if_neg h,Set.indicator_of_notMem h,mul_zero]

theorem strict_limit (P : Plan) (up : Bool) (i : I P) {F e : ℝ}
    (hF : 0 < F) (he : 0 < e) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → directionGuard up p → 1 ≤ p.argument →
      F ≤ physicalLevel N Q old →
      |actual P N Q old up i (singleChildren (.buchstab up p.argument) N Q old chi) -
        thetaAtom N Q (parentProduct old)*childIntegral P up (physicalLevel N Q old)
          (physicalStart up p) i| ≤ e*thetaAtom N Q (parentProduct old) := by
  let G := max F 1
  let A := max 4 (8/e)
  obtain ⟨Tm,hm⟩ := masked_limit P up i hF (show F ≤ G from le_max_left _ _) (by positivity : 0 < e/2)
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k := 1) hF (show F ≤ G from le_max_left _ _)
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
  obtain ⟨Tc,hc⟩ := exists_uniform_primeFloor hF (show 4 ≤ A from le_max_left _ _)
  refine ⟨max 4 (max Tm (max Ta Tc)),by omega,?_⟩
  intro N hN Q chi old p hw hL hC hg hs hFL
  let L := physicalLevel N Q old
  let c := physicalStart up p
  let d := parentProduct old
  let θ := thetaAtom N Q d
  let Ac := actual P N Q old up i (closedChildren up N old p)
  let As := actual P N Q old up i (singleChildren (.buchstab up p.argument) N Q old chi)
  have h4 : 4 ≤ N := by omega
  have hLG : L ∈ Icc F G := ⟨hFL,(parent_level_le_one hw).trans (le_max_right _ _)⟩
  have hc1 : 1 ≤ c := physicalStart_ge_one hg
  have hd := prefix_le_target_of_commonQ hw.2.1 (parentWindow_logs hw).2.1 hw.2.2.2.1
  have hθ : 0 ≤ θ := thetaAtom_nonneg h4 hw.2.1 (parentWindow_logs hw).2.1
  have hmask := hm N (by omega) L hLG (min c 6) ⟨le_min hc1 (by norm_num),min_le_right _ _⟩ d hw.2.1 hd
  have hmask' : |masked P N d up L c i-childIntegral P up L c i| < e/2 := by
    simpa only [masked,childIntegral,capped_atomDomain hc1] using hmask
  have hclosed : |Ac - θ*childIntegral P up L c i| ≤ θ*(e/2) := by
    dsimp only [Ac]
    rw [closed_exact P i hw hL hC hg (ha N (by omega) L hLG).1]
    change |θ * masked P N d up L c i - θ * childIntegral P up L c i| ≤ _
    rw [← mul_sub,abs_mul,abs_of_nonneg hθ]
    exact mul_le_mul_of_nonneg_left hmask'.le hθ
  have hceil := signed_ceiling_error_le (up := up) h4 hw hL hC hs (show 4 ≤ A from le_max_left _ _)
    ((hc N (by omega)).2 Q old hFL) (by norm_num : (0:ℝ) ≤ 1) (onAtom P N Q old up i)
    (fun q _ => by unfold onAtom; split_ifs <;> first
      | rw [abs_of_nonneg (atom_nonneg _ _ _)]; exact atom_le_one _ _ _
      | norm_num)
  have hAo : 0 < A := lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (le_max_left _ _)
  have hfrac : 4/A ≤ e/2 := by
    apply (div_le_iff₀ hAo).mpr
    have hl : 8 ≤ A*e := (div_le_iff₀ he).mp (le_max_right (4:ℝ) (8/e))
    nlinarith
  change |Ac-As| ≤ 1*((4/A)*θ) at hceil
  have hsc : |As-Ac| ≤ (e/2)*θ := by
    rw [abs_sub_comm]
    exact (by simpa only [one_mul] using hceil : |Ac-As| ≤ (4/A)*θ).trans
      (mul_le_mul_of_nonneg_right hfrac hθ)
  change |As-θ*childIntegral P up L c i| ≤ e*θ
  calc
    _ ≤ |As-Ac| + |Ac-θ*childIntegral P up L c i| := abs_sub_le _ _ _
    _ ≤ (e/2)*θ+θ*(e/2) := add_le_add hsc hclosed
    _ = _ := by ring

/-- Include the immutable predecessor coefficient BEFORE taking the global
label budget. A single pre-N bound, uniform in all emitted parents. -/
def activeRow (up : Bool) (b : FloorAtom) : RowAtom := if up then .inr b else .inl b

def StrictAt (T : ℕ) (P : Plan) (delta : ℝ) : Prop :=
    ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ r : Request, ∀ g : Fin 430,
      ∀ k : Fin 200, Coherent N Q r → Selected g.val r k .buchstab →
      frozenResidualFloor ≤ physicalLevel N Q r.old →
      let up := r.node.upper
      let p := r.node.physical
      let θ := thetaAtom N Q (parentProduct r.old)
      (∑ i : I P, |actual P N Q r.old up i
          (singleChildren (.buchstab up p.argument) N Q r.old p.ceiling) -
        θ*childIntegral P up (physicalLevel N Q r.old) (physicalStart up p) i| *
          |oldAtomValue (precedingH g) (precedingh g) (activeRow up i.1)|) ≤ delta*θ

theorem all_strict_requested (P : Plan) {delta : ℝ} (hd : 0 < delta) :
    ∃ T : ℕ, 4 ≤ T ∧ StrictAt T P delta := by
  let C := immutable430AtomL1+1
  let M : ℝ := Fintype.card (I P)
  have hC : 0 < C := by dsimp [C]; linarith [immutable430AtomL1_nonneg]
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let e := delta/((M+1)*C)
  have he : 0 < e := div_pos hd (mul_pos (by linarith) hC)
  have H (ti : Bool × I P) := strict_limit P ti.1 ti.2 Part5OriginalH430FrozenIntegerSupport.frozenResidualFloor_pos he
  choose t ht4 ht using H
  let T := 4 + ∑ ti : Bool × I P, t ti
  refine ⟨T,by dsimp [T]; omega,?_⟩
  intro N hN Q r g k hco hsel hF
  dsimp only
  let θ := thetaAtom N Q (parentProduct r.old)
  have hw := coherent_window hco
  have hN4 : 4 ≤ N := by dsimp [T] at hN; omega
  have hθ : 0 ≤ θ := thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hbounded (b : RowAtom) : |oldAtomValue (precedingH g) (precedingh g) b| ≤ C :=
    (Finset.single_le_sum (fun b _ => abs_nonneg (oldAtomValue (precedingH g) (precedingh g) b))
      (Finset.mem_univ b)).trans ((preceding_oldAtomL1_le g).trans (by dsimp [C]; linarith))
  calc
    _ ≤ ∑ _i : I P, (e*θ)*C := by
      apply Finset.sum_le_sum; intro i _
      have htN : t (r.node.upper,i) ≤ N := by
        have hh := Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (r.node.upper,i))
        dsimp [T] at hN; omega
      have hh := ht (r.node.upper,i) N htN Q _ r.old r.node.physical hw (coherent_residual hco) rfl
        (requested_buchstab_guard hco hsel)
        ((by norm_num : (1:ℝ) ≤ 2).trans (Part5OriginalH430RequestedReads.selected_buchstab_guard hco.read_valid hsel)) hF
      exact mul_le_mul hh (hbounded _) (abs_nonneg _) (mul_nonneg he.le hθ)
    _ = (M*e*C)*θ := by simp [M,nsmul_eq_mul] <;> ring
    _ ≤ ((M+1)*e*C)*θ := by
      apply mul_le_mul_of_nonneg_right _ hθ
      apply mul_le_mul_of_nonneg_right _ hC.le
      exact mul_le_mul_of_nonneg_right (by linarith) he.le
    _ = delta*θ := by dsimp [e]; field_simp [hC.ne',show M+1 ≠ 0 by linarith]

/-- No T is supplied by the caller. The fixed precision/name of the chart
is shared by actual feedback parent marks and strict Buchstab future slots,
and both estimates now hold beyond a SINGLE constructed arithmetic threshold. -/
theorem reserve_common {reserve deltaMax : ℝ} (hr : 0 < reserve) (hd : 0 < deltaMax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < deltaMax ∧
      (7/2:ℝ)*(delta*(((12:ℝ)^441-1)/11)) < reserve ∧
      ∃ m : ℕ, (∀ (j : Code (.mesh m)) (x y : ℝ),
        mask (.mesh m) j x ≠ 0 → mask (.mesh m) j y ≠ 0 → |x-y| < delta) ∧
        ∃ T : ℕ, 4 ≤ T ∧ FeedbackAt T delta ∧ StrictAt T (.mesh m) delta := by
  obtain ⟨δ,hδ,hmax,hbudget,m,hm,Tp,hTp,hp⟩ := reserve_mesh_feedback hr hd
  obtain ⟨Tc,_,hc⟩ := all_strict_requested (.mesh m) hδ
  refine ⟨δ,hδ,hmax,hbudget,m,hm,max Tp Tc,hTp.trans (le_max_left _ _),?_,?_⟩
  · intro N hN; exact hp N ((le_max_left _ _).trans hN)
  · intro N hN; exact hc N ((le_max_right _ _).trans hN)

end
end ImbalancedChen.Part5OriginalH430StrictChildBuchstab
