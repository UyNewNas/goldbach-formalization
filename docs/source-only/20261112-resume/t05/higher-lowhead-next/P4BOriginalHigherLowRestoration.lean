import ImbalancedChen.P4BOriginalHigherLowNativeAtoms

namespace ImbalancedChen.P4BOriginalHigherLowRestoration
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionThirdFactor (master admissible_words)
open P4BOriginalHigherLowBins (Groups split split_perm)
open P4BOriginalHigherLowTensor (restore)
open P4BOriginalHigherLowNativeAtoms (groups firstSet secondSet thirdSet)
open P4BOriginalMediumAtomFamily (Index support support_data third_data)
open P4BOriginalMediumSignedFibre (scalar)
open P4BOriginalMediumPhysicalAtomSum (onWord)
open P4BOriginalMediumRestoringBudget (scalar_cost)
open P5Z.HBRightClosedDyadicRoles (Block bank bank_card owner owner_mem_bank)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos log2_count_le)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalHighRankComplementBlocks (cap exists_scheduled_split_mass)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BArbitraryWidthUpperBlockGeometry (countingScale target_le_countingScale)
open P4BOuterRampRoughness (baseline)
open P4AHeldTaggedCompilerSupport (J0)

def pieces {o : ℕ} {z k0 : ℝ} (I : Index o z k0) :=
  ((firstSet I).image owner).card*((secondSet I).image owner).card*((thirdSet I).image owner).card

private theorem supported (P : Params) (S : List ℕ) {q} (hq : q∈support P S) : q≤P.N^S.length := by
  obtain ⟨ps,hp,rfl⟩ := Finset.mem_image.mp hq
  have H := actualPrimeSlotBox_prod_le_upper _ (fun _ : ℕ => P.N) S (fun _ _ p h =>
    (mem_roughPrimeFinset.mp (Finset.mem_inter.mp h).2).1.le) ps hp
  have prod (l : List ℕ) : (l.map (fun _ => P.N)).prod=P.N^l.length := by
    induction l with
    | nil => simp
    | cons i l ih => simp only [List.map_cons,List.prod_cons,ih,List.length_cons,pow_succ']
  exact H.trans_eq (prod S)

variable {o : ℕ} {z k0 : ℝ} (I : Index o z k0)
theorem factor_and_boxes (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega) (hell : I.P.ell≤1) :
    let k := J0 I.P.omega
    |restore I.P I.J (groups I)|≤(k.factorial:ℝ)^3 ∧
      (pieces I:ℝ)≤(dyadicConstant*((k:ℝ)+2)*logScale (I.P.N:ℝ))^3 := by
  let P := I.P
  let S := groups I
  let k := J0 P.omega
  have part := (split_perm P I.x I.U I.eta I.word).length_eq
  change (S.1++(S.2.1++S.2.2)).length=I.J.length at part
  simp only [List.length_append] at part
  have hr := P.rank_cap I.word hN he ho
  have a1 : S.1.length≤k := by dsimp only [k]; omega
  have a2 : S.2.1.length≤k := by dsimp only [k]; omega
  have a3 : S.2.2.length≤k := by dsimp only [k]; omega
  have fa (u : ℕ) (h : u≤k) : (u.factorial:ℝ)≤(k.factorial:ℝ) := by exact_mod_cast Nat.factorial_le h
  have m1 : |restore P I.J S|≤(k.factorial:ℝ)^3 := by
    simp only [restore,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _≤1*(k.factorial:ℝ)*k.factorial*k.factorial := by
        exact mul_le_mul (mul_le_mul (mul_le_mul (P4BOriginalCollisionTensor.scalar_bound P I.J)
          (fa _ a1) (Nat.cast_nonneg _) zero_le_one) (fa _ a2)
          (Nat.cast_nonneg _) (by positivity)) (fa _ a3) (Nat.cast_nonneg _) (by positivity)
      _=_ := by ring
  let R := P.N^(k+1)
  have hb3 (q) (hq : q∈thirdSet I) : q≤R := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    have hNZ := (Finset.mem_filter.mp ha).2
    have ha' : (a:ℝ)<P.L := by
      unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta at hNZ
      split_ifs at hNZ
      · exact (actualSmallRosserPlus_active hNZ).2.1
      · exact (actualSmallRosserMinus_active hNZ).2.1
    have hL : P.L≤(P.N:ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le : 1≤(P.N:ℝ)) hell
    simpa only [R,pow_succ'] using Nat.mul_le_mul (Nat.cast_le.mp (ha'.le.trans hL))
      ((supported P S.2.2 hb).trans (Nat.pow_le_pow_right (by omega) a3))
  have card (T : Finset ℕ) (h : ∀n∈T,0<n ∧ n≤R) : (T.image owner).card≤(bank R).card :=
    Finset.card_le_card (fun _ hB => by obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hB; exact owner_mem_bank (h u hu).1 (h u hu).2)
  have c1 := card (firstSet I) (fun u h => ⟨(support_data _ _ h).1,
    (supported P S.1 h).trans (Nat.pow_le_pow_right (by omega) (by omega : S.1.length≤k+1))⟩)
  have c2 := card (secondSet I) (fun u h => ⟨(support_data _ _ h).1,
    (supported P S.2.1 h).trans (Nat.pow_le_pow_right (by omega) (by omega : S.2.1.length≤k+1))⟩)
  have c3 := card (thirdSet I) (fun u h => ⟨(third_data _ _ _ h).1,hb3 u h⟩)
  have cb : pieces I≤(bank R).card^3 := by
    simpa only [pieces,pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul c1 c2) c3
  have hn : (1:ℝ)≤P.N := by exact_mod_cast hN.le
  have hnp := zero_lt_one.trans_le hn
  have R1 : (1:ℝ)≤R := by dsimp only [R]; rw [Nat.cast_pow]; exact one_le_pow₀ hn
  have hR : ((R-1:ℕ):ℝ)≤(R:ℝ) := by exact_mod_cast Nat.sub_le R 1
  have hcard : ((bank R).card:ℝ)≤dyadicConstant*logScale (R:ℝ) := by
    rw [bank_card]; exact log2_count_le R1 _ (by linarith)
  have hlog : logScale (R:ℝ)≤((k:ℝ)+2)*logScale (P.N:ℝ) := by
    dsimp [R,logScale]
    rw [Nat.cast_pow,Real.log_mul (by norm_num : (7:ℝ)≠0) (pow_pos hnp _).ne',Real.log_pow,
      Real.log_mul (by norm_num : (7:ℝ)≠0) hnp.ne']
    push_cast
    have h7 := Real.log_nonneg (by norm_num : (1:ℝ)≤7)
    nlinarith only [h7,Real.log_nonneg hn,Nat.cast_nonneg k,mul_nonneg (Nat.cast_nonneg k) h7]
  have cap' := hcard.trans (mul_le_mul_of_nonneg_left hlog dyadicConstant_pos.le)
  refine ⟨m1,(by exact_mod_cast cb : (pieces I:ℝ)≤((bank R).card:ℝ)^3).trans ?_⟩
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  simpa only [mul_assoc] using cap'

/-- One common pre-target constant for all original HB/frequency indices,
with the recalculated dyadic owners and restoring factorials of each word. -/
theorem scheduled (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ (order : ℕ) (zeta kap0 : ℝ) (I : Index order zeta kap0),
    I.P.N=N → I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
    ((bank (cap N)).card:ℝ)*totalMass b kap (outerWidth N) N kap0*scalar I*
      (∑ j∈I.P.words.attach,let A := onWord I j
        |restore I.P j.val (groups A)|*(pieces A:ℝ))≤C*(Real.log (N:ℝ))^54 := by
  obtain ⟨C0,hC,HM⟩ := exists_scheduled_split_mass
  let B := ((master omega T).card:ℝ)*((J0 omega).factorial:ℝ)^3
  let D := 2*dyadicConstant*((J0 omega:ℝ)+2)
  refine ⟨C0*4^12*(B*D^3),by dsimp [B,D]; positivity [dyadicConstant_pos],?_⟩
  intro b kap hb hb' hk gate
  filter_upwards [HM hb hb' hk gate,eventually_width 1 (by norm_num),eventually_one_le_nat_log] with N hmaster hw hl
  intro order zeta kap0 I hN hO hT he hE
  let L := Real.log (N:ℝ)
  have hL : 0≤L := by dsimp [L]; linarith
  have hNP : 1<I.P.N := by rw [hN]; have h := hw.1; omega
  have hOP : 0<I.P.omega := by rwa [hO]
  have M := admissible_words I.P hNP he hOP
  have hmass : ((I.P.words.attach).card:ℝ)≤((master omega T).card:ℝ) := by
    simpa only [Finset.card_attach,hO,hT] using (Nat.cast_le.mpr (Finset.card_le_card M) :
      (I.P.words.card:ℝ)≤((master I.P.omega I.P.T).card:ℝ))
  have hlog : logScale (I.P.N:ℝ)≤2*L := by
    rw [hN]; apply le_trans _ hw.2.2.2.2; unfold logScale
    apply add_le_add_left; apply Real.log_le_log (by have := hw.1; positivity)
    exact mul_le_mul_of_nonneg_left (target_le_countingScale N) (by norm_num)
  have hfactor : scalar I≤(4*L)^12 := by
    apply (scalar_cost I).2.trans
    apply pow_le_pow_left₀ (by have := logScale_one_le (P4BArbitraryWidthUpperBlockGeometry.countingScale_one_le I.N_pos); linarith)
    rw [hN]; linarith only [hw.2.2.2.2]
  have hD : 0≤D := by dsimp [D]; positivity [dyadicConstant_pos]
  have hweight :
      (∑ j∈I.P.words.attach,let A := onWord I j
        |restore I.P j.val (groups A)|*(pieces A:ℝ))≤B*(D*L)^3 := by
    let K := ((J0 omega).factorial:ℝ)^3
    calc
      _≤∑ _j∈I.P.words.attach,K*(D*L)^3 := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨hh,hp⟩ := factor_and_boxes (onWord I j) hNP he hOP hE
        apply mul_le_mul (by simpa only [onWord,hO,K] using hh) _ (Nat.cast_nonneg _) (by dsimp [K]; positivity)
        apply hp.trans
        change (dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3≤_
        rw [hO]
        have H : 0≤dyadicConstant*((J0 omega:ℝ)+2) := by positivity [dyadicConstant_pos]
        apply pow_le_pow_left₀ (mul_nonneg H (by have := logScale_one_le (by exact_mod_cast hNP.le : (1:ℝ)≤I.P.N); linarith))
        dsimp [D]; nlinarith only [mul_le_mul_of_nonneg_left hlog H]
      _≤_ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        simpa only [B,K,mul_assoc] using mul_le_mul_of_nonneg_right hmass
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg (J0 omega).factorial) 3)
            (pow_nonneg (mul_nonneg hD hL) 3))
  have hw0 : 0≤∑ j∈I.P.words.attach,let A := onWord I j
      |restore I.P j.val (groups A)|*(pieces A:ℝ) := Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have H := mul_le_mul (mul_le_mul (hmaster kap0) hfactor (scalar_cost I).1.le
    (mul_nonneg hC (pow_nonneg hL 39))) hweight hw0
      (mul_nonneg (mul_nonneg hC (pow_nonneg hL 39)) (pow_nonneg (by positivity : 0≤4*L) 12))
  apply H.trans_eq
  change (C0*L^39*(4*L)^12)*(B*(D*L)^3)=(C0*4^12*(B*D^3))*L^54
  ring

end
end ImbalancedChen.P4BOriginalHigherLowRestoration
