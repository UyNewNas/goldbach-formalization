import ImbalancedChen.P4BOriginalMediumPhysicalAtomSum

/-! Restore the true HB logarithms and count the additional dyadic boxes
for this exact same word. All exponent orders are fixed before N. -/
namespace ImbalancedChen.P4BOriginalMediumRestoringBudget
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block owner bank bank_card owner_mem_bank)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalMediumAtomFamily (Index size support support_data third_data)
open P4BOriginalMediumSignedFibre (scalar)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionThirdFactor (thirdSupport thirdPairs)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos log2_count_le)
open P4AHeldTaggedCompilerSupport (J0)

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)

theorem scalar_cost : 0<scalar I ∧ scalar I≤(2*logScale (countingScale I.P.N))^12 := by
  have hm : size I.j+size I.l≤12 := by dsimp [size]; omega
  have hX := countingScale_one_le I.N_pos
  have hL := logScale_one_le hX
  obtain ⟨y,hy,hyw⟩ := I.live
  have hY := P4BOriginalCollisionModes.live_products I.b_pos I.kap_pos I.s_pos I.gate hm
    I.cj I.ck I.bs (fibre I.bs I.i I.C) (Finset.filter_subset _ _) ⟨y,hy,hyw⟩ y hy
  have hcap : (completeProduct y:ℝ)≤6*countingScale I.P.N :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hY.2).2).trans (Nat.floor_le (by linarith))
  have one (j) : P4BOriginalMediumHBHead.scalar (I.bs j) (I.roles j)≤2*logScale (countingScale I.P.N) := by
    have hq := owns_bounds ((mem_rectangle I.bs y).mp (Finset.mem_filter.mp hy).1 j)
    have hypos : 0<completeProduct y := Finset.prod_pos (fun a _ => hY.1 a)
    have hd := Nat.le_of_dvd hypos (Finset.dvd_prod_of_mem y (Finset.mem_univ j))
    have hr : (lower (I.bs j):ℝ)≤6*countingScale I.P.N := (Nat.cast_le.mpr (hq.1.trans hd)).trans hcap
    have hx : (7*countingScale I.P.N)^2≥12*countingScale I.P.N := by
      nlinarith only [hX,mul_nonneg (sub_nonneg.mpr hX) (zero_le_one.trans hX)]
    have harg : 0<2*(lower (I.bs j):ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr (lower_pos _))
    have hl := Real.log_le_log harg ((by linarith only [hr] : 2*(lower (I.bs j):ℝ)≤12*countingScale I.P.N).trans hx)
    rw [Real.log_pow] at hl
    unfold P4BOriginalMediumHBHead.scalar
    split
    · unfold logScale
      norm_num at hl
      linarith
    · linarith
  refine ⟨Finset.prod_pos (fun j _ => P4BOriginalMediumHBHead.scalar_pos _ _),?_⟩
  have H := Finset.prod_le_prod (s:=Finset.univ)
    (fun j _ => (P4BOriginalMediumHBHead.scalar_pos (I.bs j) (I.roles j)).le)
    (fun j _ => one j)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    H.trans (by simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      pow_le_pow_right₀ (show 1≤2*logScale (countingScale I.P.N) by linarith) hm)

private theorem list_bound (N : ℕ) (ps : List ℕ) (h : ∀p∈ps,p≤N) : ps.prod≤N^ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simpa only [List.prod_cons,List.length_cons,pow_succ',Nat.add_one] using
      Nat.mul_le_mul (h p List.mem_cons_self) (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))

private theorem support_cap (P : Params) (G : List ℕ) {n : ℕ} (hn : n∈support P G) :
    n≤P.N^G.length := by
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hn
  have hc := (P4AOrderedThirdClippedFactorial.crop _ _ _ _).mp hps
  rw [←actualPrimeSlotBox_length _ G ps hps]
  exact list_bound P.N ps (fun p hp => (mem_roughPrimeFinset.mp (hc.2 p hp)).1.le)

private theorem owner_count (S : Finset ℕ) (P : Params) (d : ℕ) (hN : 1<P.N)
    (hp : ∀n∈S,0<n ∧ n≤P.N^d) :
    ((S.image owner).card:ℝ)≤dyadicConstant*((d:ℝ)+1)*logScale (P.N:ℝ) := by
  have hsub : S.image owner⊆bank (P.N^d) := by
    intro B hB
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hB
    exact owner_mem_bank (hp n hn).1 (hp n hn).2
  have hNr : (1:ℝ)≤P.N := by exact_mod_cast hN.le
  have hnp : 0<(P.N:ℝ) := zero_lt_one.trans_le hNr
  have hNd : (1:ℝ)≤(P.N:ℝ)^d := one_le_pow₀ hNr
  have hc : ((S.image owner).card:ℝ)≤((Nat.log2 (P.N^d-1)+2:ℕ):ℝ) := by
    exact_mod_cast ((Finset.card_le_card hsub).trans_eq (bank_card _))
  have hd : ((P.N^d-1:ℕ):ℝ)≤(P.N:ℝ)^d := by exact_mod_cast Nat.sub_le (P.N^d) 1
  have hl := log2_count_le hNd (P.N^d-1) (by linarith)
  have hs : logScale ((P.N:ℝ)^d)≤((d:ℝ)+1)*logScale (P.N:ℝ) := by
    unfold logScale
    rw [Real.log_mul (by norm_num : (7:ℝ)≠0) (pow_pos hnp d).ne',Real.log_pow,
      Real.log_mul (by norm_num : (7:ℝ)≠0) hnp.ne']
    have hnlog := Real.log_nonneg hNr
    have h7 := Real.log_nonneg (by norm_num : (1:ℝ)≤7)
    nlinarith only [hnlog,mul_nonneg (Nat.cast_nonneg d) (show 0≤1+Real.log 7 by linarith)]
  simpa only [mul_assoc] using (hc.trans hl).trans (mul_le_mul_of_nonneg_left hs dyadicConstant_pos.le)

def pieces :=
  ((support I.P I.groups.1).image owner).card*((support I.P I.groups.2.1).image owner).card*
    ((thirdSupport I.P I.J I.groups.2.2).image owner).card

/-- Independent dyadic gamma boxes cost at most three additional logarithms.
The rank factor depends only on original positive omega, fixed before N. -/
theorem pieces_cost (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega) (hell : I.P.ell≤1) :
    (pieces I:ℝ)≤(dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3 := by
  let d := J0 I.P.omega+1
  let M := dyadicConstant*((d:ℝ)+1)*logScale (I.P.N:ℝ)
  have hM : 0≤M := by
    have h := logScale_one_le (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N)
    dsimp [M]
    positivity
  have hlen := (P4AOriginalFiniteFallbackGroupedAtoms.partition I.P.m I.P.N _ _ _ I.x I.U I.eta
    (P4BOriginalCollisionTensor.ownerHead I.P I.J) I.J (Finset.mem_filter.mp I.word).2).length_eq
  change (I.groups.1++(I.groups.2.1++I.groups.2.2)).length=I.J.length at hlen
  simp only [List.length_append] at hlen
  have hr := I.P.rank_cap I.word hN he ho
  have H (G : List ℕ) (hG : G.length≤d) : (((support I.P G).image owner).card:ℝ)≤M :=
    owner_count _ I.P d hN (fun n hn => ⟨(support_data _ _ hn).1,(support_cap _ _ hn).trans
      (Nat.pow_le_pow_right (by omega) hG)⟩)
  have h1 := H I.groups.1 (by dsimp [d]; omega)
  have h2 := H I.groups.2.1 (by dsimp [d]; omega)
  have h3 : (((thirdSupport I.P I.J I.groups.2.2).image owner).card:ℝ)≤M := by
    apply owner_count _ I.P d hN
    intro n hn
    refine ⟨(third_data _ _ _ hn).1,?_⟩
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    have hactive := (Finset.mem_filter.mp ha).2
    have ha' : (a:ℝ)<I.P.L := by
      unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta at hactive
      split_ifs at hactive
      · exact (actualSmallRosserPlus_active hactive).2.1
      · exact (actualSmallRosserMinus_active hactive).2.1
    have hL : I.P.L≤(I.P.N:ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N) hell
    have hb' := (support_cap I.P I.groups.2.2 hb).trans
      (Nat.pow_le_pow_right (by omega : 0<I.P.N) (show I.groups.2.2.length≤J0 I.P.omega by omega))
    simpa only [d,pow_succ'] using Nat.mul_le_mul (Nat.cast_le.mp (ha'.le.trans hL)) hb'
  have H3 := mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) hM) h3 (Nat.cast_nonneg _) (mul_nonneg hM hM)
  change _≤M*M*M at H3
  unfold M d at H3
  push_cast at H3 ⊢
  simpa only [pieces,Nat.cast_mul,show (J0 I.P.omega:ℝ)+1+1=(J0 I.P.omega:ℝ)+2 by ring,
    pow_succ,pow_zero,one_mul] using H3

end
end ImbalancedChen.P4BOriginalMediumRestoringBudget
