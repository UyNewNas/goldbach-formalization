import ImbalancedChen.P1OriginalSingletonMediumFourier
import ImbalancedChen.P1OriginalSingletonOneLongRestoration
import all ImbalancedChen.P4BOriginalMediumRestoringBudget

/-!
SOURCE ONLY / NOT COMPILED.

Per live singleton fibre: restore the actual HB role scalar and original
word factorials, and count the actual occupied modulus owners. The generic
support/owner count and original finite master bank are reused. No mother
mass, complete singleton Atlas inventory or signed M estimate is assumed.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumRestoringBudget
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P1OriginalSingletonMediumReconstruction (scalar onWord)
open P1OriginalSingletonMediumFourier (amplitude amplitude_l1_budget)
open P1OriginalSingletonOneLongProfile (profileHeight)
open P1OriginalSingletonOneLongRestoration (height_one_le actual_raw_product_cap lower_le_raw)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionThirdFactor (thirdSupport master admissible_words)
open P4BOriginalMediumAtomFamily (support support_data third_data)
open P4BOriginalHigherLowTensor (restore)
open P4BOriginalHigherActionGroups (rule)
open P5Z.HBRightClosedDyadicRoles (owner)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos)
open P4AHeldTaggedCompilerSupport (J0)
open private support_cap owner_count from ImbalancedChen.P4BOriginalMediumRestoringBudget

variable {modeOrder : ℕ} {kap zeta kap0 : ℝ} (I : Index modeOrder kap zeta kap0)

/-- At most six genuine role scalars, restored outside both arithmetic
sums. The singleton's own cap2N supplies every block bound. -/
theorem scalar_cost (hkap : kap<1) :
    0<scalar I ∧ scalar I≤profileHeight I.P.N^6 := by
  have alive : ∃ n∈rectangle I.bv, P5Z.ActualLowerNormalizedAtlasOccurrence.integerProfile
      kap 6 I.P.N I.cj kap0 n≠0 := by
    obtain ⟨n,hn,hw⟩ := I.live
    exact ⟨n,(Finset.mem_filter.mp hn).1,hw⟩
  have hcap := actual_raw_product_cap kap hkap 6 I.P.N I.cj kap0 I.bv alive
  have hH := height_one_le I.P.N
  have one (a : Fin (size I.j)) :
      P4BOriginalMediumHBHead.scalar (I.bv a) (I.roles a)≤profileHeight I.P.N := by
    have hr : (lower (I.bv a):ℝ)≤2*(I.P.N:ℝ) := by exact_mod_cast (lower_le_raw I.bv a).trans hcap
    have hp : 0<2*(lower (I.bv a):ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr (lower_pos _))
    have hl := Real.log_le_log hp (show 2*(lower (I.bv a):ℝ)≤8*(I.P.N:ℝ)+8 by
      nlinarith only [hr,Nat.cast_nonneg I.P.N])
    unfold P4BOriginalMediumHBHead.scalar
    split
    · dsimp [profileHeight]
      linarith only [hl]
    · exact hH
  refine ⟨Finset.prod_pos (fun a _ => P4BOriginalMediumHBHead.scalar_pos _ _),?_⟩
  have H := Finset.prod_le_prod (s:=Finset.univ)
    (fun a _ => (P4BOriginalMediumHBHead.scalar_pos (I.bv a) (I.roles a)).le) (fun a _ => one a)
  have hd : size I.j≤6 := by dsimp [size]; omega
  apply H.trans
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using pow_le_pow_right₀ hH hd

def pieces : ℕ := I.firstOwners.card*I.secondOwners.card*I.thirdOwners.card

/-- The selected common assignment is a permutation of this exact word;
its restored factorials keep the original signed scalar. -/
theorem factor_cost (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega) :
    |restore I.P I.J I.groups|≤((J0 I.P.omega).factorial:ℝ)^3 := by
  let k := J0 I.P.omega
  have part := (rule.perm I.P hN I.x I.U zeta I.J I.word).length_eq
  change (I.groups.1++(I.groups.2.1++I.groups.2.2)).length=I.J.length at part
  simp only [List.length_append] at part
  have hr := I.P.rank_cap I.word hN he ho
  have fa (a : ℕ) (h : a≤k) : (a.factorial:ℝ)≤(k.factorial:ℝ) := by exact_mod_cast Nat.factorial_le h
  simp only [restore,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _≤1*(k.factorial:ℝ)*k.factorial*k.factorial :=
      mul_le_mul (mul_le_mul (mul_le_mul (P4BOriginalCollisionTensor.scalar_bound I.P I.J)
        (fa _ (by dsimp [k]; omega)) (Nat.cast_nonneg _) zero_le_one)
        (fa _ (by dsimp [k]; omega)) (Nat.cast_nonneg _) (by positivity))
        (fa _ (by dsimp [k]; omega)) (Nat.cast_nonneg _) (by positivity)
    _=_ := by ring

/-- Actual occupied owner sets cost at most three extra logarithms.
The third factor retains its genuine small Rosser integer. -/
theorem pieces_cost (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega) (hell : I.P.ell≤1) :
    (pieces I:ℝ)≤(dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3 := by
  let d := J0 I.P.omega+1
  let M := dyadicConstant*((d:ℝ)+1)*logScale (I.P.N:ℝ)
  have hM : 0≤M := by
    have hL := logScale_one_le (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N)
    dsimp [M]
    exact mul_nonneg (mul_nonneg dyadicConstant_pos.le
      (add_nonneg (Nat.cast_nonneg d) zero_le_one)) (zero_le_one.trans hL)
  have part := (rule.perm I.P hN I.x I.U zeta I.J I.word).length_eq
  change (I.groups.1++(I.groups.2.1++I.groups.2.2)).length=I.J.length at part
  simp only [List.length_append] at part
  have hr := I.P.rank_cap I.word hN he ho
  have H (S : List ℕ) (hS : S.length≤d) :
      (((support I.P S).image owner).card:ℝ)≤M :=
    owner_count _ I.P d hN (fun n hn => ⟨(support_data _ _ hn).1,(support_cap _ _ hn).trans
      (Nat.pow_le_pow_right (by omega) hS)⟩)
  have h1 := H I.groups.1 (by dsimp [d]; omega)
  have h2 := H I.groups.2.1 (by dsimp [d]; omega)
  have h3 : (((thirdSupport I.P I.J I.groups.2.2).image owner).card:ℝ)≤M := by
    apply owner_count _ I.P d hN
    intro n hn
    refine ⟨(third_data _ _ _ hn).1,?_⟩
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    have hz := (Finset.mem_filter.mp ha).2
    have ha' : (a:ℝ)<I.P.L := by
      unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta at hz
      split_ifs at hz
      · exact (actualSmallRosserPlus_active hz).2.1
      · exact (actualSmallRosserMinus_active hz).2.1
    have hL : I.P.L≤(I.P.N:ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N) hell
    have hb' := (support_cap I.P I.groups.2.2 hb).trans
      (Nat.pow_le_pow_right (by omega : 0<I.P.N) (show I.groups.2.2.length≤J0 I.P.omega by omega))
    simpa only [d,pow_succ'] using Nat.mul_le_mul (Nat.cast_le.mp (ha'.le.trans hL)) hb'
  have H3 := mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) hM) h3
    (Nat.cast_nonneg _) (mul_nonneg hM hM)
  change _≤M*M*M at H3
  unfold M d at H3
  push_cast at H3 ⊢
  simpa only [pieces,P1OriginalSingletonMediumLowThreeAdmissible.Index.firstOwners,
    P1OriginalSingletonMediumLowThreeAdmissible.Index.secondOwners,
    P1OriginalSingletonMediumLowThreeAdmissible.Index.thirdOwners,Nat.cast_mul,
    show (J0 I.P.omega:ℝ)+1+1=(J0 I.P.omega:ℝ)+2 by ring,
    pow_succ,pow_zero,one_mul] using H3

def modulusCost : ℝ :=
  ∑ J∈I.P.words.attach,|restore I.P J.val (onWord I J).groups|*(pieces (onWord I J):ℝ)

/-- All actual word restoring factors are charged to the existing master
bank fixed by omega and the one actual fine mesh T before N. -/
theorem modulus_cost (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega) (hell : I.P.ell≤1) :
    modulusCost I≤((master I.P.omega I.P.T).card:ℝ)*((J0 I.P.omega).factorial:ℝ)^3*
      (dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3 := by
  let K : ℝ := ((J0 I.P.omega).factorial:ℝ)^3
  let M : ℝ := (dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3
  have hM : 0≤M := by
    have hL := logScale_one_le (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N)
    dsimp [M]
    positivity [dyadicConstant_pos]
  have bound (J : {J // J∈I.P.words}) :
      |restore I.P J.val (onWord I J).groups|*(pieces (onWord I J):ℝ)≤K*M :=
    mul_le_mul (factor_cost (onWord I J) hN he ho) (pieces_cost (onWord I J) hN he ho hell)
      (Nat.cast_nonneg _) (by dsimp [K]; positivity)
  have hc : (I.P.words.card:ℝ)≤((master I.P.omega I.P.T).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (admissible_words I.P hN he ho)
  apply (Finset.sum_le_sum (fun J _ => bound J)).trans
  simpa only [modulusCost,Finset.sum_const,Finset.card_attach,nsmul_eq_mul,K,M,mul_assoc] using
    mul_le_mul_of_nonneg_right hc (mul_nonneg (by dsimp [K]; positivity) hM)

/-- Genuine per-fibre amplitude/role/factorial/owner cost. No H^dimension
factor is substituted for the Fourier L1 norm. This does not sum the outer
HB row, chart or complementary-block banks. -/
theorem restored_amplitude_cost (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ (modeOrder : ℕ) (kap zeta kap0 : ℝ)
      (I : Index modeOrder kap zeta kap0),kap<1 → 1<I.P.N →
      I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
      (∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I≤
        C*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*logScale (I.P.N:ℝ)^3 := by
  obtain ⟨CA,hCA,HA⟩ := amplitude_l1_budget
  let B : ℝ := ((master omega T).card:ℝ)*((J0 omega).factorial:ℝ)^3
  let D : ℝ := dyadicConstant*((J0 omega:ℝ)+2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hD : 0≤D := by dsimp [D]; positivity [dyadicConstant_pos]
  refine ⟨CA*B*D^3,by positivity,?_⟩
  intro modeOrder kap zeta kap0 I hkap hN hw hT he hell
  have hOP : 0<I.P.omega := by simpa only [hw] using ho
  have hL : 0≤logScale (I.P.N:ℝ) := zero_le_one.trans (logScale_one_le (by exact_mod_cast hN.le))
  have hlog : 0≤Real.log ((I.P.N:ℝ)+2) := Real.log_nonneg (by linarith only [show 0≤(I.P.N:ℝ) from Nat.cast_nonneg _])
  have hHeight := height_one_le I.P.N
  have hA : (∫ xi,‖amplitude I xi‖)≤CA*Real.log ((I.P.N:ℝ)+2)^72 := by
    apply (HA modeOrder kap zeta kap0 I).trans
    exact div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hM : modulusCost I≤B*(D*logScale (I.P.N:ℝ))^3 := by
    simpa only [B,D,hw,hT] using modulus_cost I hN he hOP hell
  have hNN : 0≤modulusCost I := Finset.sum_nonneg (fun J _ =>
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have H := mul_le_mul (mul_le_mul hA (scalar_cost I hkap).2 (scalar_cost I hkap).1.le
    (by positivity)) hM hNN (by positivity)
  apply H.trans_eq
  ring

/-- The original finite HB row scalar is retained once, outside the
occurrence amplitude and every signed modulus atom. -/
theorem hb_scalar_bound : ‖P5Z.SmoothChartHBDyadicPartition.scalar I.j.val‖≤3 := by
  have hj : I.j.val=0 ∨ I.j.val=1 ∨ I.j.val=2 := by omega
  rcases hj with h|h|h <;> rw [h] <;>
    norm_num [P5Z.SmoothChartHBDyadicPartition.scalar,Complex.norm_real,Real.norm_eq_abs]

theorem restored_row_amplitude_cost (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ (modeOrder : ℕ) (kap zeta kap0 : ℝ)
      (I : Index modeOrder kap zeta kap0),kap<1 → 1<I.P.N →
      I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
      ‖P5Z.SmoothChartHBDyadicPartition.scalar I.j.val‖*
        ((∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I)≤
        C*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*logScale (I.P.N:ℝ)^3 := by
  obtain ⟨C,hC,HC⟩ := restored_amplitude_cost omega T ho
  refine ⟨3*C,by positivity,?_⟩
  intro modeOrder kap zeta kap0 I hkap hN hw hT he hell
  have hp : 0≤(∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I :=
    mul_nonneg (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (scalar_cost I hkap).1.le)
      (Finset.sum_nonneg (fun J _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
  calc
    _≤3*((∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I) :=
      mul_le_mul_of_nonneg_right (hb_scalar_bound I) hp
    _≤3*(C*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*logScale (I.P.N:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (HC modeOrder kap zeta kap0 I hkap hN hw hT he hell) (by norm_num)
    _=_ := by ring

end
end ImbalancedChen.P1OriginalSingletonMediumRestoringBudget
