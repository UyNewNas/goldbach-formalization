import ImbalancedChen.P4BOriginalShortMediumFibreIntegral
import ImbalancedChen.P4BOriginalRankTwoMediumRemainder

/-! Source only. The original two ordered HB groups, original group scalars
and the complete complement bank apply to both the physical raw medium total
and the surviving word integrals. -/
namespace ImbalancedChen.P4BOriginalShortMediumAtlas
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block bank)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector rectangle)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ActualHBMediumBranchPartition (firstMedium firstMedium_some)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P4BUpperPairOrderedRowGeometry (rowRoles)
open P4BUpperPairOrderedRowModes (rowBank_eq_modeBank)
open P4BOriginalUpperFourierTailPaid (groupEval groupEval_sub_le groupScalarMass sourceScalarMass
  sourceScalarMass_le dyadicConstant dyadicConstant_pos)
open P4BOriginalHighRankMotherModes (modes eventually_atlas_eq_modes)
open P4BOriginalHighRankComplementBlocks (fibre cap complement_count)
open P4BOriginalHighRankPostModulusFibres (first original_partition)
open P4BOriginalHighRankPostModulusRow (original)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BOriginalNoMediumPairRows (noMedium noMedium_eq_original)
open P4BOriginalNoMediumAtlasDictionary (noMediumTotal eventually_noMediumTotal_eq_originalBank)
open P4BOriginalRankTwoMediumRemainder (mediumTotal atlasPair_eq_medium_add_noMedium)
open P4BOriginalCollisionWords (Params)
open P4BOriginalShortMediumFibreIntegral (WordRange otherFibre exists_fibre_cost)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOuterRampRoughness (baseline)

private abbrev dim (j : ℕ) := 2*(j+1)
private abbrev RowTest := (cj ck j l : ℕ) → (Fin (dim j+dim l)→Block) → ℂ
private abbrev FibreTest := (cj ck j l : ℕ) → (Fin (dim j+dim l)→Block) → Fin (dim j+dim l) → Block → ℂ

private def chartRows (N : ℕ) (f : RowTest) : ℂ :=
  ∑ js∈chartBank N 2,groupEval (js.getD 0 0) (fun j bs => groupEval (js.getD 1 0) (fun l cs =>
    f (js.getD 0 0) (js.getD 1 0) j l (Fin.append (blockVector (dim j) bs) (blockVector (dim l) cs))))

private def selectedRow (N : ℕ) (zeta : ℝ) (f : FibreTest) : RowTest := fun cj ck j l bs =>
  match first cj ck zeta bs with
  | none => 0
  | some i => ∑ V∈bank (cap N),f cj ck j l bs i V

private def physical (P : Params) (b kap s kap0 : ℝ) (K : ℕ) : FibreTest := fun cj ck j l bs i V =>
  original (u:=dim j) (v:=dim l) b kap s P.N kap0 cj ck (fibre bs i V)
    (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
    (Fin.append (rowRoles j) (rowRoles l)) P.S P.rho

/-- Original chart/HB bank after the selected short-fibre word deletion.
Every other live medium fibre still carries its original physical test. -/
def remainingAtlas (P : Params) (b kap s kap0 zeta : ℝ) (K A : ℕ) : ℂ :=
  chartRows P.N (selectedRow P.N zeta (fun cj ck j l bs i V =>
    otherFibre (u:=dim j) (v:=dim l) b kap s P kap0 zeta cj ck A bs i V
      (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l))))

private theorem chartRows_add (N : ℕ) (f g : RowTest) :
    chartRows N (fun cj ck j l bs => f cj ck j l bs+g cj ck j l bs)=chartRows N f+chartRows N g := by
  simp only [chartRows,groupEval,Finset.sum_add_distrib,mul_add]

private theorem chartRows_sub_le (N : ℕ) (f g : RowTest) (E : ℝ)
    (h : ∀ cj ck j l,j<3 → l<3 → ∀ bs,‖f cj ck j l bs-g cj ck j l bs‖≤E) :
    ‖chartRows N f-chartRows N g‖≤sourceScalarMass N*E := by
  have one (cj ck : ℕ) :
      ‖groupEval cj (fun j bs => groupEval ck (fun l cs =>
        f cj ck j l (Fin.append (blockVector (dim j) bs) (blockVector (dim l) cs))))-
      groupEval cj (fun j bs => groupEval ck (fun l cs =>
        g cj ck j l (Fin.append (blockVector (dim j) bs) (blockVector (dim l) cs))))‖≤
        (groupScalarMass cj*groupScalarMass ck)*E := by
    rw [mul_assoc]
    apply groupEval_sub_le
    intro j hj bs _
    apply groupEval_sub_le
    intro l hl cs _
    exact h cj ck j l (Finset.mem_range.mp hj) (Finset.mem_range.mp hl) _
  unfold chartRows
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun js _ => one (js.getD 0 0) (js.getD 1 0))).trans_eq ?_)
  simp only [sourceScalarMass,Finset.sum_mul]

private theorem first_none {m : ℕ} (cj ck : ℕ) (zeta : ℝ) (bs : Fin m→Block) :
    first cj ck zeta bs=none ↔ noMedium zeta cj ck bs := by
  rw [noMedium_eq_original]
  unfold first
  cases h : firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs) with
  | none => simp
  | some n =>
    obtain ⟨hlt,_,_⟩ := firstMedium_some h
    have hn : n<m := by simpa only [List.length_ofFn] using hlt
    simp [hn]

/-- Identify the *medium* atlas by subtracting the previously identified
no-medium summand algebraically before taking any norm. -/
private theorem eventually_medium_rows {b kap : ℝ} (hb : 0<b) (hkap : 0<kap) :
    ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N →
      ∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96) (kap0 zeta : ℝ) (K : ℕ),
      mediumTotal hb hs hg P.N K kap0 zeta P.S P.rho=
        chartRows P.N (selectedRow P.N zeta (physical P b kap s kap0 K)) := by
  filter_upwards [eventually_atlas_eq_modes (kap:=kap) hb,eventually_noMediumTotal_eq_originalBank (kap:=kap) hb]
    with N hmode hno
  intro P hPN s hs hg kap0 zeta K
  subst N
  let full : RowTest := fun cj ck j l bs => original (u:=dim j) (v:=dim l) b kap s P.N kap0
    cj ck (rectangle bs) (beforeHBCutoff K [cj,ck])
    (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
    (Fin.append (rowRoles j) (rowRoles l)) P.S P.rho
  let no : RowTest := fun cj ck j l bs => if noMedium zeta cj ck bs then full cj ck j l bs else 0
  let yes := selectedRow P.N zeta (physical P b kap s kap0 K)
  have hno' : noMediumTotal hb hs hg P.N K kap0 zeta P.S P.rho=chartRows P.N no :=
    hno s hs hg K kap0 zeta P.S P.rho
  have hfull : modes b kap s P.N K kap0 P.S P.rho=chartRows P.N full := by
    unfold modes chartRows
    apply Finset.sum_congr rfl
    intro js _
    exact (rowBank_eq_modeBank hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs
      (by simpa only [one_mul] using hg) P.N K (js.getD 0 0) (js.getD 1 0) kap0 P.S
        (fun d => (P.rho d:ℂ))).symm
  have one (cj ck j l : ℕ) (hj : j<3) (hl : l<3) (bs : Fin (dim j+dim l)→Block) :
      full cj ck j l bs=yes cj ck j l bs+no cj ck j l bs := by
    cases h : first cj ck zeta bs with
    | none =>
      simp only [yes,selectedRow,h,no,if_pos ((first_none cj ck zeta bs).mp h),zero_add]
    | some i =>
      have hn : ¬noMedium zeta cj ck bs := fun hh => by
        have h' := (first_none cj ck zeta bs).mpr hh
        rw [h] at h'
        cases h'
      simp only [yes,selectedRow,h,no,if_neg hn,add_zero]
      exact (original_partition (u:=dim j) (v:=dim l) hb hkap hs hg cj ck bs i
        (by dsimp [dim]; omega) (beforeHBCutoff K [cj,ck])
        (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
        (Fin.append (rowRoles j) (rowRoles l)) P.S P.rho).symm
  have hsplit : chartRows P.N full=chartRows P.N yes+chartRows P.N no := by
    rw [←chartRows_add]
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by
      simpa only [mul_zero] using chartRows_sub_le P.N full
        (fun cj ck j l bs => yes cj ck j l bs+no cj ck j l bs) 0
        (fun cj ck j l hj hl bs => by rw [one cj ck j l hj hl bs,sub_self,norm_zero])) (norm_nonneg _)
  have he := (atlasPair_eq_medium_add_noMedium hb hs hg P.N K kap0 zeta P.S P.rho).symm.trans
    ((hmode s hs hg K kap0 zeta P.S P.rho).trans (hfull.trans hsplit))
  rw [←hno'] at he
  exact add_right_cancel he

/-- A single physical-N threshold precedes every eligible complete parameter
record, chart and occurrence. A is also the order in the true post-modulus
cutoff. The original 39 outer logarithmic powers and 15 inner powers
are paid before stating the result on the raw signed medium total. -/
theorem exists_mediumTotal_cost (K A : ℕ) (omega T : ℝ) (ho : 0<omega)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgap : 19/96<baseline b kap) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ hs : 0<outerWidth N,∃ hg : 2*outerWidth N≤baseline b kap-19/96,
      ∀ P : Params,P.N=N → WordRange P omega T zeta →
        ‖mediumTotal hb hs hg P.N K kap0 zeta P.S P.rho-
          remainingAtlas P b kap (outerWidth N) kap0 zeta K A‖≤C*N/(Real.log (N:ℝ))^A := by
  obtain ⟨D,hD,HF⟩ := exists_fibre_cost K A omega T ho hz hz0 hk hkz ht ht1 hb hb1 hkap hgap
  let c := 49*dyadicConstant^15
  have hc : 0≤c := by dsimp [c]; positivity [dyadicConstant_pos]
  refine ⟨c*2^15*D,by positivity,?_⟩
  filter_upwards [HF,eventually_medium_rows hb hkap,eventually_width _ (half_pos (sub_pos.mpr hgap)),
    eventually_one_le_nat_log] with N hrow hid hw hlog
  have hs := hw.2.1
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith only [hw.2.2.1]
  refine ⟨hs,hg,?_⟩
  intro P hPN R
  subst N
  let s := outerWidth P.N
  let L := Real.log (P.N:ℝ)
  let X := logScale (countingScale P.N)
  let E := D*P.N/L^(A+15)
  let n := ((bank (cap P.N)).card:ℝ)
  let f := physical P b kap s kap0 K
  let g : FibreTest := fun cj ck j l bs i V =>
    otherFibre (u:=dim j) (v:=dim l) b kap s P kap0 zeta cj ck A bs i V
      (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l))
  have hn : 0<P.N := by have q := hw.1; omega
  have hL : 0<L := zero_lt_one.trans_le hlog
  have hX : 0≤X := zero_le_one.trans (logScale_one_le (countingScale_one_le hn))
  have hE : 0≤E := div_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg hL.le _)
  have hn0 : 0≤n := Nat.cast_nonneg _
  have hbound (cj ck j l : ℕ) (hj : j<3) (hl : l<3) (bs : Fin (dim j+dim l)→Block) :
      ‖selectedRow P.N zeta f cj ck j l bs-selectedRow P.N zeta g cj ck j l bs‖≤n*E := by
    cases h : first cj ck zeta bs with
    | none => simp only [selectedRow,h,sub_self,norm_zero]; exact mul_nonneg hn0 hE
    | some i =>
      simp only [selectedRow,h]
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      calc
        _≤∑ _V∈bank (cap P.N),E := Finset.sum_le_sum (fun V _ =>
          hrow P rfl R ⟨j,hj⟩ ⟨l,hl⟩ cj ck bs i V h)
        _=n*E := by simp only [Finset.sum_const,nsmul_eq_mul,n]
  rw [hid P rfl s hs hg kap0 zeta K]
  change ‖chartRows P.N (selectedRow P.N zeta f)-chartRows P.N (selectedRow P.N zeta g)‖≤_
  apply (chartRows_sub_le P.N _ _ (n*E) hbound).trans
  have hprices : sourceScalarMass P.N*n≤(49*dyadicConstant^14*X^14)*(dyadicConstant*X) :=
    mul_le_mul (sourceScalarMass_le hn) (complement_count hn) hn0
      (by positivity [dyadicConstant_pos])
  calc
    _=(sourceScalarMass P.N*n)*E := (mul_assoc _ _ _).symm
    _≤((49*dyadicConstant^14*X^14)*(dyadicConstant*X))*E := mul_le_mul_of_nonneg_right hprices hE
    _=(c*X^15)*E := by dsimp only [c]; ring
    _≤(c*(2*L)^15)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hw.2.2.2.2 _) hc) hE
    _=_ := by dsimp only [E]; rw [pow_add]; field_simp [hL.ne'] <;> ring

end
end ImbalancedChen.P4BOriginalShortMediumAtlas
