import ImbalancedChen.P4BOriginalTwoLongRetainedRows

/-! SOURCE ONLY / UNCOMPILED. Literal original two-group HB scalar and
chart banks, restricted only by the actual block-only no-medium test.
The actual amplitude's normalized L1 and every ordered owner are retained.
No additional child refinement is inserted in this original rowBank. -/
namespace ImbalancedChen.P4BOriginalTwoLongMotherBank
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open P4BOriginalTwoLongRetainedRows
open P4BOriginalNativeTargetPayment (localConstant)
open P4BOriginalUpperFourierTailPaid (groupEval groupEval_sub_le groupScalarMass sourceScalarMass
  sourceScalarMass_le dyadicConstant dyadicConstant_pos)
open P4BOriginalHighRankMotherMass (weightedGroup totalMass rowMass)
open P4BOriginalHighRankScheduledCount (outerWidth resolution eventually_width)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff hbCap)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank beforeHBCutoff)
open P4BUpperPairOrderedRowGeometry (rowRoles)
open P4BOuterRampRoughness (baseline)

def originalBank (zeta b kap s : ℝ) (N K : ℕ) (kap0 : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) : ℂ :=
  ∑ js∈chartBank N 2,groupEval (js.getD 0 0) (fun j bs => groupEval (js.getD 1 0) (fun l cs =>
    originalBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 (js.getD 0 0) (js.getD 1 0)
      (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
      (beforeHBCutoff K [js.getD 0 0,js.getD 1 0])
      (Fin.append (fun _ => hbCutoff (js.getD 0 0)) (fun _ => hbCutoff (js.getD 1 0)))
      (Fin.append (rowRoles j) (rowRoles l)) S c))

def retainedBank (zeta b kap s : ℝ) (N K A0 : ℕ) (kap0 : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) : ℂ :=
  ∑ js∈chartBank N 2,groupEval (js.getD 0 0) (fun j bs => groupEval (js.getD 1 0) (fun l cs =>
    retainedBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 (js.getD 0 0) (js.getD 1 0)
      (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
      (beforeHBCutoff K [js.getD 0 0,js.getD 1 0])
      (Fin.append (fun _ => hbCutoff (js.getD 0 0)) (fun _ => hbCutoff (js.getD 1 0)))
      (Fin.append (rowRoles j) (rowRoles l)) S c A0))

theorem groupEval_norm_le (cj : ℕ) (F : ℕ→List Block→ℂ) (f : ℕ→List Block→ℝ)
    (h : ∀ j∈Finset.range 3,∀ bs∈blockWords (hbCap cj) (2*(j+1)),‖F j bs‖≤f j bs) :
    ‖groupEval cj F‖≤weightedGroup cj f := by
  unfold groupEval weightedGroup
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (h j hj))

theorem weightedGroup_mul_const (cj : ℕ) (f : ℕ→List Block→ℝ) (E : ℝ) :
    weightedGroup cj (fun j bs => f j bs*E)=weightedGroup cj f*E := by
  unfold weightedGroup
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro bs hbs
  ring

/-- All actual branch rows are paid with their own amplitude mass, then
summed with the original signed HB scalars. No counting bound is assumed. -/
theorem eventually_retained_bank_le (K A0 A : ℕ)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      ‖retainedBank zeta b kap s N K A0 kap0 S (coefficient m r n e q a omega k N ((N:ℝ)^ell))‖≤
        totalMass b kap s N kap0*(localConstant A*N/(Real.log (N:ℝ))^A) := by
  filter_upwards [eventually_retained_row_le K A0 A hz hz1 hk hkz ht ht1] with N hrows
  intro b kap s hb hkap hs hg m r n e q a omega k ell hRange S hS
  let E := localConstant A*N/(Real.log (N:ℝ))^A
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  have H (cj ck : ℕ) :
      ‖groupEval cj (fun j bs => groupEval ck (fun l cs =>
        retainedBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
          (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
          (Fin.append (rowRoles j) (rowRoles l)) S c A0))‖≤
      weightedGroup cj (fun j bs => weightedGroup ck (fun l cs =>
        rowMass (u:=2*(j+1)) (v:=2*(l+1)) b kap s N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))))*E := by
    rw [←weightedGroup_mul_const]
    apply groupEval_norm_le
    intro j hj bs hbs
    rw [←weightedGroup_mul_const]
    apply groupEval_norm_le
    intro l hl cs hcs
    exact hrows hb hkap hs hg j l cj ck hj hl _ _ m r n e q a omega k ell hRange S hS
  unfold retainedBank
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun js _ => H (js.getD 0 0) (js.getD 1 0))).trans_eq
  rw [←Finset.sum_mul]
  rfl

/-- The existing complete-modulus tail is restored across the same branch.
The actual original scalar/chart inventory costs log^14. No complement
bank is added on this unsplit two-long branch. -/
theorem exists_branch_bank_tail :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
      ∀ᶠ N : ℕ in atTop,∀ (K A0 : ℕ) (kap0 zeta : ℝ)
        (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),
      S⊆Q omega N → let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖originalBank zeta b kap (outerWidth N) N K kap0 S c-
        retainedBank zeta b kap (outerWidth N) N K A0 kap0 S c‖≤
          C*N/logScale (countingScale N)^(A0+4) := by
  obtain ⟨C,hC,HC⟩ := exists_branch_row_tail
  refine ⟨49*dyadicConstant^14*C,by positivity,?_⟩
  intro b kap hb hb1 hk hgate
  filter_upwards [eventually_width _ (half_pos (sub_pos.mpr hgate))] with N hw
  obtain ⟨hN,hs,hs',hres,hLtop⟩ := hw
  have hN0 : 0<N := by omega
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith
  intro K A0 kap0 zeta m r n e q a omega k ell S hS
  dsimp only
  intro hRange
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let L := logScale (countingScale N)
  let E := C*N/L^(A0+18)
  have hL : 1≤L := logScale_one_le (countingScale_one_le hN0)
  have hp : 0<L := zero_lt_one.trans_le hL
  have hE : 0≤E := by dsimp [E]; positivity
  have H (cj ck : ℕ) :
      ‖groupEval cj (fun j bs => groupEval ck (fun l cs =>
        originalBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap (outerWidth N) N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
          (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
          (Fin.append (rowRoles j) (rowRoles l)) S c))-
        groupEval cj (fun j bs => groupEval ck (fun l cs =>
        retainedBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap (outerWidth N) N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
          (beforeHBCutoff K [cj,ck]) (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
          (Fin.append (rowRoles j) (rowRoles l)) S c A0))‖≤
        (groupScalarMass cj*groupScalarMass ck)*E := by
    rw [mul_assoc]
    apply groupEval_sub_le
    intro j hj bs hbs
    apply groupEval_sub_le
    intro l hl cs hcs
    have hd : 2*(j+1)+2*(l+1)≤12 := by
      have := Finset.mem_range.mp hj
      have := Finset.mem_range.mp hl
      omega
    exact HC hN0 hb hb1 hk hg hres hd kap0 zeta A0 cj ck _ _ _ _ m r n e q a omega k ell S hS hRange
  unfold originalBank retainedBank
  rw [←Finset.sum_sub_distrib]
  calc
    _≤∑ js∈chartBank N 2,(groupScalarMass (js.getD 0 0)*groupScalarMass (js.getD 1 0))*E :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun js _ => H _ _))
    _=sourceScalarMass N*E := by rw [←Finset.sum_mul]; rfl
    _≤(49*dyadicConstant^14*L^14)*E := mul_le_mul_of_nonneg_right (sourceScalarMass_le hN0) hE
    _=_ := by
      dsimp only [E]
      rw [show A0+18=(A0+4)+14 by omega,pow_add]
      field_simp [hp.ne']
      ring

end
end ImbalancedChen.P4BOriginalTwoLongMotherBank
