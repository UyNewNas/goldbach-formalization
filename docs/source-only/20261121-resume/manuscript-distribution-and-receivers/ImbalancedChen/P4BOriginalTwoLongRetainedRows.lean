import ImbalancedChen.P4BOriginalNativeTargetPayment
import ImbalancedChen.P4BOriginalHighRankPostModulusCount

/-! SOURCE ONLY / UNCOMPILED. The actual two-mother no-medium subbank.
Dead source rows are zero before Fourier insertion; their amplitude need
not vanish. Retained integration spends the true normalized amplitude L1,
not the volume of the frequency cube. -/
namespace ImbalancedChen.P4BOriginalTwoLongRetainedRows
noncomputable section
open Classical Filter MeasureTheory Set
open scoped BigOperators
open PrimeProducts
open P4BOriginalNoMediumPairRows (noMedium live dead_row_zero)
open P4BOriginalNativeTargetPayment
open P4BOriginalSharpNativeRow (nativeMode)
open P4BOriginalHighRankPostModulusRow (original retained truncated truncated_eq_band H exists_row_payment)
open P4BOriginalHighRankMotherMass (rowMass)
open P4BOriginalHighRankScheduledCount (outerWidth resolution)
open P4BUpperPairOrderedRowModes (amplitude amplitude_integrable amplitude_mode_integrable rowAtom)
open P4BUpperPairOrderedRowGeometry (blockScales rowRoles integerProfile)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.AllRankCauchyCubeTail (outsideCube measurableSet_outsideCube)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOuterRampRoughness (baseline)

def originalBranchRow {u v : ℕ} (zeta b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (bs : Fin (u+v)→Block) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) : ℂ :=
  if noMedium zeta cj ck bs then
    original (u:=u) (v:=v) b kap s N kap0 cj ck (rectangle bs) Z ys rs S c else 0

def retainedBranchRow {u v : ℕ} (zeta b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (bs : Fin (u+v)→Block) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) (A0 : ℕ) : ℂ :=
  if noMedium zeta cj ck bs ∧ live b kap s N kap0 cj ck bs Z ys rs then
    retained (u:=u) (v:=v) b kap s N kap0 cj ck bs (rectangle bs) Z ys rs S c A0 else 0

theorem live_profile {u v : ℕ} {b kap s kap0 : ℝ} {N cj ck : ℕ}
    {bs : Fin (u+v)→Block} {Z : ℝ} {ys : Fin (u+v)→ℝ} {rs : Fin (u+v)→Role}
    (hlive : live b kap s N kap0 cj ck bs Z ys rs) :
    ∃ y∈rectangle bs,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0 := by
  obtain ⟨y,hy,hactive⟩ := hlive
  refine ⟨y,hy,?_⟩
  intro hz
  exact (mul_ne_zero_iff.mp hactive).2 (by rw [hz]; rfl)

/-- A finite integration lemma only. The mode hypothesis is discharged by
the actual native target theorem in eventually_retained_row_le below. -/
theorem truncated_le_rowMass {u v N : ℕ} {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block) (Z : ℝ)
    (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (S : Finset ℕ) (c : ℕ→ℝ)
    (A0 : ℕ) {E : ℝ} (hE : 0≤E)
    (hmode : ∀ xi : Fin (u+v)→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      ‖nativeMode bs Z ys xi rs N S (fun d => (c d:ℂ))‖≤E) :
    ‖truncated (u:=u) (v:=v) b kap s N kap0 cj ck bs (rectangle bs) Z ys rs S c (H N A0)‖≤
      rowMass (u:=u) (v:=v) b kap s N kap0 cj ck bs*E := by
  let M := amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs
  let F := fun xi : Fin (u+v)→ℝ => nativeMode bs Z ys xi rs N S (fun d => (c d:ℂ))
  let R := (outsideCube (u+v) (H N A0))ᶜ
  have hg' : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have hM : Integrable M := amplitude_integrable hb (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<19/96) hs hg' N kap0 cj ck bs
  have hi : Integrable (fun xi => M xi*F xi) := by
    let C := fun y => ∑ q∈S,(c q:ℂ)*MellinInsertion20261028.residueKernel q N (completeProduct y)
    have terms (y : Fin (u+v)→ℕ) : Integrable (fun xi =>
        M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) := by
      have hi' := (amplitude_mode_integrable hb (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<19/96) hs hg' N kap0 cj ck bs y).const_mul (hbSlots Z ys rs y)
      exact hi'.congr (Eventually.of_forall (fun xi => by dsimp [M]; ring))
    have hh := MellinInsertion20261028.functional_integrable (rectangle bs) C
      (fun xi y => M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) (fun y _ => terms y)
    simpa only [MellinInsertion20261028.functional_mul] using hh
  rw [truncated_eq_band hb hs hg]
  change ‖∫ xi in R,M xi*F xi‖≤_
  calc
    _≤∫ xi in R,‖M xi*F xi‖ := norm_integral_le_integral_norm _
    _≤∫ xi in R,‖M xi‖*E := by
      apply setIntegral_mono_on hi.norm.integrableOn (hM.norm.mul_const E).integrableOn
        (measurableSet_outsideCube _ _).compl
      intro xi hxi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmode xi hxi) (norm_nonneg _)
    _=(∫ xi in R,‖M xi‖)*E := by rw [integral_mul_const]
    _≤_ := mul_le_mul_of_nonneg_right (setIntegral_le_integral hM.norm
      (Eventually.of_forall (fun xi => norm_nonneg _))) hE

/-- The original post-modulus tail estimate survives restriction to the
actual block-only branch and the genuine nonzero HB source rows. -/
theorem exists_branch_row_tail :
    ∃ C : ℝ,0≤C ∧ ∀ {N u v : ℕ} {b kap : ℝ},0<N → 0<b → b≤1 → 0<kap →
      2*outerWidth N≤baseline b kap-19/96 →
      (resolution N+1:ℝ)≤logScale (countingScale N) → u+v≤12 →
      ∀ (kap0 zeta : ℝ) (A0 cj ck : ℕ) (bs : Fin (u+v)→Block)
        (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
        (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),
      S⊆Q omega N → let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖originalBranchRow (u:=u) (v:=v) zeta b kap (outerWidth N) N kap0 cj ck bs Z ys rs S c-
        retainedBranchRow zeta b kap (outerWidth N) N kap0 cj ck bs Z ys rs S c A0‖≤
          C*N/logScale (countingScale N)^(A0+18) := by
  obtain ⟨C,hC,HC⟩ := exists_row_payment
  refine ⟨C,hC,?_⟩
  intro N u v b kap hN hb hb1 hk hg hres hd kap0 zeta A0 cj ck bs Z ys rs m r n e q a omega k ell S hS
  dsimp only
  intro hRange
  have hL : 0<logScale (countingScale N) :=
    zero_lt_one.trans_le (logScale_one_le (countingScale_one_le hN))
  by_cases hn : noMedium zeta cj ck bs
  · by_cases hlive : live b kap (outerWidth N) N kap0 cj ck bs Z ys rs
    · simp only [originalBranchRow,retainedBranchRow,if_pos hn,if_pos ⟨hn,hlive⟩]
      simpa only [show A0+15+3=A0+18 by omega] using
        HC hN hb hb1 hk hg hres hd kap0 A0 cj ck bs (rectangle bs) (fun _ h => h)
          Z ys rs m r n e q a omega k ell S hS hRange
    · have hz := dead_row_zero b kap (outerWidth N) N kap0 cj ck bs Z ys rs S
        (fun d => (coefficient m r n e q a omega k N ((N:ℝ)^ell) d:ℂ)) hlive
      change original (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck (rectangle bs) Z ys rs S
        (coefficient m r n e q a omega k N ((N:ℝ)^ell))=0 at hz
      simp only [originalBranchRow,retainedBranchRow,if_pos hn,not_false_eq_true,
        if_neg (show ¬(noMedium zeta cj ck bs ∧ live b kap (outerWidth N) N kap0 cj ck bs Z ys rs)
          from fun h => hlive h.2),hz,sub_self,norm_zero]
      positivity
  · simp only [originalBranchRow,retainedBranchRow,if_neg hn,
      if_neg (show ¬(noMedium zeta cj ck bs ∧ live b kap (outerWidth N) N kap0 cj ck bs Z ys rs)
        from fun h => hn h.1),sub_self,norm_zero]
    positivity

theorem eventually_retained_row_le (K A0 A : ℕ)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (j l cj ck : ℕ),j∈Finset.range 3 → l∈Finset.range 3 →
      ∀ (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block)
        (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      let blocks := Fin.append bs cs
      let Z := beforeHBCutoff K [cj,ck]
      let ys := Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck)
      let rs := Fin.append (rowRoles j) (rowRoles l)
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      ‖retainedBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 cj ck blocks Z ys rs S c A0‖≤
        rowMass (u:=2*(j+1)) (v:=2*(l+1)) b kap s N kap0 cj ck blocks*
          (localConstant A*N/(Real.log (N:ℝ))^A) := by
  filter_upwards [eventually_native_target_paid K A0 A hz hz1 hk hkz ht ht1,
    eventually_one_le_nat_log] with N Hlocal hlog
  intro b kap s hb hkap hs hg j l cj ck hj hl bs cs m r n e q a omega k ell hRange S hS
  dsimp only
  let blocks := Fin.append bs cs
  let Z := beforeHBCutoff K [cj,ck]
  let ys := Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck)
  let rs := Fin.append (rowRoles j) (rowRoles l)
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  have hlog0 : 0<Real.log (N:ℝ) := zero_lt_one.trans_le hlog
  have hE : 0≤localConstant A*N/(Real.log (N:ℝ))^A := by
    have hc := localConstant_nonneg A
    positivity
  by_cases h : noMedium zeta cj ck blocks ∧ live b kap s N kap0 cj ck blocks Z ys rs
  · have hweak := live_profile h.2
    simp only [retainedBranchRow,if_pos h,retained,if_pos hweak]
    apply truncated_le_rowMass hb hs hg kap0 cj ck blocks Z ys rs S c A0 hE
    intro xi hxi
    exact Hlocal hb hkap hs hg j l cj ck hj hl bs cs h.1 h.2
      m r n e q a omega k ell hRange S hS xi hxi
  · simp only [retainedBranchRow,if_neg h,norm_zero]
    exact mul_nonneg (integral_nonneg (fun _ => norm_nonneg _)) hE

end
end ImbalancedChen.P4BOriginalTwoLongRetainedRows
