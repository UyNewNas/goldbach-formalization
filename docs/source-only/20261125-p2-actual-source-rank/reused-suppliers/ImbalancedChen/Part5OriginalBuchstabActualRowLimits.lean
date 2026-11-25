import ImbalancedChen.Part5OriginalBuchstabNativeAtomDictionary
import ImbalancedChen.Part5OriginalH430BuchstabArithmeticRows

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact binding of the new prime sums to the original closedChildren and
strictRow carriers. Physical residual, old integer word, physical ceiling
and Q are not replaced. The N+1 enumeration cap is derived from local
geometry. This file proves local arithmetic coefficient limits; it does
not identify an arbitrary local parent with the original full Member tree.
-/
namespace ImbalancedChen.Part5OriginalBuchstabActualRowLimits

noncomputable section
open Set Filter MeasureTheory Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open Part5OriginalUpsilon5CausalDictionary
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels Part5UpperTables
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactThetaMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalPrefixMaskMass
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BuchstabCeilingDictionary Part5OriginalH430BuchstabCeilingPayment
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430BuchstabPhysicalBudget Part5OriginalH430NativeBuchstabMeasure
open Part5OriginalBuchstabCompactAtoms Part5OriginalBuchstabTrueAtomLimits
open Part5OriginalBuchstabNativeAtomDictionary
open Part5OriginalH430PhysicalMassPerturbation

/-- The actual arithmetic residual determines the same original Q. -/
theorem parent_sameQ {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) :
    Q = (parentProduct old:ℝ)*(N:ℝ)^(physicalLevel N Q old) := by
  simpa only [residualExponent,physicalLevel,residualLevel] using
    sameQ_eq_residualExponent hw.1 hw.2.1
      (zero_lt_one.trans (parentWindow_logs hw).2.1)

theorem parent_level_le_one {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) : physicalLevel N Q old ≤ 1 := by
  have hd1 : (1:ℝ) ≤ parentProduct old := by
    exact_mod_cast (show 1 ≤ parentProduct old from hw.2.1)
  have hd0 : (0:ℝ) < parentProduct old := by exact_mod_cast hw.2.1
  have hQ0 : 0 < Q := hd0.trans hw.2.2.1
  have hR : residualLevel Q old ≤ (N:ℝ) :=
    (div_le_self hQ0.le hd1).trans hw.2.2.2.1
  have hlogs := parentWindow_logs hw
  apply (div_le_iff₀ hlogs.1).mpr
  simpa only [one_mul] using
    Real.log_le_log (zero_lt_one.trans hlogs.2.1) hR

theorem primeCoord_eq_relative {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) :
    primeCoord N (physicalLevel N Q old) q 0 = relativePrime Q old q := by
  have h := physical_log_ratio hw.1 hw.2.1 (parentWindow_logs hw).2.2
    (fun _ : Fin 1 => q) 0
  rw [← parent_sameQ hw] at h
  simpa only [primeCoord,normalizedLog,relativePrime,residualLevel] using h.symm

theorem query_eq_arithmetic {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hq : q.Prime) :
    query (primeCoord N (physicalLevel N Q old) q) =
      P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q := by
  have hp : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hR : 0 < Real.log (residualLevel Q old) :=
    Real.log_pos (parentWindow_logs hw).2.1
  rw [query,primeCoord_eq_relative hw]
  unfold relativePrime P2EnhancedLowerPrimeChildCarriers.buchstabArgument
  field_simp [hp.ne',hR.ne'] <;> ring

theorem singleCoordinates_eq_nativePoint (N q : ℕ) :
    singleCoordinates N q = nativePoint (physicalPrime N q) := by
  funext i
  fin_cases i <;> simp [singleCoordinates,nativePoint]

theorem singleShape_eq (up : Bool) (s : ℝ) :
    singleShape (.buchstab up s) = buchstabShape up := by cases up <;> rfl

/-- This converse uses the existing inverse native map, not a new
source-admission assumption. The lower s=2 case is included. -/
theorem native_local_iff_interval {up : Bool} {p : PhysicalNode} {x : ℝ}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard up p)
    (hx : 0 < x) :
    LocalDomain p (buchstabShape up) (nativePoint x) ↔
      P2EnhancedLowerPhysicalTransition.buchstabArgument p (nativePoint x) ∈
        Icc (physicalStart up p) 5 := by
  let w := P2EnhancedLowerPhysicalTransition.buchstabArgument p (nativePoint x)
  have hinv : buchstabPoint p w = nativePoint x := by
    rw [← nativePoint_nativeMap,nativeMap_left_inverse hL hx]
  constructor
  · intro hd
    have hw := (native_local_query_bounds hd).2
    exact (actual_buchstab_domain hL hC hg hw.1).mp (hinv.symm ▸ hd)
  · intro hw
    have hw1 : 1 ≤ w := (physicalStart_ge_one hg).trans hw.1
    exact hinv ▸ (actual_buchstab_domain hL hC hg hw1).mpr hw

/-- Same normalized atom on the real prime coordinate and on the
literal original LocalDomain, including its actual query and ceiling. -/
theorem natural_atom_iff {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hq : q.Prime)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hg : directionGuard up p) (b : FloorAtom) :
    primeCoord N (physicalLevel N Q old) q ∈ atomDomain up b (physicalStart up p) ↔
      LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q) ∧
      P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q ∈ tableAtomSet up b := by
  have hLp : 0 < residual p := hL.symm ▸ (parentWindow_logs hw).2.2
  have hCp : 0 < p.ceiling := hC.symm ▸ hw.2.2.2.2
  have hx : 0 < physicalPrime N q := physicalPrime_pos hw.1 hq
  have hu : 0 < primeCoord N (physicalLevel N Q old) q 0 := by
    rw [primeCoord_eq_relative hw]
    exact div_pos (Real.log_pos (by exact_mod_cast hq.one_lt))
      (Real.log_pos (parentWindow_logs hw).2.1)
  have hquery := actual_buchstab_argument hw hq hL
  rw [singleCoordinates_eq_nativePoint] at hquery
  rw [atomDomain_query (physicalStart_ge_one hg),query_eq_arithmetic hw hq,
    singleShape_eq,singleCoordinates_eq_nativePoint,
    native_local_iff_interval hLp hCp hg hx,hquery]
  simp only [hu,true_and]

/-- Actual local support lies strictly inside the enlarged prime window.
The finite equality endpoints of the atom itself have not been removed. -/
theorem local_mem_primeWindow {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hq : q.Prime)
    (hcop : q.Coprime (N*parentProduct old))
    (hL : residual p = physicalLevel N Q old)
    (hlocal : LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q)) :
    q ∈ primeWindow (parentProduct old*N)
      ((N:ℝ)^(physicalLevel N Q old/10)) ((N:ℝ)^(3*physicalLevel N Q old/5)) := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hw.1
  have hqR : (0:ℝ) < q := by exact_mod_cast hq.pos
  have hp : (N:ℝ)^(physicalPrime N q) = (q:ℝ) := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hNR) hqR).mp
    exact div_mul_cancel₀ _ (Real.log_pos hNR).ne'
  obtain ⟨hx,hceil,hsq,hfloor⟩ := local_geometry hlocal
  rw [hL] at hsq hfloor
  have hLp := (parentWindow_logs hw).2.2
  refine mem_primeWindow.mpr ⟨hq,by simpa only [Nat.mul_comm] using hcop,?_,?_⟩
  · rw [← hp]
    apply (Real.rpow_le_rpow_left_iff hNR).mpr
    linarith
  · rw [← hp]
    apply (Real.rpow_lt_rpow_left_iff hNR).mpr
    linarith

def closedAtom (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ)
    (p : PhysicalNode) (b : FloorAtom) : ℝ :=
  ∑ q ∈ closedChildren up N old p,
    pointAtom (thetaAtom N Q (parentProduct old*q.val)) up
      (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) b

theorem closedAtom_eq_filter (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ)
    (p : PhysicalNode) (b : FloorAtom) :
    closedAtom up N Q old p b =
      ∑ q ∈ (closedChildren up N old p).filter (fun q =>
        P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up b),
        thetaAtom N Q (parentProduct old*q.val) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hb : P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up b
  · simp only [pointAtom,indicator_of_mem hb,mul_one,if_pos hb]
  · simp only [pointAtom,indicator_of_notMem hb,mul_zero,if_neg hb]

theorem maskedAtom_eq_filter (N : ℕ) (L : ℝ) (d : ℕ)
    (up : Bool) (b : FloorAtom) (c : ℝ) :
    maskedAtom N L d up b c =
      ∑ q ∈ (primeWindow (d*N) ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5))).filter
        (fun q => primeCoord N L q ∈ atomDomain up b c),
        localPrimeFactor d q*residualSingle (primeCoord N L q) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hx : primeCoord N L q ∈ atomDomain up b c
  · simp only [atomTest,indicator_of_mem hx,if_pos hx]
  · simp only [atomTest,indicator_of_notMem hx,mul_zero,if_neg hx]

/-- Exact equality before limits. Both directions of the natural/Fin
carrier correspondence are proved; there is no source-equality field. -/
theorem closedAtom_eq_theta_masked {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hg : directionGuard up p) (hA : 4 ≤ (N:ℝ)^(physicalLevel N Q old/10))
    (b : FloorAtom) :
    closedAtom up N Q old p b = thetaAtom N Q (parentProduct old)*
      maskedAtom N (physicalLevel N Q old) (parentProduct old) up b (physicalStart up p) := by
  rw [closedAtom_eq_filter,maskedAtom_eq_filter,Finset.mul_sum]
  refine Finset.sum_bij (fun q _ => q.val) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hq,hb⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,hl⟩ := mem_closedChildren.mp hq
    exact Finset.mem_filter.mpr ⟨local_mem_primeWindow hw hp.1 hp.2 hL hl,
      (natural_atom_iff hw hp.1 hL hC hg b).mpr ⟨hl,hb⟩⟩
  · intro q hq r hr he
    exact Fin.ext he
  · intro q hq
    obtain ⟨hwq,hx⟩ := Finset.mem_filter.mp hq
    have hp := (mem_primeWindow.mp hwq).1
    obtain ⟨hl,hb⟩ := (natural_atom_iff hw hp hL hC hg b).mp hx
    have hcap := local_prime_le_target hw hL hl
    let r : Fin (N+1) := ⟨q,by omega⟩
    refine ⟨r,Finset.mem_filter.mpr ⟨mem_closedChildren.mpr ⟨⟨hp,?_⟩,hl⟩,hb⟩,rfl⟩
    simpa only [Nat.mul_comm] using (mem_primeWindow.mp hwq).2.1
  · intro q hq
    obtain ⟨hq,hb⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,hl⟩ := mem_closedChildren.mp hq
    have hwq := local_mem_primeWindow hw hp.1 hp.2 hL hl
    have hq4 := hA.trans (mem_primeWindow.mp hwq).2.2.1
    have hq2 : 2 < q.val := by exact_mod_cast (show (2:ℝ) < q.val by linarith)
    have htheta := thetaAtom_single (by omega) hw.2.1 hp.1 hq2
      (Nat.coprime_mul_iff_right.mp hp.2).1 (parentWindow_logs hw).2.1
    change thetaAtom N Q (parentProduct old*q.val) =
      thetaAtom N Q (parentProduct old)*
        (localPrimeFactor (parentProduct old) q.val/(1-relativePrime Q old q.val)) at htheta
    rw [htheta,← primeCoord_eq_relative hw]
    have hu := relativePrime_le_half hw hL hq
    rw [← primeCoord_eq_relative hw] at hu
    simp only [residualSingle,max_eq_right (show (1/10:ℝ) ≤
      1-primeCoord N (physicalLevel N Q old) q.val 0 by linarith)]
    ring

/-- Active row polarities agree with the original 802-atom bank convention. -/
def integralRow (up : Bool) (p : PhysicalNode) : RowAtom → ℝ
  | .inl b => if up then 0 else normalizedAtomIntegral false b (physicalStart false p)
  | .inr b => if up then normalizedAtomIntegral true b (physicalStart true p) else 0

def maskedRow (up : Bool) (N : ℕ) (L : ℝ) (d : ℕ) (p : PhysicalNode) : RowAtom → ℝ
  | .inl b => if up then 0 else maskedAtom N L d false b (physicalStart false p)
  | .inr b => if up then maskedAtom N L d true b (physicalStart true p) else 0

theorem closedRow_eq_theta_masked {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hg : directionGuard up p) (hA : 4 ≤ (N:ℝ)^(physicalLevel N Q old/10))
    (b : RowAtom) : closedRow up N Q old p b =
      thetaAtom N Q (parentProduct old)*maskedRow up N (physicalLevel N Q old) (parentProduct old) p b := by
  cases up <;> cases b with
  | inl b =>
      first
      | exact closedAtom_eq_theta_masked hw hL hC hg hA b
      | simp only [closedRow,rowFrom,maskedRow,if_true,mul_zero]
  | inr b =>
      first
      | exact closedAtom_eq_theta_masked hw hL hC hg hA b
      | simp only [closedRow,rowFrom,maskedRow,Bool.false_eq_true,if_false,mul_zero]

/-- No residual upper-bound assumption is needed: it is derived from the
actual parentWindow at Q<=N. The lower floor is still a graph obligation. -/
theorem uniform_closedRow_error {Lmin epsilon : ℝ}
    (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, ∀ up : Bool,
      parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → directionGuard up p → Lmin ≤ physicalLevel N Q old →
      ∀ b : RowAtom,
      |closedRow up N Q old p b-thetaAtom N Q (parentProduct old)*integralRow up p b| ≤
        epsilon*thetaAtom N Q (parentProduct old) := by
  let Lmax := max Lmin 1
  obtain ⟨Tp,hp⟩ := compact_uniform_masked_atoms (Lmax:=Lmax) hmin (le_max_left _ _) he
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=1) hmin
    (show Lmin ≤ Lmax from le_max_left _ _) (by norm_num : (0:ℝ) ≤ 0)
    (by norm_num : (0:ℝ) < 1)
  refine ⟨max 4 (max Tp Ta), ?_⟩
  intro N hN Q chi old p up hw hL hC hg hminL b
  have hN4 : 4 ≤ N := by omega
  have hLC : physicalLevel N Q old ∈ Icc Lmin Lmax :=
    ⟨hminL,(parent_level_le_one hw).trans (le_max_right _ _)⟩
  have hdN := prefix_le_target_of_commonQ hw.2.1 (parentWindow_logs hw).2.1 hw.2.2.2.1
  have hc := physicalStart_ge_one hg
  have hcc : min (physicalStart up p) 6 ∈ Icc (1:ℝ) 6 :=
    ⟨le_min hc (by norm_num),min_le_right _ _⟩
  have ht := thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hscalar (a : FloorAtom) :
      |maskedAtom N (physicalLevel N Q old) (parentProduct old) up a (physicalStart up p) -
        normalizedAtomIntegral up a (physicalStart up p)| < epsilon := by
    have hh := hp N (by omega) _ hLC _ hcc _ hw.2.1 hdN up a
    simpa only [maskedAtom,atomTest,normalizedAtomIntegral,capped_atomDomain hc] using hh
  rw [closedRow_eq_theta_masked hw hL hC hg (ha N (by omega) _ hLC).1,
    ← mul_sub,abs_mul,abs_of_nonneg ht]
  have herr : |maskedRow up N (physicalLevel N Q old) (parentProduct old) p b -
      integralRow up p b| ≤ epsilon := by
    cases up <;> cases b with
    | inl a =>
        first | exact (hscalar a).le
              | simpa only [maskedRow,integralRow,if_true,sub_self,abs_zero] using he.le
    | inr a =>
        first | exact (hscalar a).le
              | simpa only [maskedRow,integralRow,Bool.false_eq_true,if_false,sub_self,abs_zero] using he.le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left herr ht

/-- The same ideal coefficient occurs in the actual native integral.
There is no assertion that physicalWeight p equals thetaAtom N Q d. -/
theorem native_integralRow_dictionary {up : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard up p) :
    (∀ b : FloorAtom, nativeAtomCoefficient up p b = physicalWeight p *
      (if up then integralRow up p (.inr b) else integralRow up p (.inl b))) := by
  intro b
  have h := nativeAtomCoefficient_eq_normalized hL hC hg b
  cases up <;> simpa only [integralRow,if_true,if_false,Bool.false_eq_true] using h

end
end ImbalancedChen.Part5OriginalBuchstabActualRowLimits
