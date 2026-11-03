import ImbalancedChen.Part5OriginalH430BuchstabAtomIntervalGeometry
import ImbalancedChen.Part5OriginalH430BuchstabArithmeticRows

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact dictionary from the previously constructed physical closedChildren
to the d*N-deleted prime sum. The finite N+1 cap is proved harmless from
the original parentWindow and LocalDomain. Arithmetic parent Theta and
continuous parent physicalWeight remain different objects; the two
normalizations are linked to the SAME actual atomMass without equating
them. This does not yet insert full Program.Member history filters.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabInteriorDictionary

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalPrefixMaskMass P2OriginalHalfOpenProfileCarrier P2OriginalCompactThetaMass
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BuchstabCeilingDictionary
open Part5OriginalH430BuchstabCeilingPayment
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430NativeBuchstabMeasure
open Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430BuchstabMaskedIntervals
open Part5OriginalH430BuchstabAtomIntervalGeometry

/-- The moving residual exponent is derived from the SAME Q and word. -/
theorem sameQ_eq_physicalLevel {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) :
    Q = (parentProduct old:ℝ)*(N:ℝ)^(physicalLevel N Q old) := by
  exact sameQ_eq_residualExponent hw.1 hw.2.1
    (zero_lt_one.trans (parentWindow_logs hw).2.1)

theorem primeCoordinate_eq_relative {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (q : ℕ) :
    primeCoordinate N (physicalLevel N Q old) q = relativePrime Q old q := by
  have h := physical_log_ratio hw.1 hw.2.1 (parentWindow_logs hw).2.2
    (fun _ : Fin 1 => q) 0
  rw [← sameQ_eq_physicalLevel hw] at h
  exact h.symm

theorem primeCoordinate_mul_level {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (q : ℕ) :
    physicalLevel N Q old*primeCoordinate N (physicalLevel N Q old) q =
      physicalPrime N q := by
  rw [primeCoordinate_eq_relative hw]
  exact relativePrime_physical hw

theorem arithmeticQuery_eq {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hq : q.Prime) :
    P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q =
      reciprocalQuery (primeCoordinate N (physicalLevel N Q old) q) := by
  rw [primeCoordinate_eq_relative hw]
  have hl : Real.log (residualLevel Q old) ≠ 0 := (Real.log_pos (parentWindow_logs hw).2.1).ne'
  have hq0 : Real.log (q:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  unfold P2EnhancedLowerPrimeChildCarriers.buchstabArgument reciprocalQuery relativePrime
  field_simp [hl,hq0] <;> ring

theorem singleCoordinates_native (N q : ℕ) :
    singleCoordinates N q = nativePoint (physicalPrime N q) := by
  funext i
  fin_cases i <;> simp [singleCoordinates,nativePoint]

theorem local_atom_dictionary {up : Bool} {N q : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (hC : p.ceiling = chi) (hg : directionGuard up p) (hq : q.Prime) (b : FloorAtom) :
    (LocalDomain p (singleShape (.buchstab up p.argument)) (singleCoordinates N q) ∧
      P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q ∈ tableAtomSet up b) ↔
    primeCoordinate N (physicalLevel N Q old) q ∈
      relativeAtomDomain up (physicalStart up p) b := by
  have hu : 0 < primeCoordinate N (physicalLevel N Q old) q := by
    rw [primeCoordinate_eq_relative hw]
    exact div_pos (Real.log_pos (by exact_mod_cast hq.one_lt))
      (Real.log_pos (parentWindow_logs hw).2.1)
  have hpoint : nativePoint (residual p*primeCoordinate N (physicalLevel N Q old) q) =
      singleCoordinates N q := by
    rw [hL,primeCoordinate_mul_level hw]
    exact (singleCoordinates_native N q).symm
  have hshape : singleShape (.buchstab up p.argument) = buchstabShape up := by
    cases up <;> rfl
  simpa only [hshape,hpoint,arithmeticQuery_eq hw hq] using
    local_relative_atom_iff (hL.symm ▸ (parentWindow_logs hw).2.2)
      (hC.symm ▸ hw.2.2.2.2) hg hu b

theorem atom_member_enlarged {up : Bool} {N q M : ℕ} {L start : ℝ} {b : FloorAtom}
    (hN : 1 < N) (hL : 0 < L) (hq : q.Prime) (hc : q.Coprime M)
    (hu : primeCoordinate N L q ∈ relativeAtomDomain up start b) :
    q ∈ enlargedWindow M N L := by
  have hu' := relativeAtomDomain_bounds hu
  have hcoords : (1/10:ℝ) ≤ normalizedLog N L (fun _ : Fin 1 => q) 0 ∧
      normalizedLog N L (fun _ : Fin 1 => q) 0 < 3/5 := by
    change (1/10:ℝ) ≤ primeCoordinate N L q ∧ primeCoordinate N L q < 3/5
    constructor <;> linarith [hu'.1,hu'.2]
  have hb := (normalizedLog_window hN hL (fun _ : Fin 1 => q)
    (fun _ => hq.pos) 0 (1/10) (3/5)).mp hcoords
  apply mem_primeWindow.mpr
  refine ⟨hq,hc,?_,?_⟩
  · convert hb.1 using 1 <;> congr 1 <;> ring
  · convert hb.2 using 1 <;> congr 1 <;> ring

/-- The full closed local atom has an exact arithmetic carrier, not only
an inclusion into an analytic box. -/
theorem closed_atom_carrier {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (hC : p.ceiling = chi) (hg : directionGuard up p) (b : FloorAtom) (q : Fin (N+1)) :
    (q ∈ closedChildren up N old p ∧
      P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up b) ↔
    (q.val ∈ enlargedWindow (parentProduct old*N) N (physicalLevel N Q old) ∧
      primeCoordinate N (physicalLevel N Q old) q.val ∈
        relativeAtomDomain up (physicalStart up p) b) := by
  constructor
  · rintro ⟨hclosed,hb⟩
    obtain ⟨hp,hlocal⟩ := mem_closedChildren.mp hclosed
    have hu := (local_atom_dictionary hw hL hC hg hp.1 b).mp ⟨hlocal,hb⟩
    exact ⟨atom_member_enlarged hw.1 (parentWindow_logs hw).2.2 hp.1
      (by simpa only [mul_comm] using hp.2) hu, hu⟩
  · rintro ⟨hwin,hu⟩
    have hp := mem_primeWindow.mp hwin
    obtain ⟨hlocal,hb⟩ := (local_atom_dictionary hw hL hC hg hp.1 b).mpr hu
    exact ⟨mem_closedChildren.mpr
      ⟨⟨hp.1,by simpa only [mul_comm] using hp.2.1⟩,hlocal⟩,hb⟩

def closedAtom (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ)
    (p : PhysicalNode) (b : FloorAtom) : ℝ :=
  ∑ q ∈ closedChildren up N old p,
    pointAtom (thetaAtom N Q (parentProduct old*q.val)) up
      (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) b

theorem windowMass_filter (N : ℕ) (L : ℝ) (d : ℕ) (D : Set ℝ) :
    windowMass N L d D =
      ∑ q ∈ (enlargedWindow (d*N) N L).filter (fun q => primeCoordinate N L q ∈ D),
        localPrimeFactor d q*residualKernel (primeCoordinate N L q) := by
  unfold windowMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hu : primeCoordinate N L q ∈ D <;> simp [hu]

/-- Exact arithmetic parent factor. No division by parent Theta, by a
marked-cell mass, or by the continuous parent weight is performed. -/
theorem closedAtom_eq_windowMass {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (hC : p.ceiling = chi) (hg : directionGuard up p)
    (hA : 4 ≤ (N:ℝ)^(physicalLevel N Q old/10)) (b : FloorAtom) :
    closedAtom up N Q old p b = thetaAtom N Q (parentProduct old) *
      windowMass N (physicalLevel N Q old) (parentProduct old)
        (relativeAtomDomain up (physicalStart up p) b) := by
  let S := (closedChildren up N old p).filter (fun q =>
    P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up b)
  let V := (enlargedWindow (parentProduct old*N) N (physicalLevel N Q old)).filter
    (fun q => primeCoordinate N (physicalLevel N Q old) q ∈
      relativeAtomDomain up (physicalStart up p) b)
  have hreindex : (∑ q ∈ S, thetaAtom N Q (parentProduct old*q.val)) =
      ∑ q ∈ V, thetaAtom N Q (parentProduct old*q) := by
    apply Finset.sum_bij (fun q _ => q.val)
    · intro q hq
      exact Finset.mem_filter.mpr
        ((closed_atom_carrier hw hL hC hg b q).mp (Finset.mem_filter.mp hq))
    · intro q hq r hr heq
      exact Fin.ext heq
    · intro q hq
      obtain ⟨hwin,hu⟩ := Finset.mem_filter.mp hq
      have hp := mem_primeWindow.mp hwin
      have hlocal := ((local_atom_dictionary hw hL hC hg hp.1 b).mpr hu).1
      have hcap := local_prime_le_target hw hL hlocal
      let r : Fin (N+1) := ⟨q,by omega⟩
      refine ⟨r,?_,rfl⟩
      exact Finset.mem_filter.mpr ((closed_atom_carrier hw hL hC hg b r).mpr ⟨hwin,hu⟩)
    · intro q hq
      rfl
  calc
    closedAtom up N Q old p b = ∑ q ∈ S, thetaAtom N Q (parentProduct old*q.val) := by
      unfold closedAtom S
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hb : P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈ tableAtomSet up b
      · simp only [pointAtom,indicator_of_mem hb,mul_one,if_pos hb]
      · simp only [pointAtom,indicator_of_notMem hb,mul_zero,if_neg hb]
    _ = ∑ q ∈ V, thetaAtom N Q (parentProduct old*q) := hreindex
    _ = _ := by
      rw [windowMass_filter,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨hwin,hu⟩ := Finset.mem_filter.mp hq
      have hp := mem_primeWindow.mp hwin
      have hq4 := hA.trans hp.2.2.1
      have hq2 : 2 < q := by exact_mod_cast (show (2:ℝ) < q by linarith)
      have hpN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hp.2.1).2
      have hden : (1/10:ℝ) ≤ 1-primeCoordinate N (physicalLevel N Q old) q := by
        linarith [(relativeAtomDomain_bounds hu).2]
      rw [thetaAtom_single (by omega) hw.2.1 hp.1 hq2 hpN (parentWindow_logs hw).2.1]
      change thetaAtom N Q (parentProduct old) *
        (localPrimeFactor (parentProduct old) q/(1-relativePrime Q old q)) = _
      rw [← primeCoordinate_eq_relative hw, residualKernel, max_eq_right hden]
      ring

/-- The original two polar rows: H-parent reads h; h-parent reads H. -/
def integralRow (up : Bool) (p : PhysicalNode) : RowAtom → ℝ
  | .inl b => if up then 0 else atomMass false b (physicalStart false p)
  | .inr b => if up then atomMass true b (physicalStart true p) else 0

def nativeRow (up : Bool) (p : PhysicalNode) : RowAtom → ℝ
  | .inl b => if up then 0 else nativeAtomCoefficient false p b
  | .inr b => if up then nativeAtomCoefficient true p b else 0

theorem nativeRow_eq_weight {up : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard up p) (b : RowAtom) :
    nativeRow up p b = physicalWeight p*integralRow up p b := by
  cases up <;> cases b <;>
    simp only [nativeRow,integralRow,Bool.false_eq_true,if_false,if_true,mul_zero]
  all_goals exact nativeAtomCoefficient_eq hL hC hg _

/-- One common threshold before Q, the labelled prefix, the physical
node, both directions, the moving start and every original polar atom. -/
theorem uniform_closed_row_atom_error {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, ∀ up : Bool,
      parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → directionGuard up p →
      physicalLevel N Q old ∈ Icc Lmin Lmax → ∀ b : RowAtom,
      |closedRow up N Q old p b-thetaAtom N Q (parentProduct old)*integralRow up p b| ≤
        epsilon*thetaAtom N Q (parentProduct old) := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_masked_atom hmin hmax he
  obtain ⟨Ta,hTa⟩ := compact_multiplier_error (k := 1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
  refine ⟨max 4 (max Tp Ta), ?_⟩
  intro N hN Q chi old p up hw hL hC hg hcompact b
  have hN4 : 4 ≤ N := by omega
  have ht : 0 ≤ thetaAtom N Q (parentProduct old) :=
    thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hdN := prefix_le_target_of_commonQ hw.2.1
    (parentWindow_logs hw).2.1 hw.2.2.2.1
  have hA := (hTa N (by omega) _ hcompact).1
  have hpoint (c : FloorAtom) :
      |closedAtom up N Q old p c-thetaAtom N Q (parentProduct old)*
        atomMass up c (physicalStart up p)| ≤ epsilon*thetaAtom N Q (parentProduct old) := by
    rw [closedAtom_eq_windowMass hw hL hC hg hA c, ← mul_sub,
      abs_mul, abs_of_nonneg ht]
    have hm := hTp N (by omega) _ hcompact (parentProduct old) hw.2.1 hdN
      up (physicalStart up p) c
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm.le ht
  cases up <;> cases b with
  | inl c =>
      first
      | exact hpoint c
      | simpa only [closedRow,rowFrom,integralRow,Bool.false_eq_true,if_false,if_true,
          mul_zero,sub_self,abs_zero] using mul_nonneg he.le ht
  | inr c =>
      first
      | exact hpoint c
      | simpa only [closedRow,rowFrom,integralRow,Bool.false_eq_true,if_false,if_true,
          mul_zero,sub_self,abs_zero] using mul_nonneg he.le ht

end
end ImbalancedChen.Part5OriginalH430BuchstabInteriorDictionary
