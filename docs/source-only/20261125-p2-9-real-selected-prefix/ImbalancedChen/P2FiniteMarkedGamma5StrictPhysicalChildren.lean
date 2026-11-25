import ImbalancedChen.P2FiniteMarkedGamma5ActualParentChildren
import ImbalancedChen.Part5OriginalH430PrimeChildAdmission

namespace ImbalancedChen.P2FiniteMarkedGamma5StrictPhysicalChildren
noncomputable section
open Real
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry (physicalLevel)
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open P2FiniteMarkedGamma5ActualParentChildren

def oneDomain (v : PhysicalNode) (rule : SingleRule) (z : Point) : Prop :=
  match rule with
  | .buchstab up s =>
      (if up then 1 ≤ s else 2 ≤ s) ∧
      P2EnhancedLowerPhysicalTransition.buchstabArgument v z ∈
        (if up then buchstabUpperDomain s else buchstabLowerDomain s)
  | .w1 i j => normalized v z 0 ∈ W1Domain i j
  | .w2 b i => normalized v z 0 ∈ W2SingletonDomain (originalW2At b) i

/-- All real window and log tests have strict positive denominators. -/
def window (v : PhysicalNode) : Prop :=
  0 < residual v ∧ v.total ≤ 1 ∧ 0 < v.ceiling

def singleGate (v : PhysicalNode) (rule : SingleRule) (z : Point) : Prop :=
  window v ∧ 0 < z 0 ∧ oneDomain v rule z ∧ z 0 < v.ceiling ∧ z 0 < residual v

def pairGate (v : PhysicalNode) (bank : Fin 36) (piece : Fin 4) (z : Point) : Prop :=
  window v ∧ 0 < z 0 ∧ z 0 < z 1 ∧ normalized v z ∈ W2PairDomain (originalW2At bank) piece ∧
    z 0 < v.ceiling ∧ z 1 < v.ceiling ∧ z 0 + z 1 < residual v

private theorem cap_iff {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hq : 0 < q) :
    ((parentProduct old * q : ℕ) : ℝ) < Q ↔ physicalPrime N q < physicalLevel N Q old := by
  have hd : (0 : ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have hQ : 0 < Q := hd.trans hw.2.2.1
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  simp only [physicalPrime,physicalLevel,residualLevel,Nat.cast_mul,
    div_lt_div_iff_of_pos_right (P2EnhancedLowerPrimeChildGeometry.parentWindow_logs hw).1,
    Real.log_lt_log_iff hq' (div_pos hQ hd),lt_div_iff₀ hd]
  rw [mul_comm]

private theorem pair_cap_iff {N a b : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (ha : 0 < a) (hb : 0 < b) :
    ((parentProduct old * b * a : ℕ) : ℝ) < Q ↔
      physicalPrime N a + physicalPrime N b < physicalLevel N Q old := by
  have hprod : physicalPrime N (b*a) = physicalPrime N a + physicalPrime N b := by
    simp only [physicalPrime,Nat.cast_mul,Real.log_mul (Nat.cast_pos.mpr hb).ne' (Nat.cast_pos.mpr ha).ne']
    ring
  simpa only [← Nat.mul_assoc,hprod] using (cap_iff hw (Nat.mul_pos hb ha))

variable {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
variable (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
variable (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
variable (ho : o ∈ rootHistory N n k t p)
include hN ht ht' hn hp ho

theorem single_physical_iff (rule : SingleRule) (q : Fin (N+1))
    (hq : q.val.Prime) (hc : q.val.Coprime N) :
    q ∈ singleChildren rule N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ↔
      singleGate o.current.node.physical rule (singleCoordinates N q.val) := by
  have hN' : 1 < N := by omega
  have H := rootHistory_coherent hN' ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hw := coherent_window H
  have hL := coherent_residual H
  have hw' : window o.current.node.physical := ⟨H.residual_pos,H.total_le_one,H.ceiling_pos⟩
  have hd : singleDomain rule (rootQ N n k t p) o.current.old q.val ↔
      oneDomain o.current.node.physical rule (singleCoordinates N q.val) := by
    cases rule with
    | buchstab up s => simp only [oneDomain,singleDomain,actual_buchstab_argument hw hq hL]
    | w1 i j => simp only [oneDomain,singleDomain,actual_normalized_single hw hL]
    | w2 b i => simp only [oneDomain,singleDomain,actual_normalized_single hw hL]
  rw [single_iff hN ht ht' hn hp ho,cap_iff hw hq.pos,← hL,hd]
  simp [singleGate,hw,hw',hq,hc,singleCoordinates,physicalPrime_pos hN' hq]

theorem pair_physical_iff (bank : Fin 36) (piece : Fin 4) (v : Fin (N+1) × Fin (N+1))
    (ha : v.1.val.Prime) (hca : v.1.val.Coprime N)
    (hb : v.2.val.Prime) (hcb : v.2.val.Coprime N) :
    v ∈ pairChildren bank piece N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ↔
      pairGate o.current.node.physical bank piece (pairCoordinates N v.1.val v.2.val) := by
  have hN' : 1 < N := by omega
  have H := rootHistory_coherent hN' ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hw := coherent_window H
  have hL := coherent_residual H
  have hw' : window o.current.node.physical := ⟨H.residual_pos,H.total_le_one,H.ceiling_pos⟩
  have horder : v.1.val < v.2.val ↔ physicalPrime N v.1.val < physicalPrime N v.2.val := by
    constructor
    · exact physicalPrime_strictMono hN' ha
    · intro h
      by_contra! hrev
      rcases lt_or_eq_of_le hrev with hh | hh
      · exact (not_lt_of_ge (physicalPrime_strictMono hN' hb hh).le) h
      · simpa only [hh,lt_self_iff_false] using h
  rw [pair_iff hN ht ht' hn hp ho,pair_cap_iff hw ha.pos hb.pos,← hL,horder,
    ← actual_normalized_pair hw hL]
  simp [pairGate,hw,hw',ha,hb,hca,hcb,pairCoordinates,physicalPrime_pos hN' ha]

end
end ImbalancedChen.P2FiniteMarkedGamma5StrictPhysicalChildren
