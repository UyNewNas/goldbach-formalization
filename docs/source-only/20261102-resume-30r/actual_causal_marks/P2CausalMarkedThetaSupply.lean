import ImbalancedChen.P2CausalPrimeHistorySource
import ImbalancedChen.P2EnhancedNonunitMarkedMass
import ImbalancedChen.P2OriginalW2CountTupleReindex
import ImbalancedChen.P2MarkedThetaLiNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Concrete application of Q11/Q12 to the generated arithmetic histories.
All old-prime and residual floors and the independent true-alpha gate are
discharged by the source theorem. Marks with different ranks or paths
remain external indices of the ORIGINAL p5z product pushforward. The
new theorems give no preceding H/h table count licence, no PP coefficient,
and no identification of these paths with all adopted numerical choices.
-/

namespace ImbalancedChen.P2CausalMarkedThetaSupply
noncomputable section
open Finset Wu2008DoubleSieve
open P2CausalPrimeHistorySource P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry P2EnhancedLowerPrimeChildMarks
open P2EnhancedSwitchedTrueNormalization P2EnhancedNonunitPhysicalQuadrature
open P2EnhancedMarkedBoxExceptionSupply P2EnhancedTwentyOneSameQWeighted
open P2EnhancedExactExceptionTheta P2EnhancedNonunitMarkedMass
open P2OriginalChildPhysicalNormalization
open scoped Classical BigOperators

structure Mark where
  rootRank : ℕ
  rank : ℕ
  box : PrimeBox rootRank
  history : History rootRank rank
  ceiling : ℝ
  coefficient : ℝ

def Mark.source (m : Mark) (N : ℕ) (nu : ℝ) : Finset (Fin m.rank → Fin (N+1)) :=
  m.history.family N ((N : ℝ)^nu) m.ceiling m.box

def Mark.weight (m : Mark) : ℝ := m.coefficient*m.history.scalar

/-- Conditions on fixed box faces, before N. The half-level row is
separate from the residual row; neither is a count or mass conclusion. -/
def Mark.BoxRows (m : Mark) (nu eta : ℝ) (horizon : ℕ) : Prop :=
  (∀ j, eta ≤ m.box.lower j) ∧
  6*eta ≤ nu-∑ j, m.box.upper j ∧
  2*nu ≤ 1+∑ j, m.box.lower j ∧
  m.history.depth ≤ horizon ∧ 0 ≤ m.coefficient

/-- A finite source fixes ONE positive root floor and ONE depth bound
before N. Empty books and rank-zero roots are included. The independent
alpha row remains explicit and is not inferred from the positive gaps. -/
theorem finite_book_common_floor {I : Type*} (A : Finset I) (marks : I → Mark) (nu : ℝ)
    (hlo : ∀ i ∈ A, ∀ j, 0 < (marks i).box.lower j)
    (hres : ∀ i ∈ A, 0 < nu-∑ j, (marks i).box.upper j)
    (halpha : ∀ i ∈ A, 2*nu ≤ 1+∑ j, (marks i).box.lower j)
    (hc : ∀ i ∈ A, 0 ≤ (marks i).coefficient) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ horizon : ℕ,
      ∀ i ∈ A, (marks i).BoxRows nu eta horizon := by
  let floors : Finset ℝ := insert 1 (A.biUnion fun i =>
    insert ((nu-∑ j, (marks i).box.upper j)/6)
      (univ.image (marks i).box.lower))
  have hne : floors.Nonempty := ⟨1,mem_insert_self _ _⟩
  have hpos : ∀ x ∈ floors, 0 < x := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · norm_num
    obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hx with rfl | hx
    · exact div_pos (hres i hi) (by norm_num)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    exact hlo i hi j
  let eta := floors.min' hne
  have he : 0 < eta := hpos eta (floors.min'_mem hne)
  let horizon := A.sup (fun i => (marks i).history.depth)
  refine ⟨eta,he,horizon,?_⟩
  intro i hi
  refine ⟨?_,?_,halpha i hi,le_sup hi,hc i hi⟩
  · intro j
    apply floors.min'_le
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i,hi,mem_insert_of_mem
      (mem_image.mpr ⟨j,mem_univ _,rfl⟩)⟩)
  · have hbound : eta ≤ (nu-∑ j, (marks i).box.upper j)/6 := by
      apply floors.min'_le
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨i,hi,mem_insert_self _ _⟩)
    linarith only [hbound]

theorem floorAt_antitone {eta : ℝ} (he : 0 < eta) {n m : ℕ} (hnm : n ≤ m) :
    floorAt eta m ≤ floorAt eta n := by
  have hm : m = n+(m-n) := by omega
  rw [hm]
  generalize m-n = k
  induction k with
  | zero => simp
  | succ k ih =>
      exact (by simpa only [Nat.add_succ] using floorAt_step he (n+k)).trans ih

theorem Mark.source_facts {N horizon : ℕ} (hN : 1 < N) {nu eta : ℝ}
    (he : 0 < eta) (m : Mark) (hm : m.BoxRows nu eta horizon)
    {t : Fin m.rank → Fin (N+1)} (ht : t ∈ m.source N nu) :
    TupleFacts N nu (floorAt eta horizon) t := by
  have h := m.history.family_facts hN he hm.1 hm.2.1 hm.2.2.1 ht
  have hsmall := floorAt_antitone he hm.2.2.2.1
  exact ⟨fun j => ⟨(h.1 j).1,(h.1 j).2.1,hsmall.trans (h.1 j).2.2⟩,
    (mul_le_mul_of_nonneg_left hsmall (by norm_num)).trans h.2.1,h.2.2⟩

theorem physical_floor_to_power {N p : ℕ} (hN : 1 < N) (hp : 0 < p)
    {eta : ℝ} (h : eta ≤ physicalPrime N p) : (N : ℝ)^eta ≤ p := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) (Nat.cast_pos.mpr hp)).mp
  rw [Real.log_rpow hN0]
  exact (le_div_iff₀ hlog).mp h

/-- This is a fixed covering prime box for the already constructed exact
history family. No point is added to the arithmetic source S. -/
theorem Mark.source_box {N horizon : ℕ} (hN : 1 < N) {nu eta : ℝ}
    (he : 0 < eta) (m : Mark) (hm : m.BoxRows nu eta horizon)
    {t : Fin m.rank → Fin (N+1)} (ht : t ∈ m.source N nu) (j : Fin m.rank) :
    (t j).val ∈ primeWindow N ((N : ℝ)^(floorAt eta horizon)) ((N : ℝ)^(2 : ℝ)) := by
  have h := (m.source_facts hN he hm ht).1 j
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have htN : ((t j).val : ℝ) ≤ N := by
    exact_mod_cast (show (t j).val ≤ N by omega)
  have hupper : ((t j).val : ℝ) < (N : ℝ)^(2 : ℝ) := by
    rw [Real.rpow_two,pow_two]
    exact htN.trans_lt (by simpa only [mul_one] using
      mul_lt_mul_of_pos_left hNr (zero_lt_one.trans hNr))
  exact mem_primeWindow.mpr ⟨h.1,h.1.coprime_iff_not_dvd.mpr h.2.1,
    physical_floor_to_power hN h.1.pos h.2.2,hupper⟩

theorem Mark.source_scale {N horizon : ℕ} (hN : 1 < N) {nu eta : ℝ}
    (he : 0 < eta) (m : Mark) (hm : m.BoxRows nu eta horizon)
    {t : Fin m.rank → Fin (N+1)} (ht : t ∈ m.source N nu) :
    0 < Part3.labelledProduct t ∧
    (Part3.labelledProduct t : ℝ) < (N : ℝ)^nu ∧
    (227/50 : ℝ)*floorAt eta horizon ≤
      Real.log ((N : ℝ)^nu/(Part3.labelledProduct t : ℝ))/Real.log N ∧
    (N : ℝ)^(floorAt eta horizon) ≤ (N : ℝ)^nu/Part3.labelledProduct t ∧
    2 ≤ trueAlpha N ((N : ℝ)^nu) (Part3.labelledProduct t) := by
  have hf := m.source_facts hN he hm ht
  have h0 := floorAt_pos he horizon
  have h := facts_trueAlpha hN h0 hf
  have hfloor : floorAt eta horizon ≤ residualExponent N (Part3.labelledProduct t) nu := by
    linarith only [h.2.1,h0]
  have hscale := scale_floor_of_residual hN h.1 hfloor
  have hR : 1 < (N : ℝ)^nu/Part3.labelledProduct t :=
    (one_lt_rpow (by exact_mod_cast hN) h0).trans_le hscale
  refine ⟨h.1,?_,?_,hscale,h.2.2⟩
  · exact (one_lt_div (Nat.cast_pos.mpr h.1)).mp hR
  · rw [residual_log hN h.1]
    have hn : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    rw [mul_div_cancel_left₀ _ hn]
    linarith only [h.2.1,h0]

def sourceSupport {I : Type*} (A : Finset I) (marks : I → Mark) (N : ℕ) (nu : ℝ) : Finset ℕ :=
  mixtureSupport A (fun i => (marks i).rank) (fun i => (marks i).source N nu)

def sourceSigma {I : Type*} (A : Finset I) (marks : I → Mark) (N : ℕ) (nu : ℝ) (d : ℕ) : ℝ :=
  mixtureSigma A (fun i => (marks i).rank) (fun i => (marks i).source N nu)
    (fun i _ => (marks i).weight) d

theorem sourceSigma_nonneg {I : Type*} (A : Finset I) (marks : I → Mark)
    (N : ℕ) (nu : ℝ) (hc : ∀ i ∈ A, 0 ≤ (marks i).coefficient) (d : ℕ) :
    0 ≤ sourceSigma A marks N nu d := by
  exact sum_nonneg fun i hi => p5z_markedProductWeight_nonneg _ _
    (fun _ _ => mul_nonneg (hc i hi) (marks i).history.scalar_nonneg) d

theorem source_support_data {I : Type*} {N horizon : ℕ} (hN : 1 < N)
    {nu eta : ℝ} (he : 0 < eta) (A : Finset I) (marks : I → Mark)
    (hm : ∀ i ∈ A, (marks i).BoxRows nu eta horizon)
    {d : ℕ} (hd : d ∈ sourceSupport A marks N nu) :
    0 < d ∧ (d : ℝ) < (N : ℝ)^nu ∧
    (N : ℝ)^(floorAt eta horizon) ≤ (N : ℝ)^nu/d ∧
    2 ≤ trueAlpha N ((N : ℝ)^nu) d := by
  obtain ⟨i,hi,hd⟩ := mem_biUnion.mp hd
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hd
  have h := (marks i).source_scale hN he (hm i hi) ht
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- Exact fibrewise weighted sum on the original support. This is the
support version of the existing p5z pushforward, retaining every tuple. -/
theorem marked_support_test {r N : ℕ} (S : Finset (Fin r → Fin (N+1)))
    (W : (Fin r → Fin (N+1)) → ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ markSupport S, p5z_markedProductWeight S W d*G d) =
      ∑ t ∈ S, W t*G (Part3.labelledProduct t) := by
  have hf := sum_fiberwise_of_maps_to (s := S) (t := markSupport S)
    (g := Part3.labelledProduct) (fun t ht => mem_image.mpr ⟨t,ht,rfl⟩)
    (fun t => W t*G (Part3.labelledProduct t))
  rw [← hf]
  apply sum_congr rfl
  intro d hd
  unfold p5z_markedProductWeight
  rw [sum_mul]
  apply sum_congr rfl
  intro t ht
  rw [(mem_filter.mp ht).2]

theorem marked_weight_zero_off_support {r N : ℕ} (S : Finset (Fin r → Fin (N+1)))
    (W : (Fin r → Fin (N+1)) → ℝ) {d : ℕ} (hd : d ∉ markSupport S) :
    p5z_markedProductWeight S W d = 0 := by
  apply sum_eq_zero
  intro t ht
  exact (hd (mem_image.mpr ⟨t,(mem_filter.mp ht).1,(mem_filter.mp ht).2⟩)).elim

/-- Fubini keeps the external path index even when two paths give the
same product or even the same tuple. It is also valid for signed G. -/
theorem sourceSigma_test {I : Type*} (A : Finset I) (marks : I → Mark)
    (N : ℕ) (nu : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ sourceSupport A marks N nu, sourceSigma A marks N nu d*G d) =
      ∑ i ∈ A, ∑ t ∈ (marks i).source N nu,
        (marks i).weight*G (Part3.labelledProduct t) := by
  unfold sourceSigma mixtureSigma
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hsub : markSupport ((marks i).source N nu) ⊆ sourceSupport A marks N nu := by
    intro d hd
    exact mem_biUnion.mpr ⟨i,hi,hd⟩
  rw [← marked_support_test]
  symm
  apply sum_subset hsub
  intro d hd hnot
  rw [marked_weight_zero_off_support _ _ hnot,zero_mul]

/-- Exact installed literal-li common-Q normalizer, with C(dN), phi(d),
original scalars and product multiplicities. The trueLi correction is
applied separately below using the existing uniform supplier. -/
theorem source_Theta_exact {I : Type*} (A : Finset I) (marks : I → Mark)
    (N : ℕ) (nu : ℝ) :
    Theta N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) =
      ∑ i ∈ A, ∑ t ∈ (marks i).source N nu,
        (marks i).weight*thetaAtom N ((N : ℝ)^nu) (Part3.labelledProduct t) := by
  rw [Theta_eq_sum_atoms]
  exact sourceSigma_test A marks N nu _

/-- The existing literal-li/trueLi theorem is instantiated with this
same source; its positive-kernel conditions come from the actual history.
This corrects an additive li convention, not an arithmetic count error. -/
theorem causal_trueTheta_comparison {eta epsilon : ℝ} (he : 0 < eta)
    (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ,
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark),
      (∀ i ∈ A, (marks i).BoxRows nu eta horizon) →
      let D := sourceSupport A marks N nu
      let sigma := sourceSigma A marks N nu
      Theta N ((N : ℝ)^nu) D sigma ≤
        P2MarkedThetaLiNormalization.trueTheta N ((N : ℝ)^nu) D sigma ∧
      P2MarkedThetaLiNormalization.trueTheta N ((N : ℝ)^nu) D sigma ≤
        (1+epsilon)*Theta N ((N : ℝ)^nu) D sigma ∧
      |P2MarkedThetaLiNormalization.trueTheta N ((N : ℝ)^nu) D sigma -
        Theta N ((N : ℝ)^nu) D sigma| ≤ epsilon*Theta N ((N : ℝ)^nu) D sigma := by
  obtain ⟨T,hT,hconvert⟩ := P2MarkedThetaLiNormalization.uniform_trueTheta_relative_error epsilon heps
  refine ⟨T,hT,?_⟩
  intro N hN nu I A marks hm
  have hN1 : 1 < N := by omega
  have hs := source_support_data hN1 he A marks hm
  exact hconvert N hN ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu)
    (fun d hd => (hs hd).1)
    (fun d _ => sourceSigma_nonneg A marks N nu (fun i hi => (hm i hi).2.2.2.2) d)
    (fun d hd => (one_lt_rpow (by exact_mod_cast hN1) (floorAt_pos he horizon)).trans_le
      (hs hd).2.2.1)

/-- Q11 is actually instantiated at all generated histories. Its old
and new roughness inputs are discharged, with one pre-N threshold. -/
theorem causal_exception_payment {eta epsilon : ℝ} (he : 0 < eta) (heps : 0 < epsilon)
    (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark),
      (∀ i ∈ A, (marks i).BoxRows nu eta horizon) →
      weightedErrors N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) +
        weightedCollisions N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) ≤
      epsilon*Theta N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) := by
  obtain ⟨T,hT,hpay⟩ := marked_box_mixture_payment (floorAt_pos he horizon) heps
  refine ⟨T,hT,?_⟩
  intro N hN hEven nu hnu I A marks hm
  have hN1 : 1 < N := by omega
  have hQ : (N : ℝ)^nu ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN1.le : (1 : ℝ) ≤ N) hnu
  exact hpay N hN hEven ((N : ℝ)^nu) hQ I A (fun i => (marks i).rank)
    (fun _ _ => floorAt eta horizon) (fun _ _ => 2)
    (fun i => (marks i).source N nu) (fun i _ => (marks i).weight)
    (fun _ _ _ => le_rfl)
    (fun i hi t ht j => (marks i).source_box hN1 he (hm i hi) ht j)
    (fun i hi t ht => ((marks i).source_scale hN1 he (hm i hi) ht).2.1)
    (fun i hi t ht => ((marks i).source_scale hN1 he (hm i hi) ht).2.2.1)
    (fun i hi _ _ => mul_nonneg (hm i hi).2.2.2.2 (marks i).history.scalar_nonneg)

/-- Q12 is instantiated on the SAME sigma and Theta as Q11. The true
alpha gate is derived from the independent fixed root-box half-level row.
The original twenty Gamma9--21 occurrences remain Q12's literal list. -/
theorem causal_nonunit_payment {eta epsilon : ℝ} (he : 0 < eta) (heps : 0 < epsilon)
    (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ,
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark),
      (∀ i ∈ A, (marks i).BoxRows nu eta horizon) →
      convertedOriginalSwitches N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) ≤
        originalIntegralSwitches N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) +
        epsilon*Theta N ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu) := by
  obtain ⟨T,hT,hpay⟩ := original_Gamma9_to_21_theta_upper (floorAt_pos he horizon) heps
  refine ⟨T,hT,?_⟩
  intro N hN nu I A marks hm
  have hN1 : 1 < N := by omega
  have hsource := source_support_data hN1 he A marks hm
  exact hpay N hN ((N : ℝ)^nu) (sourceSupport A marks N nu) (sourceSigma A marks N nu)
    (fun d hd => (hsource hd).1)
    (fun d _ => sourceSigma_nonneg A marks N nu (fun i hi => (hm i hi).2.2.2.2) d)
    (fun d hd => (hsource hd).2.2.1)
    (fun d hd => (hsource hd).2.2.2)

end
end ImbalancedChen.P2CausalMarkedThetaSupply
