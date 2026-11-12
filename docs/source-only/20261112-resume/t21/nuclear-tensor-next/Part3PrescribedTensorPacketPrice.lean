import ImbalancedChen.Part3PrescribedTensorSeedNorm
import ImbalancedChen.Part3OriginalProjectedContinuousCovariance
import Batteries.Tactic.OpenPrivate

/-! Sum the actual Poisson-block weights on the two observation frames
before using the absolute centre budget. The four integer tile indices
never enter the arithmetic carriers or their coefficients. -/
namespace ImbalancedChen.Part3.PrescribedTensorPacketPrice20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups UpperHalfPlane
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 PrescribedTensorSeedNorm20261112
open ActualSignedPoincareEnvelope20261112 OriginalContinuousPoincarePackets20261110
open OriginalCuspidalPoincareTrace20261110 ActualContinuousPoincarePairing20261110
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalContinuousClassRemoval20261110 P3NativePeriod64SamplingSourceOnly (D4)
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

private theorem sum_ae {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι)
    (V : ι → QuotientL2 N) (f : ι → Gamma0OrbitSpace N → ℂ)
    (h : ∀ b, (V b : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] f b) :
    ((∑ b∈s,V b : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      fun u => ∑ b∈s,f b u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 (carrierPushforward N)
  | @insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (V b) (∑ t∈s,V t),h b,ih] with u hu h₁ h₂
    simpa only [Pi.add_apply,h₁,h₂] using hu

theorem packet_budget (N : ℕ) [NeZero N] (one right : Bool) (S : Finset ℕ)
    (w : ℕ → ℂ) (ind : ℕ → ℤ) (hn : ∀ b∈S,ind b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i k : ℤ,
      let ψ := probe right i k
      let h := probe_test right i k
      ‖(packet_L2 N one S w ind hn ψ h.1 h.2.1 h.2.2).toLp (packet N one S w ind ψ)‖ ≤ C*price i := by
  classical
  choose K hK hK' using fun b : S => scaled_frame_budget N (ind b) (hn b b.property)
  refine ⟨∑ b : S, ‖w b‖*K b,Finset.sum_nonneg (fun b _ => mul_nonneg (norm_nonneg _) (hK b)),?_⟩
  intro i k
  let ψ := probe right i k
  let h := probe_test right i k
  let t (b : S) := scaled_test (ind b) (hn b b.property) ψ h.1 h.2.1 h.2.2
  let A (b : S) := framedVector N (originalFrame one) (ind b) (scaledSeed (ind b) ψ)
    (t b).1 (t b).2.1 (t b).2.2
  let F (b : S) := originalPoincare N one (ind b) (scaledSeed (ind b) ψ)
  have aeA (b : S) : (A b : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] F b := by
    unfold F
    rw [original_eq_framed N one (ind b) _ (t b).2.1 (t b).2.2]
    exact framedVector_ae N _ _ _ _ _ _
  have aeS := sum_ae (N:=N) (Finset.univ : Finset S) (fun b => star (w b) • A b)
    (fun b u => star (w b)*F b u) (fun b => by
      filter_upwards [Lp.coeFn_smul (star (w b)) (A b),aeA b] with u hu hv
      simpa only [Pi.smul_apply,smul_eq_mul,hv] using hu)
  have eq : (packet_L2 N one S w ind hn ψ h.1 h.2.1 h.2.2).toLp (packet N one S w ind ψ)
      = ∑ b : S,star (w b) • A b := by
    apply Lp.ext
    apply (packet_L2 N one S w ind hn ψ h.1 h.2.1 h.2.2).coeFn_toLp.trans
    simpa only [F,Finset.sum_coe_sort,packet] using aeS.symm
  change ‖(packet_L2 N one S w ind hn ψ h.1 h.2.1 h.2.2).toLp (packet N one S w ind ψ)‖ ≤ _
  rw [eq,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_smul,norm_star,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK' b (originalFrame one) right i k) (norm_nonneg _)

abbrev mVector (N : ℕ) [NeZero N] (J j : ℕ) (ell : D4 → ℤ) (q : Modes) :=
  originalMVector N J j ell (pattern q.1.1 q.2.1) (pattern_test _ _).1
    (pattern_test _ _).2.1 (pattern_test _ _).2.2
abbrev nVector (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (ell : D4 → ℤ) (q : Modes) :=
  originalNVector D r k z ha upper negativeM ell (rightPattern q.1.2 q.2.2) (right_test _ _).1
    (right_test _ _).2.1 (right_test _ _).2.2

theorem marked_trace_class (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ)
    (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    Summable (fun q : Modes => ‖c ell Y q‖*(‖mVector z.val J j ell q‖*
      ‖nVector D r k z ha upper negativeM ell q‖)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  obtain ⟨L,hL,hM⟩ := packet_budget z.val false false (commonMBlock J j)
    (fun p => star ((commonPoissonCompleted J j (ell 1)).weight p)) (fun p => (p:ℤ)) (common_nonzero J j)
  obtain ⟨R,hR,hN⟩ := packet_budget z.val true true (nCarrier D k z.val)
    (traceBeta D r k upper negativeM ell z.val) (traceIndex D k negativeM z.val)
    (row_nonzero D k z ha negativeM)
  apply ((absolute_centers ell hY (A:=1) zero_le_one).mul_right (4*L*R)).of_nonneg_of_le
    (fun q => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  intro q
  have a := (hM q.1.1 q.2.1).trans (mul_le_mul_of_nonneg_left (price_growth _) hL)
  have b := (hN q.1.2 q.2.2).trans (mul_le_mul_of_nonneg_left (price_growth _) hR)
  have e : heightWeight 1 q=Real.exp |(q.1.1:ℝ)|*Real.exp |(q.1.2:ℝ)| := by
    simp only [heightWeight,one_mul,Real.exp_add]
  calc
    _ ≤ ‖c ell Y q‖*((L*(2*Real.exp |(q.1.1:ℝ)|))*(R*(2*Real.exp |(q.1.2:ℝ)|))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul a b (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _ := by rw [e]; ring

end
end ImbalancedChen.Part3.PrescribedTensorPacketPrice20261112
