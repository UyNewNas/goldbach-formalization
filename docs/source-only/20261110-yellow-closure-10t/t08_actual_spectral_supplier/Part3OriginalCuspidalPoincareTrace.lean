import ImbalancedChen.Part3OriginalContinuousPoincarePackets
import ImbalancedChen.Part3OriginalNativeCuspFunctionals

/-! The actual cuspidal projection of the same two physical quotient
packets. The native basis covers the entire all-cusp annihilator. Its
existing K classification fixes the complex order and coefficient of
every index before the common compact radial transform is applied. -/
namespace ImbalancedChen.Part3.OriginalCuspidalPoincareTrace20261110

noncomputable section
open Complex Set Filter MeasureTheory Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators
open ActualCuspBasisWhittakerCoefficients20261102 OriginalNativeCuspFunctionals20261102
open ActualFullCuspEigenbasis20261026b ActualFullCuspResolvent20261026b
open AllNormalizedCuspAnnihilator20261026b Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a NormalizedCuspCompactPoincare20261026b
open Gamma0ActualCuspsSourceOnly CompactCuspParabolicL220261025a
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open OriginalContinuousClassRemoval20261110 OriginalSignedTraceInput20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 P3NativePeriod64SamplingSourceOnly (D4)

local instance (N : ℕ) [NeZero N] (hN : 0 < N) : CompleteSpace (ActualFullCuspL2 N hN) :=
  (allFrameCuspSubspace_closed N hN).completeSpace_coe

theorem complex_order_test_integrable (ν : ℂ) (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ y)*orderRadial m ν y)) (Ioi 0) := by
  let F := fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ y)*orderRadial m ν y)
  have hm' : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hK : ContinuousOn (fun y : ℝ => ComplexOrderKBridgeSourceOnly.complexOrderK ν
      (2*Real.pi*|(m : ℝ)|*y)) (tsupport ψ) := by
    intro y hy
    exact ((ComplexOrderKQCalculus.complexOrderK_hasDerivAt_q ν
      (mul_pos (show 0 < 2*Real.pi*|(m : ℝ)| by positivity) (hs hy))).continuousAt.comp
        (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hF : ContinuousOn F (tsupport ψ) := ((continuousOn_id.inv₀ (fun y hy => (hs hy).ne')).pow 2).smul
    (hψ.star.continuousOn.mul ((continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)).continuousOn.mul hK))
  have hp : Function.support F ⊆ tsupport ψ := by
    intro y hy
    by_contra hn
    exact hy (by simp [F,image_eq_zero_of_notMem_tsupport hn])
  exact ((integrableOn_iff_integrable_of_support_subset hp).mp (ContinuousOn.integrableOn_compact hc hF)).integrableOn

private theorem seed_memLp (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    MemLp (originalPoincare N one m ψ) 2 (carrierPushforward N) := by
  rw [original_eq_framed N one m ψ hc hpos]
  exact framePoincare_memLp_two N (NeZero.pos N) (originalFrame one) m ψ hψ hc hpos

theorem basis_seed_integral (N : ℕ) [NeZero N] (i : actualCuspBasisIndex N (NeZero.pos N))
    (one : Bool) (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    let B : QuotientL2 N := actualCuspHilbertBasis N (NeZero.pos N) i
    (∫ u,star (originalPoincare N one m ψ u)*B u ∂carrierPushforward N) =
      orderProbe m ψ (basisOrder N (NeZero.pos N) i)*basisR N (NeZero.pos N) i (originalFrame one) m := by
  let B : QuotientL2 N := actualCuspHilbertBasis N (NeZero.pos N) i
  rw [original_eq_framed N one m ψ hc hpos,
    framePoincare_pairing_eq_fourier N (NeZero.pos N) (originalFrame one) m ψ hψ hc hpos B B.memLp,
    orderProbe,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [basisModes_ae_original N (NeZero.pos N) i (originalFrame one),ae_restrict_mem measurableSet_Ioi] with y hy hposy
  rw [← hy m,basisMode_eq_normalizedR N (NeZero.pos N) i (originalFrame one) hm hposy]
  simp only [orderRadial,Complex.real_smul]
  ring

theorem basis_packet_inner (N : ℕ) [NeZero N] (i : actualCuspBasisIndex N (NeZero.pos N))
    (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ) (hn : ∀ b ∈ S,ind b ≠ 0)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    inner ℂ ((packet_L2 N one S w ind hn ψ hψ hc hpos).toLp (packet N one S w ind ψ))
      (actualCuspHilbertBasis N (NeZero.pos N) i : QuotientL2 N) =
      orderProbe 1 ψ (basisOrder N (NeZero.pos N) i)*
        markedRow S w ind (basisR N (NeZero.pos N) i (originalFrame one)) := by
  let B : QuotientL2 N := actualCuspHilbertBasis N (NeZero.pos N) i
  let P := fun b => originalPoincare N one (ind b) (scaledSeed (ind b) ψ)
  let hV := packet_L2 N one S w ind hn ψ hψ hc hpos
  let V := packet N one S w ind ψ
  have hI (b : ℕ) (hb : b ∈ S) : Integrable (fun u => w b*(star (P b u)*B u)) (carrierPushforward N) := by
    obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hpos
    have hi : Integrable (fun u => star (P b u)*B u) (carrierPushforward N) :=
      MemLp.integrable_mul (p := 2) (q := 2) (seed_memLp N one (ind b) _ h₁ h₂ h₃).star B.memLp
    exact hi.const_mul _
  calc
    _ = ∫ u, star (V u)*B u ∂carrierPushforward N := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hV.coeFn_toLp] with u hu
      rw [hu]
      simp only [RCLike.inner_apply',Complex.star_def]
    _ = ∫ u, ∑ b ∈ S,w b*(star (P b u)*B u) ∂carrierPushforward N := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => by
        simp only [V,packet,star_sum,star_mul,star_star,Finset.sum_mul,P]
        apply Finset.sum_congr rfl
        intro b _
        ring)
    _ = _ := by
      rw [integral_finsetSum S hI,markedRow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hpos
      rw [integral_const_mul,basis_seed_integral N i one (ind b) (hn b hb) _ h₁ h₂ h₃,
        common_orderProbe (ind b) (hn b hb)]
      ring

private theorem common_nonzero (J j : ℕ) (p : ℕ) (hp : p ∈ commonMBlock J j) : (p : ℤ) ≠ 0 := by
  have H := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) j) (Finset.mem_Ico.mp hp).1
  exact_mod_cast H.ne'

private theorem row_nonzero (D : OriginalData) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue ≠ 0) (negativeM : Bool) (n : ℕ) (hn : n ∈ nCarrier D k z.val) :
    traceIndex D k negativeM z.val n ≠ 0 :=
  Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z.val hn ha)

def originalMVector (N : ℕ) [NeZero N] (J j : ℕ) (ell : D4 → ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) : QuotientL2 N :=
  (packet_L2 N false (commonMBlock J j) (fun p => star ((commonPoissonCompleted J j (ell 1)).weight p))
    (fun p => (p : ℤ)) (common_nonzero J j) ψ hψ hc hpos).toLp (mPacket N J j ell ψ)

def originalNVector (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (ell : D4 → ℤ) (φ : ℝ → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hpos : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    QuotientL2 z.val := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  exact (packet_L2 z.val true (nCarrier D k z.val) (traceBeta D r k upper negativeM ell z.val)
    (traceIndex D k negativeM z.val) (row_nonzero D k z ha negativeM) φ hφ hc hpos).toLp
    (nPacket D r k z upper negativeM ell φ)

def project (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] ActualFullCuspL2 N (NeZero.pos N) :=
  (allFrameCuspSubspace N (NeZero.pos N)).orthogonalProjectionOnto

/-- True HasSum over the entire native cuspidal Hilbert basis, in the
orientation forced by the author's exterior conjugation on M. It gives
the spatial inner product of the actual cusp projections in order N,M.
Threshold, exceptional and regular Maass vectors all retain their own
original eigenvalue and their same-basis S20 coefficients. -/
theorem original_cuspidal_trace (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let hN := NeZero.pos z.val
    HasSum (fun i : actualCuspBasisIndex z.val hN =>
        (star (orderProbe 1 ψ (basisOrder z.val hN i))*orderProbe 1 φ (basisOrder z.val hN i))*
          (star (originalMFunctional J j ell z.val hN i)*originalNFunctional D r k upper negativeM ell z.val hN i))
      (inner ℂ (project z.val (originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ))
        (project z.val (originalMVector z.val J j ell ψ hψ hcψ hpψ))) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let N := z.val
  let hN := NeZero.pos N
  let B := actualCuspHilbertBasis N hN
  let K := allFrameCuspSubspace N hN
  let Mv := originalMVector N J j ell ψ hψ hcψ hpψ
  let Nv := originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ
  have hM (i : actualCuspBasisIndex N hN) : inner ℂ Mv (B i : QuotientL2 N) =
      orderProbe 1 ψ (basisOrder N hN i)*originalMFunctional J j ell N hN i := by
    exact basis_packet_inner N i false _ _ _ (common_nonzero J j) ψ hψ hcψ hpψ
  have hT (i : actualCuspBasisIndex N hN) : inner ℂ Nv (B i : QuotientL2 N) =
      orderProbe 1 φ (basisOrder N hN i)*originalNFunctional D r k upper negativeM ell N hN i := by
    exact basis_packet_inner N i true _ _ _ (row_nonzero D k z ha negativeM) φ hφ hcφ hpφ
  convert B.hasSum_inner_mul_inner (project N Nv) (project N Mv) using 1
  ext i
  change _ = inner ℂ (K.orthogonalProjectionOnto Nv) (B i) * inner ℂ (B i) (K.orthogonalProjectionOnto Mv)
  rw [K.inner_orthogonalProjectionOnto_eq_of_mem_right,K.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ← inner_conj_symm (B i : QuotientL2 N) Mv,hM,hT]
  simp only [starRingEnd_apply,star_mul]
  ring

end
end ImbalancedChen.Part3.OriginalCuspidalPoincareTrace20261110
