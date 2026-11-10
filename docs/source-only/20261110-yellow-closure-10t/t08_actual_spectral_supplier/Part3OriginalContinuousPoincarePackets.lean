import ImbalancedChen.Part3ActualContinuousPoincarePairing
import ImbalancedChen.Part3OriginalContinuousCuspGram

/-! The same marked M and N functionals as compact, physical quotient
Poincare tests. Height dilation gives one common radial probe per side
of the source covariance, even when the signed indices vary. -/
namespace ImbalancedChen.Part3.OriginalContinuousPoincarePackets20261110

noncomputable section
open Set MeasureTheory Complex UpperHalfPlane
open scoped UpperHalfPlane BigOperators MatrixGroups
open ActualContinuousSpatialProfiles20261110 ActualContinuousPoincarePairing20261110
open ActualOrdinaryContinuousModes20261110 ActualContinuousClassFourier20261110
open ActualYoungFormalClass20261110 ActualCriticalCuspEvaluation20261110
open ActualCuspDenominatorClasses20261110 ActualYoungCriticalProjection20261110
open OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open ActualYoungCriticalCusps20261110 Gamma0QuotientCellPushforward20261025a
open CompactCuspParabolicL220261025a NormalizedCuspCompactPoincare20261026b
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open P3NativePeriod64SamplingSourceOnly (D4)

def scaledSeed (m : ℤ) (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((Real.sqrt |(m : ℝ)| : ℝ) : ℂ)⁻¹ * ψ (|(m : ℝ)|*y)

theorem scaled_test (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Continuous (scaledSeed m ψ) ∧ HasCompactSupport (scaledSeed m ψ) ∧
      tsupport (scaledSeed m ψ) ⊆ Ioi (0 : ℝ) := by
  let c := |(m : ℝ)|
  have hC : 0 < c := abs_pos.mpr (by exact_mod_cast hm)
  let g := fun y : ℝ => ψ (c*y)
  have hg : HasCompactSupport g := hc.comp_smul hC.ne'
  have hs : tsupport g = (fun y : ℝ => c*y) ⁻¹' tsupport ψ :=
    tsupport_comp_eq_preimage ψ (Homeomorph.smulOfNeZero c hC.ne')
  refine ⟨continuous_const.mul (hψ.comp (continuous_const.mul continuous_id)),hg.mul_left,?_⟩
  intro y hy
  have hgy : y ∈ tsupport g := tsupport_mul_subset_right hy
  rw [hs] at hgy
  exact (mul_pos_iff_of_pos_left hC).mp (hpos hgy)

def orderRadial (m : ℤ) (ν : ℂ) (y : ℝ) : ℂ :=
  2*(Real.sqrt y : ℂ)*ComplexOrderKBridgeSourceOnly.complexOrderK ν (2*Real.pi*|(m : ℝ)|*y)

def orderProbe (m : ℤ) (ψ : ℝ → ℂ) (ν : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ y)*orderRadial m ν y)

/-- The true y⁻²dy and the sqrt(y) in the K Fourier expansion both
enter the factor |m|⁻¹/². No division by a Fourier transform occurs. -/
theorem common_orderProbe (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (ν : ℂ) :
    orderProbe m (scaledSeed m ψ) ν = orderProbe 1 ψ ν := by
  let c := |(m : ℝ)|
  have hC : 0 < c := abs_pos.mpr (by exact_mod_cast hm)
  let F := fun u : ℝ => ((u⁻¹)^2 : ℝ) • (star (ψ u)*orderRadial 1 ν u)
  have sub := integral_comp_mul_left_Ioi' F 0 hC
  rw [mul_zero] at sub
  have jac (y : ℝ) (hy : 0 < y) :
      (y⁻¹)^2*(Real.sqrt c)⁻¹*(2*Real.sqrt y) =
        c*((c*y)⁻¹)^2*(2*Real.sqrt (c*y)) := by
    rw [Real.sqrt_mul hC.le]
    field_simp [hC.ne',hy.ne',(Real.sqrt_pos.mpr hC).ne']
    <;> ring_nf <;> simp [Real.sq_sqrt hC.le] <;> ring
  change (∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (scaledSeed m ψ y)*orderRadial m ν y)) =
    ∫ u in Ioi (0 : ℝ), F u
  rw [← sub,← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have harg : 2*Real.pi*|(m : ℝ)|*y = 2*Real.pi*(c*y) := by dsimp [c]; ring
  have hJ := congrArg (fun r : ℝ => (r : ℂ)) (jac y hy)
  push_cast at hJ
  let K := ComplexOrderKBridgeSourceOnly.complexOrderK ν (2*Real.pi*(c*y))
  calc
    _ = ((((y : ℂ)⁻¹)^2 * (Real.sqrt c : ℂ)⁻¹) * (2*(Real.sqrt y : ℂ))) * (star (ψ (c*y))*K) := by
      simp only [scaledSeed,orderRadial,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv,harg,
        star_mul,Complex.star_def,map_inv₀,Complex.conj_ofReal,K,c]
      ring
    _ = (((c : ℂ)*(((c : ℂ)*(y : ℂ))⁻¹)^2)*(2*(Real.sqrt (c*y) : ℂ))) * (star (ψ (c*y))*K) := by rw [hJ]
    _ = c • F (c*y) := by
      simp only [F,orderRadial,Int.cast_one,abs_one,mul_one,Complex.real_smul,Complex.ofReal_pow,
        Complex.ofReal_inv,Complex.ofReal_mul,K]
      ring

theorem common_radialProbe (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (t : ℝ) :
    radialProbe m (scaledSeed m ψ) t = radialProbe 1 ψ t :=
  common_orderProbe m hm ψ (criticalPoint t-1/2)

/-- Spatial packet coefficients are conjugated because the actual
test pairing is conjugate-linear in its Poincare vector. -/
def packet (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (ψ : ℝ → ℂ) (u : Gamma0OrbitSpace N) : ℂ :=
  ∑ b ∈ S,star (w b)*originalPoincare N one (ind b) (scaledSeed (ind b) ψ) u

def spectrum (N : ℕ) [NeZero N] (V : Gamma0OrbitSpace N → ℂ) (a : Parameters N) (t : ℝ) : ℂ :=
  ∫ u, star (V u)*quotientProfile a t u ∂carrierPushforward N

theorem packet_L2 (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (hn : ∀ b ∈ S, ind b ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) : MemLp (packet N one S w ind ψ) 2 (carrierPushforward N) := by
  apply memLp_finsetSum S
  intro b hb
  obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hpos
  apply MemLp.const_mul'
  cases one
  · exact compactCuspPoincare_memLp_two N (ind b) _ h₁ h₂ h₃
  · exact framePoincare_memLp_two N (NeZero.pos N) Gamma0ActualCuspsSourceOnly.cuspOneMatrix (ind b) _ h₁ h₂ h₃

theorem packet_spectrum (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (hn : ∀ b ∈ S, ind b ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (a : Parameters N) (t : ℝ) :
    Integrable (fun u => star (packet N one S w ind ψ u)*quotientProfile a t u) (carrierPushforward N) ∧
    spectrum N (packet N one S w ind ψ) a t =
      radialProbe 1 ψ t*markedRow S w ind (fun n => nativeR a one n t) := by
  let P := fun b => originalPoincare N one (ind b) (scaledSeed (ind b) ψ)
  let E := quotientProfile a t
  have H (b : ℕ) (hb : b ∈ S) :
      Integrable (fun u => star (P b u)*E u) (carrierPushforward N) ∧
      (∫ u,star (P b u)*E u ∂carrierPushforward N) = radialProbe 1 ψ t*nativeR a one (ind b) t := by
    obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hpos
    simpa only [P,E,common_radialProbe (ind b) (hn b hb)] using
      original_spatial_pairing a one (ind b) (hn b hb) _ h₁ h₂ h₃ t
  have hsum (u : Gamma0OrbitSpace N) : star (packet N one S w ind ψ u)*E u =
      ∑ b ∈ S,w b*(star (P b u)*E u) := by
    simp only [packet,star_sum,star_mul,star_star,Finset.sum_mul,P]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hI (b : ℕ) (hb : b ∈ S) : Integrable (fun u => w b*(star (P b u)*E u)) (carrierPushforward N) :=
    (H b hb).1.const_mul _
  change Integrable (fun u => star (packet N one S w ind ψ u)*E u) _ ∧
    (∫ u, star (packet N one S w ind ψ u)*E u ∂_) = _
  simp_rw [hsum]
  refine ⟨integrable_finsetSum S hI,?_⟩
  rw [integral_finsetSum S hI,markedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_const_mul,(H b hb).2]
  ring

def mPacket (N : ℕ) [NeZero N] (J j : ℕ) (ell : D4 → ℤ) (ψ : ℝ → ℂ) : Gamma0OrbitSpace N → ℂ :=
  packet N false (commonMBlock J j) (fun p => star ((commonPoissonCompleted J j (ell 1)).weight p))
    (fun p => (p : ℤ)) ψ

def nPacket (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) (φ : ℝ → ℂ) : Gamma0OrbitSpace z.val → ℂ :=
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  packet z.val true (nCarrier D k z.val) (traceBeta D r k upper negativeM ell z.val)
    (traceIndex D k negativeM z.val) φ

/-- The native-cusp covariance of the two actual spatial test packets
is the manuscript's original continuous numerator times the two true
common probes. With this conjugate-first convention its first factor
is conjugate(<P_M,E>), and the second is <P_N,E>. -/
theorem original_packet_covariance (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    MemLp (mPacket z.val J j ell ψ) 2 (carrierPushforward z.val) ∧
    MemLp (nPacket D r k z upper negativeM ell φ) 2 (carrierPushforward z.val) ∧
    nativeProduct z.val (fun a => spectrum z.val (mPacket z.val J j ell ψ) a t)
      (fun a => spectrum z.val (nPacket D r k z upper negativeM ell φ) a t) =
      (star (radialProbe 1 ψ t)*radialProbe 1 φ t)*
        classProduct z.val (fun i => M J j ell (fun n => channelR i false n t))
          (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  have hm (p : ℕ) (hp : p ∈ commonMBlock J j) : (p : ℤ) ≠ 0 := by
    have hpos := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) j) (Finset.mem_Ico.mp hp).1
    exact_mod_cast hpos.ne'
  have hn (n : ℕ) (hn : n ∈ nCarrier D k z.val) : traceIndex D k negativeM z.val n ≠ 0 :=
    Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z.val hn ha)
  refine ⟨packet_L2 _ _ _ _ _ hm ψ hψ hcψ hpψ,packet_L2 _ _ _ _ _ hn φ hφ hcφ hpφ,?_⟩
  have hM (a : Parameters z.val) : spectrum z.val (mPacket z.val J j ell ψ) a t =
      radialProbe 1 ψ t*M J j ell (fun n => nativeR a false n t) :=
    (packet_spectrum _ _ _ _ _ hm ψ hψ hcψ hpψ a t).2
  have hN (a : Parameters z.val) : spectrum z.val (nPacket D r k z upper negativeM ell φ) a t =
      radialProbe 1 φ t*source D r k z upper negativeM ell (fun n => nativeR a true n t) :=
    (packet_spectrum _ _ _ _ _ hn φ hφ hcφ hpφ a t).2
  rw [original_projected_product D r k z upper negativeM J j ell t]
  simp only [nativeProduct,hM,hN,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end ImbalancedChen.Part3.OriginalContinuousPoincarePackets20261110
