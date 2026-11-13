import ImbalancedChen.Part3OriginalCuspHitPacking
import ImbalancedChen.Part3OriginalUnitStripPacketMass
import ImbalancedChen.Part3ActualSingleModeSpectralEnergy

/-! Finite-hit Cauchy followed by nonnegative unfolding of the complete
polynomial on the actual quotient with its native hyperbolic measure. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHighStripPacketBudget20261113
open Set Filter MeasureTheory UpperHalfPlane Complex
open scoped MatrixGroups UpperHalfPlane BigOperators ENNReal
open OriginalCuspHitPacking20261112 OriginalExceptionalHeightWindow20261112
open OriginalUnitStripPacketMass20261113 ActualContinuousPoincarePairing20261110
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactSeedSharpL2Budget20261025a ActualSignedPoincareEnvelope20261112
open Gamma0ActualConstantMode20261025a NormalizedCuspCompactPoincare20261026b

def overlap (N : ℕ) (Y : ℝ) : ℝ := 2+4/((N:ℝ)*Y)

theorem overlap_nonneg (N : ℕ) {Y : ℝ} (hY : 0<Y) : 0≤overlap N Y := by
  unfold overlap; positivity

private theorem finite_cauchy {ι : Type*} (S : Finset ι) (v : ι→ℂ) :
    ‖∑ i∈S,v i‖^2 ≤ (S.card:ℝ)*∑ i∈S,‖v i‖^2 := by
  have t := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2
  exact t.trans (by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖v i‖))

/-- Sharp multiplicity from the two original normalized cusps replaces the
non-quantitative compact transporter count in the original unfolding. -/
private theorem pointwise (N : ℕ) (hN : 0<N) (one : Bool) {Y : ℝ} (hY : 0<Y)
    (f : ℍ→ℂ) (w : ℍ)
    (off : ∀ i, i∉hits N hN one Y w → translatedSeed N f i w=0) :
    ENNReal.ofReal (‖complexSeedTrace N f w‖^2) ≤
      ENNReal.ofReal (overlap N Y)*fullSeedTrace N (seedSquareMass f) w := by
  classical
  let F := hits_finite N hN one hY w
  let S := F.toFinset
  have zero (i) (hi : i∉S) := off i (fun h => hi (F.mem_toFinset.mpr h))
  have card : (S.card:ℝ)≤overlap N Y := count_hits N hN one hY w S
    (fun _ h => F.mem_toFinset.mp h)
  have tr : complexSeedTrace N f w = ∑ i∈S,translatedSeed N f i w := tsum_eq_sum zero
  have mass : fullSeedTrace N (seedSquareMass f) w =
      ∑ i∈S,ENNReal.ofReal (‖translatedSeed N f i w‖^2) := by
    apply tsum_eq_sum
    intro i hi
    change ENNReal.ofReal (‖translatedSeed N f i w‖^2)=0
    simp [zero i hi]
  rw [tr,mass,← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (overlap_nonneg N hY)]
  exact ENNReal.ofReal_le_ofReal ((finite_cauchy S _).trans
    (mul_le_mul_of_nonneg_right card (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

private theorem frame_mode_off (N : ℕ) (hN : 0<N) (one : Bool) {H L : ℝ}
    (hH : 0<H) (hL : 0<L) {m : ℤ} (lo : L≤|(m:ℝ)|) (hi : |(m:ℝ)|≤2*L)
    (w : ℍ) (i : effectiveGamma0 N) (outside : i∉hits N hN one (bottom H L) w) :
    translatedSeed N (physicalFrameSeed N hN (originalFrame one) m (seed (H*|(m:ℝ)|)).toFun) i w=0 :=
  mode_off hH hL lo hi outside

private theorem frame_packet_off (N : ℕ) (hN : 0<N) (one : Bool) {H L : ℝ}
    (hH : 0<H) (hL : 0<L) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) (w : ℍ) (i : effectiveGamma0 N)
    (outside : i∉hits N hN one (bottom H L) w) :
    translatedSeed N (framePacket N hN (originalFrame one) H s a) i w=0 :=
  Finset.sum_eq_zero (fun m hm => mul_eq_zero_of_right _ (frame_mode_off N hN one hH hL
    (band m hm).1 (band m hm).2 w i outside))

theorem quotient_mass (N : ℕ) [NeZero N] (one : Bool) {H L : ℝ} (hH : 0<H) (hL : 0<L)
    (s : Finset ℤ) (a : ℤ→ℂ) (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    (∫⁻ q,ENNReal.ofReal (‖complexPoincare N (framePacket N (NeZero.pos N) (originalFrame one) H s a) q‖^2)
      ∂carrierPushforward N) ≤ ENNReal.ofReal (overlap N (bottom H L)*(4*coeffMass s a)) := by
  let f := framePacket N (NeZero.pos N) (originalFrame one) H s a
  let Y := bottom H L
  let k := ENNReal.ofReal (overlap N Y)
  have hy := bottom_pos hH hL
  have fm := seedSquareMass_measurable f (framePacket_measurable N _ _ H s a)
  rw [quotient_squareMass_eq_carrier]
  calc
    _ ≤ ∫⁻ w in reducedCarrier N,k*fullSeedTrace N (seedSquareMass f) w :=
      lintegral_mono (fun w => pointwise N (NeZero.pos N) one hy f w
        (frame_packet_off N _ one hH hL s a band w))
    _ = k*∫⁻ w in reducedCarrier N,fullSeedTrace N (seedSquareMass f) w :=
      lintegral_const_mul _ (fullSeedTrace_measurable N _ fm)
    _ = k*∫⁻ w : ℍ,seedSquareMass f w := by rw [← lintegral_fullSeedTrace N _ fm]
    _ ≤ k*ENNReal.ofReal (4*coeffMass s a) :=
      mul_le_mul_left' (physical_mass N _ _ hH hL s a band) k
    _ = _ := (ENNReal.ofReal_mul (overlap_nonneg N hy)).symm

def modeVector (N : ℕ) [NeZero N] (one : Bool) (H : ℝ) (m : ℤ) : QuotientL2 N :=
  let ξ := seed (H*|(m:ℝ)|)
  framedVector N (originalFrame one) m ξ.toFun ξ.continuous ξ.compact ξ.positive

def packetVector (N : ℕ) [NeZero N] (one : Bool) (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) :
    QuotientL2 N := ∑ m∈s,a m • modeVector N one H m

theorem packet_rep (N : ℕ) [NeZero N] (one : Bool) {H L : ℝ} (hH : 0<H) (hL : 0<L)
    (s : Finset ℤ) (a : ℤ→ℂ) (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    ⇑(packetVector N one H s a) =ᵐ[carrierPushforward N]
      complexPoincare N (framePacket N (NeZero.pos N) (originalFrame one) H s a) := by
  classical
  let g := originalFrame one
  let f := fun m => physicalFrameSeed N (NeZero.pos N) g m (seed (H*|(m:ℝ)|)).toFun
  let F := framePacket N (NeZero.pos N) g H s a
  have term (m : ℤ) : ⇑(a m • modeVector N one H m) =ᵐ[carrierPushforward N]
      (fun q => a m*complexPoincare N (f m) q) := by
    let ξ := seed (H*|(m:ℝ)|)
    filter_upwards [Lp.coeFn_smul (a m) (modeVector N one H m),
      framedVector_ae N g m ξ.toFun ξ.continuous ξ.compact ξ.positive] with q h h'
    change (a m • modeVector N one H m) q=a m*complexPoincare N (f m) q
    exact h.trans (congrArg (fun c : ℂ => a m*c) h')
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun m => a m • modeVector N one H m),
    ae_all_iff.mpr term,reducedProjection_range_ae N] with q h ha hq
  obtain ⟨w,rfl⟩ := hq
  refine h.trans ((Finset.sum_congr rfl (fun m _ => ha m)).trans ?_)
  simp only [complexPoincare_projection]
  let fin := hits_finite N (NeZero.pos N) one (bottom_pos hH hL) (w:ℍ)
  let T := fin.toFinset
  have off (i) (hi : i∉T) : i∉hits N (NeZero.pos N) one (bottom H L) w :=
    fun h => hi (fin.mem_toFinset.mpr h)
  have each (m) (hm : m∈s) : complexSeedTrace N (f m) w =
      ∑ i∈T,translatedSeed N (f m) i w :=
    tsum_eq_sum (fun i hi => frame_mode_off N _ one hH hL (band m hm).1 (band m hm).2 w i (off i hi))
  have whole : complexSeedTrace N F w=∑ i∈T,translatedSeed N F i w :=
    tsum_eq_sum (fun i hi => frame_packet_off N _ one hH hL s a band w i (off i hi))
  rw [whole]
  calc
    _ = ∑ m∈s,∑ i∈T,a m*translatedSeed N (f m) i w := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [each m hm,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem packet_norm_budget (N : ℕ) [NeZero N] (one : Bool) {H L : ℝ} (hH : 0<H) (hL : 0<L)
    (s : Finset ℤ) (a : ℤ→ℂ) (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    ‖packetVector N one H s a‖^2 ≤ overlap N (bottom H L)*(4*coeffMass s a) := by
  let v := packetVector N one H s a
  have eq := packet_rep N one hH hL s a band
  have h := quotient_mass N one hH hL s a band
  have id : ENNReal.ofReal (‖v‖^2) =
      ∫⁻ q,ENNReal.ofReal (‖complexPoincare N (framePacket N (NeZero.pos N) (originalFrame one) H s a) q‖^2)
        ∂carrierPushforward N := by
    rw [← lp_square_integral v,ofReal_integral_eq_lintegral_ofReal
      (v.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)) (ae_of_all _ fun _ => sq_nonneg _)]
    exact lintegral_congr_ae (eq.mono (fun _ e => by rw [e]))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (overlap_nonneg N (bottom_pos hH hL))
    (mul_nonneg (by norm_num) (coeffMass_nonneg s a)))).mp (id.le.trans h)

end ImbalancedChen.Part3.OriginalHighStripPacketBudget20261113
end
