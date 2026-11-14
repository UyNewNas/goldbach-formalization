import ImbalancedChen.Part3OriginalRegularInfinityDyadic
import ImbalancedChen.Part3ActualCuspOneGeometricPairing

/-! Isometric transport of the very same compact physical packet, at
negative frequency and at the manuscript's Fricke-related observation. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPhysicalTransport20261113
open Set Filter MeasureTheory Complex UpperHalfPlane Finset
open scoped UpperHalfPlane MatrixGroups
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalRegularPreKuznetsovPolar20261113 (physical compact_profile)
open OriginalRegularCompactCoordinates20261113 (spatial)
open ActualUnitBandHeightSeeds20261112 (modulation window)
open ActualContinuousPoincarePairing20261110 (originalPoincare)
open OriginalContinuousPoincarePackets20261110 (packet packet_L2 scaledSeed scaled_test)
open ActualInfinityCuspAnnihilator20261026b (HeightSeed QuotientL2)
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0ActualParabolicUnfolding20261025a
open ActualInfinityKloostermanSeed20261025a (fourierRadialSeed)
open ActualFrickeQuotientMeasure20261026b (quotientFricke)
open ActualCuspOneGeometricPairing20261112 (one_zero_pair)
open P3Period64NativeReconstructionSourceOnly (e norm_e)
open private pulled_infinity fricke_measure from ImbalancedChen.Part3ActualCuspOneGeometricPairing
open private seed_memLp from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem radial_conj {y : ℝ} (hy : 0<y) (r : ℝ) (j : ℕ) :
    (compact r j).toFun y=star ((compact (-r) j).toFun y) := by
  change (OriginalRegularPreKuznetsovSeed20261113.seed (2*Real.pi) r j).toFun y=_
  have modE (u : ℝ) : star (modulation (-r) u)=modulation r u := by
    simp only [modulation,Complex.star_def,←Complex.exp_conj,map_mul,Complex.conj_ofReal,
      Complex.ofReal_neg,map_neg,Complex.conj_I]
    congr 1 <;> ring
  rw [compact_profile r j hy,show (compact (-r) j).toFun y=
    (window j (Real.log (2*Real.pi*y)):ℂ)*physical 0 (-r) y from compact_profile (-r) j hy]
  simp only [physical,star_mul',modE,Complex.star_def,Complex.conj_ofReal]

private theorem seed_conj (m : ℤ) (hm : m≠0) (r : ℝ) (j : ℕ) (z : ℍ) :
    fourierRadialSeed (-m) (scaledSeed (-m) (compact r j).toFun) z=
      star (fourierRadialSeed m (scaledSeed m (compact (-r) j).toFun) z) := by
  have h0 : 0<|(m:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  simp only [fourierRadialSeed,fourier_neg,scaledSeed,Int.cast_neg,abs_neg,
    star_mul',star_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [radial_conj (mul_pos h0 z.im_pos) r j] <;> rfl

private theorem negative_mode (q : ℕ+) (m : ℤ) (hm : m≠0) (r : ℝ) (j : ℕ) :
    originalPoincare q.val false (-m) (scaledSeed (-m) (compact r j).toFun)=ᵐ[carrierPushforward q.val]
      fun u => star (originalPoincare q.val false m (scaledSeed m (compact (-r) j).toFun) u) := by
  filter_upwards [reducedProjection_range_ae q.val] with u hu
  obtain ⟨z,rfl⟩ := hu
  change parabolicComplexPoincare _ _ (reducedProjection q.val z)=star (parabolicComplexPoincare _ _ (reducedProjection q.val z))
  simp only [parabolicComplexPoincare_projection,parabolicTraceComplex,tsum_star]
  exact tsum_congr (fun c => seed_conj m hm r j _)

theorem negative_norm (q : ℕ+) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ)
    (nf : ∀ i∈S,f i≠0) (r : ℝ) (j : ℕ) :
    ‖spatial q false S a (fun i => -f i) (fun i hi => neg_ne_zero.mpr (nf i hi)) (compact r j)‖=
    ‖spatial q false S (fun i => star (a i)) f nf (compact (-r) j)‖ := by
  let X := packet q.val false S a (fun i => -f i) (compact r j).toFun
  let Y := packet q.val false S (fun i => star (a i)) f (compact (-r) j).toFun
  have eq : X=ᵐ[carrierPushforward q.val] fun u => star (Y u) := by
    have h := ae_all_iff.mpr (fun i : ↥S => negative_mode q (f i.val) (nf i.val i.property) r j)
    filter_upwards [h] with u hu
    simp only [X,Y,packet,star_sum,star_mul',star_star]
    exact sum_congr rfl (fun i hi => by rw [hu ⟨i,hi⟩])
  unfold spatial
  rw [Lp.norm_toLp,Lp.norm_toLp]
  exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (eq.mono (fun u h => by
    change ‖X u‖=‖Y u‖
    rw [h,norm_star])))

def phase (q : ℕ+) (m : ℤ) := e ((m:ℝ)/q.val)
theorem phase_norm (q : ℕ+) (m : ℤ) : ‖phase q m‖=1 := norm_e _

private theorem pairing (q : ℕ+) (X : Gamma0OrbitSpace q.val→ℂ)
    (hx : MemLp X 2 (carrierPushforward q.val)) (v : QuotientL2 q.val) :
    inner ℂ (hx.toLp X) v=∫ u,star (X u)*v u ∂carrierPushforward q.val := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx.coeFn_toLp] with u hu
  simp only [RCLike.inner_apply',hu,Complex.star_def]

private theorem fricke_mode (q : ℕ+) (m : ℤ) (φ : ℝ→ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆Ioi (0:ℝ)) :
    originalPoincare q.val true m φ=ᵐ[carrierPushforward q.val] fun u =>
      star (phase q m)*originalPoincare q.val false m φ (quotientFricke q.val q.property u) := by
  let W := quotientFricke q.val q.property
  let X := originalPoincare q.val true m φ
  let Y := originalPoincare q.val false m φ
  let Z := fun u => star (phase q m)*(Y ∘ W) u
  have x := seed_memLp q.val true m φ hφ hc hp
  have y := seed_memLp q.val false m φ hφ hc hp
  have z : MemLp Z 2 (carrierPushforward q.val) := (y.comp_measurePreserving (fricke_measure q.val)).const_mul _
  have E : x.toLp X=z.toLp Z := by
    apply ext_inner_right ℂ
    intro v
    rw [pairing q X x v,pairing q Z z v]
    have T := one_zero_pair q.val m φ hφ hc hp v v.memLp
    have pull := pulled_infinity q.val m φ hc hp
    calc
      _=phase q m*∫ u,star (InfinityZeroActualQuotientGeometricAssembly20261026b.zeroCuspPoincare q.val q.property m φ hc hp u)*v u ∂carrierPushforward q.val := T
      _=_ := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards [pull] with u hu
        change _=star (star (phase q m)*Y (W u))*v u
        rw [star_mul',star_star]
        change Y (W u)=_ at hu
        rw [←hu]
        ring
  have h := x.coeFn_toLp.symm.trans (by rw [E];exact z.coeFn_toLp)
  exact h

theorem fricke_norm (q : ℕ+) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ)
    (nf : ∀ i∈S,f i≠0) (ψ : HeightSeed) :
    ‖spatial q true S a f nf ψ‖=‖spatial q false S (fun i => phase q (f i)*a i) f nf ψ‖ := by
  let X := packet q.val true S a f ψ.toFun
  let Y := packet q.val false S (fun i => phase q (f i)*a i) f ψ.toFun
  let W := quotientFricke q.val q.property
  have eq : X=ᵐ[carrierPushforward q.val] Y ∘ W := by
    have h := ae_all_iff.mpr (fun i : ↥S => by
      obtain ⟨c,k,p⟩ := scaled_test (f i.val) (nf i.val i.property) ψ.toFun ψ.continuous ψ.compact ψ.positive
      exact fricke_mode q (f i.val) _ c k p)
    filter_upwards [h] with u hu
    change (∑ i∈S,star (a i)*_)=∑ i∈S,star (phase q (f i)*a i)*_
    apply sum_congr rfl
    intro i hi
    rw [hu ⟨i,hi⟩,star_mul']
    ring
  have y := packet_L2 q.val false S (fun i => phase q (f i)*a i) f nf ψ.toFun ψ.continuous ψ.compact ψ.positive
  unfold spatial
  rw [Lp.norm_toLp,Lp.norm_toLp]
  exact congrArg ENNReal.toReal ((eLpNorm_congr_ae eq).trans
    (eLpNorm_comp_measurePreserving y.aestronglyMeasurable (fricke_measure q.val)))

end ImbalancedChen.Part3.OriginalRegularPhysicalTransport20261113
end

