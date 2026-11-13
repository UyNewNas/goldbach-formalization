import ImbalancedChen.Part3OriginalSameInfinityScalarPrices

/-! Take the height limit followed by the window limit on the native
same-infinity spectrum, at the fixed literal period-64 test. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityFixedScalarTrace20261113
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Classical BigOperators MatrixGroups
open OriginalSameInfinityScalarPrices20261113 OriginalSameInfinityTensorSpectrum20261113
open OriginalSameInfinityScalarTensor20261113 (pair)
open OriginalSameInfinityScalarLimits20261113 (target scalar_limits)
open P3NativePeriod64SamplingSourceOnly (D4) P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102 ActualCuspBasisIndexCounting20261026b
open ActualPositiveNativeDiagonal20261112 ActualUnitBandSpectralMass20261112 ActualMarkedCubicPrice20261112
open ActualPrescribedPositiveJ20261112 ActualPositiveScalarPacket20261112
open ActualPositiveSmallHeightWaves20261112 (radius)
open OriginalPositiveRatioWindows20261112 OriginalPositiveResponseLimit20261112 OriginalPositiveRegularPrice20261112
open private price_div regular_packet from ImbalancedChen.Part3OriginalMarkedPacketLimits

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩
variable (q m n : ℕ+)
local notation "Idx" => actualCuspBasisIndex q.val (NeZero.pos q.val)

def total (d : Idx→ℂ) (c : ℝ→ℂ) :=
  (∑' i,d i*disc q m n i)+(∫ t : ℝ,c t*cont q m n t)

private theorem dominated (W : ℕ→ℂ→ℂ) (d : Idx→ℂ) (c : ℝ→ℂ)
    (md : ∀ i,Tendsto (fun k => W k (basisOrder q.val (NeZero.pos q.val) i)) atTop (𝓝 (d i)))
    (mc : ∀ t : ℝ,Tendsto (fun k => W k ((t:ℂ)*I)) atTop (𝓝 (c t)))
    (meas : ∀ k,AEStronglyMeasurable (fun t : ℝ => W k ((t:ℂ)*I)) volume)
    (price : ∃ C : ℝ,0≤C ∧ ∀ᶠ k in atTop,∀ t : ℝ,(1+|t|)^3*Real.cosh (Real.pi*t)*‖W k ((t:ℂ)*I)‖≤C) :
    Tendsto (fun k => orderSum q m n (W k)) atTop (𝓝 (total q m n d c)) := by
  obtain ⟨C,_,P⟩ := price
  obtain ⟨S,L⟩ := cubic_prices q m n
  let E := {i : Idx | exceptional q.val i}
  have finite : E.Finite := (actualCuspIndexSublevel_finite q.val (NeZero.pos q.val) (1/4)).subset
    (fun _ h => h.le)
  let B := fun i : Idx => if i∈E then (‖d i‖+1)*‖disc q m n i‖ else 0
  have sb : Summable B := summable_of_hasFiniteSupport (finite.subset (fun i hi =>
    by by_contra hx; exact hi (if_neg hx)))
  have phase : ∀ᶠ k in atTop,∀ i∈E,‖W k (basisOrder q.val (NeZero.pos q.val) i)‖≤‖d i‖+1 :=
    (eventually_all_finite finite).2 fun i _ => ((md i).norm.eventually
      (eventually_lt_nhds (lt_add_of_pos_right _ zero_lt_one))).mono fun _ h => h.le
  have DS := tendsto_tsum_of_dominated_convergence ((S.mul_left C).add sb)
    (fun i => (md i).mul_const (disc q m n i)) (by
      filter_upwards [P,phase] with k p f i
      rw [norm_mul]
      by_cases hi : i∈E
      · simpa only [Pi.add_apply,B,if_pos hi,slotPrice,if_pos (show exceptional q.val i from hi),
          mul_zero,zero_mul,zero_add] using mul_le_mul_of_nonneg_right (f i hi) (norm_nonneg _)
      · have o := order_regular q.val hi
        simpa only [Pi.add_apply,B,if_neg hi,add_zero,slotPrice,if_neg (show ¬exceptional q.val i from hi),o,
          mul_assoc] using mul_le_mul_of_nonneg_right (price_div (p (height q.val i))) (norm_nonneg (disc q m n i)))
  have I := tendsto_integral_filter_of_dominated_convergence (fun t => C*(linePrice t*‖cont q m n t‖))
    (Eventually.of_forall (fun k => (meas k).mul (covariance_meas q m n))) (P.mono (fun k p => ae_of_all _ fun t => by
      rw [norm_mul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (price_div (p t)) (norm_nonneg _)))
    (L.const_mul C) (ae_of_all _ fun t => (mc t).mul_const (cont q m n t))
  exact DS.add I

private theorem order_range (i : Idx) : |(basisOrder q.val (NeZero.pos q.val) i).re|≤radius := by
  by_cases h : exceptional q.val i
  · obtain ⟨a,ha,e⟩ := order_exceptional q.val h
    rw [e,ofReal_re,abs_of_nonneg ha.1]
    dsimp only [radius]
    linarith only [ha.2]
  · rw [order_regular q.val h]
    simp [radius,Complex.mul_re]

theorem fixed_scalar_trace (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) :
    target ell Y q m n=total q m n (nativeWeight q.val (spectralTest ell Y))
      (fun t => positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ)) := by
  have G := scalar_limits ell yp q m n
  have eq (j : ℕ) : OriginalSameInfinityScalarLimits20261113.window ell yp j q m n=
      orderSum q m n (response (ratio ell yp j)) := by
    have H : Tendsto (fun R : ℕ => orderSum q m n (packet unit (ratio ell yp j) R)) atTop
        (𝓝 (orderSum q m n (response (ratio ell yp j)))) := by
      obtain ⟨C,R₀,c,p⟩ := packet_regular_price unit _ unit_mass (ratio_zero ell yp j)
      apply dominated q m n
      · exact fun i => (packet_limit unit _ unit_mass (ratio_zero ell yp j)
          (order_range q i)).comp tendsto_natCast_atTop_atTop
      · exact regular_packet ell j yp
      · exact fun R => (line_meas _ _ _).aestronglyMeasurable
      · exact ⟨C,c,(tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R₀)).mono fun R h => p _ h⟩
    apply tendsto_nhds_unique ((G.2.2.2.1 j).comp tendsto_natCast_atTop_atTop)
    exact H.congr' (Eventually.of_forall (fun R : ℕ => (compact_scalar unit (ratio ell yp j) R q m n).symm))
  have H : Tendsto (fun j => orderSum q m n (response (ratio ell yp j))) atTop
      (𝓝 (total q m n (nativeWeight q.val (spectralTest ell Y))
        (fun t => positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ)))) := by
    apply dominated q m n
    · intro i
      by_cases hi : exceptional q.val i
      · obtain ⟨hp,lt,_⟩ := complementary_range q.val hi
        have o : basisOrder q.val (NeZero.pos q.val) i=(complementaryHeight q.val i:ℂ) := if_pos hi.le
        rw [nativeWeight,if_pos hi,o]
        exact exceptional_limit ell yp hp lt
      · rw [nativeWeight,if_neg hi,order_regular q.val hi]
        exact regular_limit ell yp _
    · exact regular_limit ell yp
    · exact fun j => aestronglyMeasurable_of_tendsto_ae (atTop:Filter ℕ)
        (fun R => (line_meas unit (ratio ell yp j) R).aestronglyMeasurable) (ae_of_all _ (regular_packet ell j yp))
    · obtain ⟨C,c,h⟩ := response_regular_price ell yp
      exact ⟨C,c,Eventually.of_forall h⟩
  exact tendsto_nhds_unique G.2.2.2.2 (H.congr' (Eventually.of_forall fun j => (eq j).symm))

end
end ImbalancedChen.Part3.OriginalSameInfinityFixedScalarTrace20261113
