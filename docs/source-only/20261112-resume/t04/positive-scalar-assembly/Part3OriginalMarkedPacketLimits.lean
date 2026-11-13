import ImbalancedChen.Part3OriginalPositiveRegularPrice
import ImbalancedChen.Part3ActualMarkedCubicPrice
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Batteries.Tactic.OpenPrivate

/-! The two limits at the original pair of marked rows. Each complementary
slot is priced at its actual order on its finite fixed-level subspace. -/
namespace ImbalancedChen.Part3.OriginalMarkedPacketLimits20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveNativeDiagonal20261112 ActualUnitBandSpectralMass20261112
open ActualMarkedCubicPrice20261112 ActualPrescribedPositiveJ20261112
open ActualPositiveScalarPacket20261112 ActualPositiveSmallHeightWaves20261112 (radius)
open OriginalPositiveRatioWindows20261112 OriginalPositiveResponseLimit20261112 OriginalPositiveRegularPrice20261112
open ActualFullCuspEigenbasis20261026b ActualCuspDenominatorClasses20261110 ActualCuspBasisIndexCounting20261026b
open ActualCuspBasisWhittakerCoefficients20261102 ActualContinuousPoincarePairing20261110 ActualContinuousClassFourier20261110
open OriginalNativeCuspFunctionals20261102 OriginalSimultaneousPrefixCompletion20261102 OriginalCommonPoissonLanes20261102
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102
open OriginalTwoZFourierAssembly20261102 OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110
open OriginalMarkedArithmeticTrace20261112 OriginalContinuousPoincarePackets20261110
open private product_le from ImbalancedChen.Part3ActualMarkedSpectralMajorants
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private covariance_measurable from ImbalancedChen.Part3OriginalPrescribedSpectralConvergence

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)

local instance levelNZ : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
local notation "Idx" => actualCuspBasisIndex z.val (NeZero.pos z.val)

def dMark (i : Idx) : ℂ := star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
  originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i
def cMark (t : ℝ) := nativeProduct z.val (fun a => M J j ell (fun h => nativeR a false h t))
    (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))

local notation "d₀" => dMark D r k z upper negativeM J j ell
local notation "c₀" => cMark D r k z upper negativeM J j ell

theorem marked_prices (ha : D.block.atom.residue≠0) :
    Summable (fun i : Idx => slotPrice z.val i*‖d₀ i‖) ∧ Integrable (fun t => linePrice t*‖c₀ t‖) := by
  let S := commonMBlock J j
  let T := nCarrier D k z.val
  let w := fun p => star ((commonPoissonCompleted J j (ell 1)).weight p)
  let b := traceBeta D r k upper negativeM ell z.val
  let f := fun p : ℕ => (p:ℤ)
  let l := traceIndex D k negativeM z.val
  let X := fun t (a : Parameters z.val) => M J j ell (fun h => nativeR a false h t)
  let Z := fun t (a : Parameters z.val) => source D r k z upper negativeM ell (fun h => nativeR a true h t)
  have A := discrete_mark z.val (originalFrame false) S w f (common_nonzero J j)
  have B := discrete_mark z.val (originalFrame true) T b l (row_nonzero D k z ha negativeM)
  constructor
  · apply (A.add B).of_nonneg_of_le (fun i => mul_nonneg (slotPrice_nn _ _) (norm_nonneg _))
    intro i
    rw [dMark,norm_mul,norm_star,←mul_add]
    exact mul_le_mul_of_nonneg_left (product_le _ _) (slotPrice_nn _ _)
  have I := cont_budget_L1 z.val false S w f (common_nonzero J j)
  have L := cont_budget_L1 z.val true T b l (row_nonzero D k z ha negativeM)
  have cm := covariance_measurable D r k z ha upper negativeM J j ell
  have price_cont : Continuous linePrice := by unfold linePrice cubic; fun_prop (disch:=positivity)
  apply (I.add L).mono' (price_cont.aestronglyMeasurable.mul cm.norm)
  exact ae_of_all _ fun t => by
    rw [Real.norm_of_nonneg (mul_nonneg (linePrice_pos _).le (norm_nonneg _))]
    have e : linePrice t*‖c₀ t‖=(linePrice t/(4*Real.pi))*‖∑ a,star (X t a)*Z t a‖ := by
      rw [cMark,nativeProduct,← Finset.sum_div,norm_div]
      simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
      ring
    rw [e]
    have p : ‖∑ a,star (X t a)*Z t a‖≤(∑ a,‖X t a‖^2)+(∑ a,‖Z t a‖^2) := by
      rw [← Finset.sum_add_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by rw [norm_mul,norm_star]; exact product_le _ _)
    apply (mul_le_mul_of_nonneg_left p (div_nonneg (linePrice_pos t).le (by positivity))).trans
    rw [mul_add]
    exact add_le_add (cont_mark z.val false S w f t) (cont_mark z.val true T b l t)

def total (d : Idx→ℂ) (c : ℝ→ℂ) :=
  (∑' i,d i*d₀ i)+(∫ t : ℝ,c t*c₀ t)

def orderTotal (W : ℂ→ℂ) := total D r k z upper negativeM J j ell
  (fun i => W (basisOrder z.val (NeZero.pos z.val) i)) (fun t => W ((t:ℂ)*I))

private theorem price_div {C t : ℝ} {a : ℂ} (h : (1+|t|)^3*Real.cosh (Real.pi*t)*‖a‖≤C) :
    ‖a‖≤C*linePrice t := by
  have b : 0<(1+|t|)^3*Real.cosh (Real.pi*t) := mul_pos (by positivity) (Real.cosh_pos _)
  calc
    _ ≤ C/((1+|t|)^3*Real.cosh (Real.pi*t)) := (le_div_iff₀ b).mpr (by simpa only [mul_comm ‖a‖] using h)
    _ = _ := by simp only [linePrice,cubic,div_eq_mul_inv,mul_inv_rev,one_mul]; ring

private theorem dominated (ha : D.block.atom.residue≠0) (W : ℕ→ℂ→ℂ) (d : Idx→ℂ) (c : ℝ→ℂ)
    (md : ∀ i,Tendsto (fun n => W n (basisOrder z.val (NeZero.pos z.val) i)) atTop (𝓝 (d i)))
    (mc : ∀ t : ℝ,Tendsto (fun n => W n ((t:ℂ)*I)) atTop (𝓝 (c t)))
    (m : ∀ n,AEStronglyMeasurable (fun t : ℝ => W n ((t:ℂ)*I)) volume)
    (price : ∃ C : ℝ,0≤C ∧ ∀ᶠ n in atTop,∀ t : ℝ,(1+|t|)^3*Real.cosh (Real.pi*t)*‖W n ((t:ℂ)*I)‖≤C) :
    Tendsto (fun n => orderTotal D r k z upper negativeM J j ell (W n)) atTop
      (𝓝 (total D r k z upper negativeM J j ell d c)) := by
  obtain ⟨D0,C0,p⟩ := price
  obtain ⟨S,L⟩ := marked_prices D r k z upper negativeM J j ell ha
  let E := {i : Idx | exceptional z.val i}
  have fin : E.Finite := (actualCuspIndexSublevel_finite z.val (NeZero.pos z.val) (1/4)).subset fun i hi => hi.le
  let B := fun i : Idx => if i∈E then (‖d i‖+1)*‖d₀ i‖ else 0
  have sb : Summable B := summable_of_hasFiniteSupport (fin.subset (fun i hi =>
    by by_contra hx; exact hi (if_neg hx)))
  have phase : ∀ᶠ n in atTop,∀ i∈E,‖W n (basisOrder z.val (NeZero.pos z.val) i)‖≤‖d i‖+1 :=
    (eventually_all_finite fin).2 fun i _ => ((md i).norm.eventually (eventually_lt_nhds (lt_add_of_pos_right _ zero_lt_one))).mono fun _ h => h.le
  have DS := tendsto_tsum_of_dominated_convergence ((S.mul_left D0).add sb)
    (fun i => (md i).mul_const (d₀ i)) (by
      filter_upwards [p,phase] with n P Fin i
      rw [norm_mul]
      by_cases hi : i∈E
      · simpa only [Pi.add_apply,B,if_pos hi,slotPrice,if_pos (show exceptional z.val i from hi),mul_zero,zero_mul,zero_add] using
          mul_le_mul_of_nonneg_right (Fin i hi) (norm_nonneg _)
      · have o := order_regular z.val hi
        simpa only [Pi.add_apply,B,if_neg hi,add_zero,slotPrice,if_neg (show ¬exceptional z.val i from hi),o,mul_assoc] using
          mul_le_mul_of_nonneg_right (price_div (P (height z.val i))) (norm_nonneg (d₀ i)))
  have M := covariance_measurable D r k z ha upper negativeM J j ell
  have CS := tendsto_integral_filter_of_dominated_convergence (fun t => D0*(linePrice t*‖c₀ t‖))
    (Eventually.of_forall (fun n => (m n).mul M)) (p.mono (fun n P => ae_of_all _ fun t => by
      rw [norm_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (price_div (P t)) (norm_nonneg _)))
    (L.const_mul D0) (ae_of_all _ fun t => (mc t).mul_const (c₀ t))
  exact DS.add CS

private theorem basis_range (i : Idx) : |(basisOrder z.val (NeZero.pos z.val) i).re|≤radius := by
  by_cases h : exceptional z.val i
  · obtain ⟨a,ha,e⟩ := order_exceptional z.val h
    rw [e,ofReal_re,abs_of_nonneg ha.1]; norm_num [radius] at *; linarith [ha.2]
  · rw [order_regular z.val h]; simp [radius,Complex.mul_re]

private theorem regular_packet (n : ℕ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    Tendsto (fun R : ℕ => packet unit (ratio ell hY n) R ((t:ℂ)*I)) atTop
      (𝓝 (response (ratio ell hY n) ((t:ℂ)*I))) :=
  (packet_limit unit _ unit_mass (ratio_zero ell hY n) (by simp [radius,Complex.mul_re])).comp tendsto_natCast_atTop_atTop

theorem product_limit (ha : D.block.atom.residue≠0) {Y : ℝ} (hY : 0<Y) (n : ℕ) :
    Tendsto (fun R : ℕ => orderTotal D r k z upper negativeM J j ell (packet unit (ratio ell hY n) R)) atTop
      (𝓝 (orderTotal D r k z upper negativeM J j ell (response (ratio ell hY n)))) := by
  obtain ⟨C,R₀,c,H⟩ := packet_regular_price unit _ unit_mass (ratio_zero ell hY n)
  apply dominated D r k z upper negativeM J j ell ha
  · exact fun i => (packet_limit unit _ unit_mass (ratio_zero ell hY n) (basis_range D k z i)).comp tendsto_natCast_atTop_atTop
  · exact regular_packet ell n hY
  · exact fun R => (line_meas _ _ _).aestronglyMeasurable
  · exact ⟨C,c,(tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R₀)).mono fun R h => H _ h⟩

theorem ratio_limit (ha : D.block.atom.residue≠0) {Y : ℝ} (hY : 0<Y) :
    Tendsto (fun n => orderTotal D r k z upper negativeM J j ell (response (ratio ell hY n))) atTop
      (𝓝 (total D r k z upper negativeM J j ell (nativeWeight z.val (spectralTest ell Y))
        (fun t => positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ)))) := by
  apply dominated D r k z upper negativeM J j ell ha
  · intro i
    by_cases hi : exceptional z.val i
    · have ⟨a,b,_⟩ := complementary_range z.val hi
      have o : basisOrder z.val (NeZero.pos z.val) i=(complementaryHeight z.val i:ℂ) := if_pos hi.le
      rw [nativeWeight,if_pos hi,o]
      exact exceptional_limit ell hY a b
    · rw [nativeWeight,if_neg hi,order_regular z.val hi]
      exact regular_limit ell hY _
  · exact regular_limit ell hY
  · exact fun n => aestronglyMeasurable_of_tendsto_ae (atTop:Filter ℕ)
      (fun R => (line_meas unit (ratio ell hY n) R).aestronglyMeasurable) (ae_of_all _ (regular_packet ell n hY))
  · obtain ⟨C,c,H⟩ := response_regular_price ell hY
    exact ⟨C,c,Eventually.of_forall H⟩

end
end ImbalancedChen.Part3.OriginalMarkedPacketLimits20261112
