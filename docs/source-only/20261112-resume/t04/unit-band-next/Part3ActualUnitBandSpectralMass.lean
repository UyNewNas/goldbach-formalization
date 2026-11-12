import ImbalancedChen.Part3ActualSingleModeSpectralEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Fixed-level unit-band masses with the actual native spectrum. -/
namespace ImbalancedChen.Part3.ActualUnitBandSpectralMass20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped MatrixGroups BigOperators Topology Classical
open ActualUnitBandMellinProbe20261112 ActualUnitBandHeightSeeds20261112 ActualUnitBandSeedBudget20261112
open ActualSingleModeSpectralEnergy20261112 ActualFullCuspEigenbasis20261026b
open ActualCuspEigenbasisNativeLabels20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def height (i : Idx) : ℝ := Real.sqrt (actualCuspNativeEigenvalue N (NeZero.pos N) i-1/4)
def exceptional (i : Idx) : Prop := actualCuspNativeEigenvalue N (NeZero.pos N) i<1/4

theorem order_exceptional {i : Idx} (h : exceptional N i) :
    ∃ α∈Icc (0:ℝ) (1/2),basisOrder N (NeZero.pos N) i=(α:ℂ) := by
  let eig := actualCuspNativeEigenvalue N (NeZero.pos N) i
  have heig : 0≤eig := actualCuspNativeEigenvalue_nonneg N (NeZero.pos N) i
  refine ⟨Real.sqrt (1/4-eig),⟨Real.sqrt_nonneg _,?_⟩,if_pos (le_of_lt h)⟩
  apply (Real.sqrt_le_iff.mpr ⟨by norm_num,?_⟩)
  linarith

theorem order_regular {i : Idx} (h : ¬exceptional N i) :
    basisOrder N (NeZero.pos N) i=((height N i:ℝ):ℂ)*I := by
  let eig := actualCuspNativeEigenvalue N (NeZero.pos N) i
  by_cases le : eig≤1/4
  · have eq : eig=1/4 := le_antisymm le (le_of_not_gt h)
    simp [basisOrder,height,show actualCuspNativeEigenvalue N (NeZero.pos N) i=1/4 from eq]
  · exact if_neg le

private theorem strip (i : Idx) : |(basisOrder N (NeZero.pos N) i).re|<1 := by
  by_cases hx : exceptional N i
  · obtain ⟨α,hα,E⟩ := order_exceptional N hx
    rw [E,Complex.ofReal_re,abs_of_nonneg hα.1]
    linarith [hα.2]
  · simp [order_regular N hx,Complex.mul_re]

def bandSet (T : ℝ) : Set ℝ := {t | T≤|t| ∧ |t|≤T+1}
theorem band_measurable (T : ℝ) : MeasurableSet (bandSet T) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter (isClosed_le continuous_abs continuous_const).measurableSet

def budget (m : ℤ) := Classical.choose (uniform_seed_budget N m)

theorem discrete_probe_budget (m : ℤ) (hm : m≠0) (g : SL(2,ℤ)) (T : ℝ) (S : Finset Idx) :
    (∑ i∈S,‖(2*probeIntegral T (basisOrder N (NeZero.pos N) i))*basisR N (NeZero.pos N) i g m‖^2) ≤ budget N m := by
  let f := fun k => seed (rate m) T k
  have lim := tendsto_finsetSum S (fun i _ =>
    (((cutoff_limit m hm T (strip N i)).mul_const (basisR N (NeZero.pos N) i g m)).norm.pow 2))
  apply le_of_tendsto lim
  exact Eventually.of_forall (fun k => (compact_discrete N g m hm (f k) S).trans
    ((Classical.choose_spec (uniform_seed_budget N m)).2 g T k))

private theorem fatou_budget {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {B : ℝ}
    (hF : ∀ k,Integrable (F k)) (hpos : ∀ k t,0≤F k t) (hB : ∀ k,(∫ t,F k t)≤B)
    (lim : ∀ t,Tendsto (fun k => F k t) atTop (𝓝 (f t))) : Integrable f ∧ (∫ t,f t)≤B := by
  have nn (t : ℝ) : 0≤f t := le_of_tendsto_of_tendsto' tendsto_const_nhds (lim t) (fun k => hpos k t)
  have mf := aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hF k).aestronglyMeasurable) (ae_of_all _ lim)
  let G := fun k t => ENNReal.ofReal (F k t)
  have H := lintegral_liminf_le' (μ := (volume : Measure ℝ)) (u := atTop)
    (f := G) (fun k => ENNReal.measurable_ofReal.comp_aemeasurable (hF k).aestronglyMeasurable.aemeasurable)
  have el (t : ℝ) : liminf (fun k => G k t) atTop=ENNReal.ofReal (f t) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (lim t)).liminf_eq
  simp_rw [el] at H
  have ub (k : ℕ) : (∫⁻ t,G k t)≤ENNReal.ofReal B := by
    rw [show (∫⁻ t,G k t)=_ from (ofReal_integral_eq_lintegral_ofReal (hF k) (ae_of_all _ (hpos k))).symm]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have mass : (∫⁻ t,ENNReal.ofReal (f t))≤ENNReal.ofReal B := H.trans (by
    simpa only [liminf_const] using (liminf_le_liminf (Eventually.of_forall ub)))
  have hi : Integrable f := ⟨mf,(hasFiniteIntegral_iff_ofReal (ae_of_all _ nn)).mpr
    (mass.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  have bnn := (integral_nonneg (hpos 0)).trans (hB 0)
  apply (ENNReal.ofReal_le_ofReal_iff bnn).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ nn)]

theorem continuous_probe_budget (m : ℤ) (hm : m≠0) (one : Bool) (T : ℝ) :
    let F := fun t : ℝ => ‖2*probeIntegral T ((t:ℂ)*I)‖^2*continuousMass N one m t
    Integrable F ∧ (∫ t,F t)≤budget N m := by
  let f := fun k => seed (rate m) T k
  let F := fun k (t : ℝ) => ‖orderProbe m (f k).toFun ((t:ℂ)*I)‖^2*continuousMass N one m t
  have H := fun k => compact_continuous N one m hm (f k)
  apply fatou_budget (F := F) (fun k => (H k).1) (fun _ t => mul_nonneg (sq_nonneg _) (continuousMass_nonneg N one m t))
    (fun k => (H k).2.trans ((Classical.choose_spec (uniform_seed_budget N m)).2 (originalFrame one) T k))
  intro t
  exact ((cutoff_limit m hm T (ν := (t:ℂ)*I) (by simp [Complex.mul_re])).norm.pow 2).mul_const _

private theorem mass_meas (m : ℤ) (hm : m≠0) (one : Bool) : AEStronglyMeasurable (continuousMass N one m) volume := by
  let P := fun t : ℝ => ‖2*probeIntegral 1 ((t:ℂ)*I)‖^2
  have E (t : ℝ) : P t = 4*((Real.pi^3/4)*Real.sinh Real.pi/
      ((Real.cosh Real.pi+Real.cosh (Real.pi*t))^2)) := by
    dsimp only [P]
    rw [norm_mul,mul_pow,gamma_norm 1 t (by norm_num)]
    norm_num
  have c : Continuous P := by simp_rw [funext E]; fun_prop (disch := positivity)
  have nz (t : ℝ) : P t≠0 := by rw [E]; positivity
  apply (((continuous_probe_budget N m hm one 1).1.aestronglyMeasurable).div c.aestronglyMeasurable).congr
  exact ae_of_all _ (fun t => by change P t*_/P t=_; field_simp [nz t])

def regularTerm (g : SL(2,ℤ)) (m : ℤ) (T : ℝ) (i : Idx) : ℝ :=
  if ¬exceptional N i ∧ T≤height N i ∧ height N i≤T+1 then
    ‖basisR N (NeZero.pos N) i g m‖^2/Real.cosh (Real.pi*height N i) else 0

def exceptionalTerm (g : SL(2,ℤ)) (m : ℤ) (i : Idx) : ℝ :=
  if exceptional N i then ‖basisR N (NeZero.pos N) i g m‖^2 else 0

private theorem nonnegative_sum {ι : Type*} {w : ι → ℝ} {A : ℝ} (h : ∀ i,0≤w i)
    (B : ∀ S : Finset ι,(∑ i∈S,w i)≤A) : Summable w ∧ (∑' i,w i)≤A := by
  have H := summable_of_sum_le h B
  exact ⟨H,le_of_tendsto H.hasSum (Eventually.of_forall B)⟩

/-- Both original observation cusps, all incoming singular cusps, all
positive levels, and every signed nonzero frequency. The discrete
bounds also hold in every normalized integral observation frame. -/
theorem native_unit_band (m : ℤ) (hm : m≠0) :
    ∃ C : ℝ,0≤C ∧
      (∀ (g : SL(2,ℤ)) (T : ℝ),0≤T → Summable (regularTerm N g m T) ∧
        (∑' i,regularTerm N g m T i)≤C*(1+T)) ∧
      (∀ (one : Bool) (T : ℝ),0≤T →
        IntegrableOn (fun t => continuousMass N one m t/Real.cosh (Real.pi*t)) (bandSet T) ∧
        (∫ t in bandSet T,continuousMass N one m t/Real.cosh (Real.pi*t))≤C*(1+T)) ∧
      (∀ g : SL(2,ℤ),Summable (exceptionalTerm N g m) ∧ (∑' i,exceptionalTerm N g m i)≤C) := by
  obtain ⟨L,hL,lower⟩ := reciprocal_cosh_le
  obtain ⟨c,hc,floor⟩ := exceptional_probe_floor
  let B := budget N m
  have B0 : 0≤B := (Classical.choose_spec (uniform_seed_budget N m)).1
  let C := max (L*B) (B/c)
  refine ⟨C,(mul_nonneg hL.le B0).trans (le_max_left _ _),?_⟩
  have Tband {T t : ℝ} (hT : 0≤T) (h : t∈bandSet T) : | |t| - max 1 T |≤1 := by
    obtain ⟨a,b⟩ := h
    rw [abs_le]
    constructor <;> rcases le_total (1:ℝ) T with e|e
    all_goals first | rw [max_eq_right e]; linarith | rw [max_eq_left e]; linarith
  have ker {T t : ℝ} (hT : 0≤T) (ht : t∈bandSet T) :
      (Real.cosh (Real.pi*t))⁻¹ ≤ (L*(1+T))*‖2*probeIntegral (max 1 T) ((t:ℂ)*I)‖^2 := by
    have H := lower (le_max_left 1 T) (Tband hT ht)
    have mag : ‖probeIntegral (max 1 T) ((t:ℂ)*I)‖^2 ≤ ‖2*probeIntegral (max 1 T) ((t:ℂ)*I)‖^2 := by
      rw [norm_mul,mul_pow]
      norm_num
      nlinarith [sq_nonneg ‖probeIntegral (max 1 T) ((t:ℂ)*I)‖]
    exact H.trans (mul_le_mul (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hL.le)
      mag (sq_nonneg _) (mul_nonneg hL.le (by linarith)))
  constructor
  · intro g T ht
    apply nonnegative_sum (fun i => by unfold regularTerm; split <;> positivity)
    intro S
    have H := discrete_probe_budget N m hm g (max 1 T) S
    calc
      _ ≤ ∑ i∈S,(L*(1+T))*‖(2*probeIntegral (max 1 T) (basisOrder N (NeZero.pos N) i))*basisR N (NeZero.pos N) i g m‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [regularTerm]
        split
        next test =>
          have ht' : height N i∈bandSet T := by simpa only [bandSet,mem_setOf_eq,abs_of_nonneg (Real.sqrt_nonneg _ : 0≤height N i)] using test.2
          rw [order_regular N test.1,norm_mul,mul_pow,div_eq_mul_inv]
          nlinarith only [mul_le_mul_of_nonneg_right (ker ht ht') (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖)]
        next => positivity
      _ ≤ (L*B)*(1+T) := by rw [← Finset.mul_sum]; nlinarith only [mul_le_mul_of_nonneg_left H (mul_nonneg hL.le (by linarith : 0≤1+T))]
      _ ≤ C*(1+T) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  constructor
  · intro one T ht
    let v := fun t => ‖2*probeIntegral (max 1 T) ((t:ℂ)*I)‖^2*continuousMass N one m t
    have H := continuous_probe_budget N m hm one (max 1 T)
    have mv (t : ℝ) : 0≤v t := mul_nonneg (sq_nonneg _) (continuousMass_nonneg N one m t)
    have maj {t : ℝ} (ht' : t∈bandSet T) : continuousMass N one m t/Real.cosh (Real.pi*t) ≤ (L*(1+T))*v t := by
      rw [div_eq_mul_inv]
      dsimp only [v]
      nlinarith only [mul_le_mul_of_nonneg_right (ker ht ht') (continuousMass_nonneg N one m t)]
    let μ := volume.restrict (bandSet T)
    have I : Integrable (fun t => continuousMass N one m t/Real.cosh (Real.pi*t)) μ :=
      (H.1.integrableOn.const_mul (L*(1+T))).mono'
        ((mass_meas N m hm one).div (by fun_prop : Continuous (fun t : ℝ => Real.cosh (Real.pi*t))).aestronglyMeasurable).restrict (by
          filter_upwards [ae_restrict_mem (band_measurable T)] with t hmem
          rw [Real.norm_of_nonneg (div_nonneg (continuousMass_nonneg N one m t) (Real.cosh_pos _).le)]
          exact maj hmem)
    refine ⟨I,?_⟩
    calc
      _ ≤ ∫ t in bandSet T,(L*(1+T))*v t := integral_mono_ae I (H.1.integrableOn.const_mul _)
        ((ae_restrict_mem (band_measurable T)).mono (fun t ht' => maj ht'))
      _ ≤ (L*B)*(1+T) := by
        rw [integral_const_mul]
        have V := setIntegral_le_integral H.1 (ae_of_all _ mv) (s := bandSet T)
        nlinarith only [mul_le_mul_of_nonneg_left (V.trans H.2) (mul_nonneg hL.le (by linarith : 0≤1+T))]
      _ ≤ C*(1+T) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · intro g
    apply nonnegative_sum (fun i => by unfold exceptionalTerm; split <;> positivity)
    intro S
    have H := discrete_probe_budget N m hm g 0 S
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hc).mpr
    rw [Finset.sum_mul]
    apply le_trans (Finset.sum_le_sum ?_) H
    intro i _
    rw [exceptionalTerm]
    split
    next hi =>
      obtain ⟨α,hα,E⟩ := order_exceptional N hi
      rw [E,norm_mul,norm_mul,mul_pow,mul_pow]
      norm_num only [Complex.norm_ofNat]
      nlinarith only [mul_le_mul_of_nonneg_right (floor α hα) (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖),
        mul_nonneg (sq_nonneg ‖probeIntegral 0 (α:ℂ)‖) (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖)]
    next => rw [zero_mul]; positivity

end
end ImbalancedChen.Part3.ActualUnitBandSpectralMass20261112
