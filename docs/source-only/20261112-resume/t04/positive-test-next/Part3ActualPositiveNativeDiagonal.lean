import ImbalancedChen.Part3ActualPrescribedPositiveJ
import ImbalancedChen.Part3ActualPrescribedDiagonalTrace
import ImbalancedChen.Part3OriginalExceptionalJNativeCompletion
import Batteries.Tactic.OpenPrivate

/-! Pricing the actual same-sign regular and complementary branches on
the physical fixed-level index set and on the full Eisenstein line. -/
namespace ImbalancedChen.Part3.ActualPositiveNativeDiagonal20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedPositiveJ20261112 ActualUnitBandSpectralMass20261112
open ActualSingleModeSpectralEnergy20261112 ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102 ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisIndexCounting20261026b
open OriginalExceptionalJNativeCompletion20261110 (native_cusp_eigenvalue_pos)
open private summable_bill bill_eq bill decay regularTerm_nn from ImbalancedChen.Part3ActualPrescribedDiagonalTrace
open private mass_meas from ImbalancedChen.Part3ActualUnitBandSpectralMass

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def complementaryHeight (i : Idx) : ℝ := Real.sqrt (1/4-actualCuspNativeEigenvalue N (NeZero.pos N) i)

theorem complementary_range {i : Idx} (h : exceptional N i) :
    0<complementaryHeight N i ∧ complementaryHeight N i<1/2 ∧ 0<Real.cos (Real.pi*complementaryHeight N i) := by
  have H := native_cusp_eigenvalue_pos N (NeZero.pos N) i
  have a : 0<complementaryHeight N i := Real.sqrt_pos.mpr (sub_pos.mpr h)
  have b : complementaryHeight N i<1/2 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith only [H])
  exact ⟨a,b,Real.cos_pos_of_mem_Ioo ⟨by nlinarith only [mul_pos Real.pi_pos a,Real.pi_pos],
    by nlinarith only [mul_lt_mul_of_pos_left b Real.pi_pos]⟩⟩

def nativeWeight (Φ : ℝ → ℂ) (i : Idx) : ℂ :=
  if exceptional N i then exceptionalWeight Φ (complementaryHeight N i)/(Real.cos (Real.pi*complementaryHeight N i):ℂ)
  else positiveWeight Φ (height N i)/(Real.cosh (Real.pi*height N i):ℂ)

private theorem band_bound {D : ℝ} {Φ : ℝ → ℂ} (H : ∀ t,‖positiveWeight Φ t‖*(1+|t|)^5≤D)
    {k : ℕ} {t : ℝ} (h : t∈bandSet (k:ℝ)) : ‖positiveWeight Φ t‖≤decay D k := by
  apply (le_div_iff₀ (by positivity : 0<(1+(k:ℝ))^5)).mpr
  exact (mul_le_mul_of_nonneg_left (by gcongr; exact h.1) (norm_nonneg _)).trans (H t)

theorem discrete_diagonal (g : SL(2,ℤ)) (m : ℤ) (hm : m≠0)
    (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun i : Idx => ‖nativeWeight N (spectralTest ell Y) i‖*‖basisR N (NeZero.pos N) i g m‖^2) := by
  let Φ := spectralTest ell Y
  obtain ⟨D,d,rap⟩ := fixed_regular_decay ell hY 5
  obtain ⟨C,c,reg,_,_⟩ := native_unit_band N m hm
  let F := fun p : ℕ×Idx => decay D p.1*regularTerm N g m (p.1:ℝ) p.2
  have f0 (p : ℕ×Idx) : 0≤F p := mul_nonneg (div_nonneg d (by positivity)) (regularTerm_nn N _ _ _ _)
  have sf : Summable F := by
    apply (summable_prod_of_nonneg f0).mpr
    refine ⟨fun k => ((reg g k (Nat.cast_nonneg k)).1).mul_left _,?_⟩
    apply Summable.of_nonneg_of_le (fun k => tsum_nonneg fun i => f0 (k,i)) _ (summable_bill D C)
    intro k
    change (∑' i,decay D k*regularTerm N g m (k:ℝ) i)≤_
    rw [tsum_mul_left,← bill_eq]
    exact mul_le_mul_of_nonneg_left (reg g k (Nat.cast_nonneg k)).2 (div_nonneg d (by positivity))
  let slot := fun i : Idx => (⌊height N i⌋₊,i)
  let A := fun i : Idx => ‖nativeWeight N Φ i‖*‖basisR N (NeZero.pos N) i g m‖^2
  let E := fun i : Idx => if exceptional N i then A i else 0
  have se : Summable E := by
    apply summable_of_hasFiniteSupport
    apply (actualCuspIndexSublevel_finite N (NeZero.pos N) (1/4)).subset
    intro i hi
    by_contra h
    have h' : ¬exceptional N i := fun e => h e.le
    exact hi (if_neg h')
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (sq_nonneg _)) _
    (se.add (sf.comp_injective (i := slot) (fun _ _ h => congrArg Prod.snd h)))
  intro i
  change A i≤E i+F (slot i)
  by_cases hx : exceptional N i
  · simpa only [E,if_pos hx] using le_add_of_nonneg_right (a:=A i) (f0 (slot i))
  · let k := ⌊height N i⌋₊
    have h0 : 0≤height N i := Real.sqrt_nonneg _
    have bounds := And.intro (Nat.floor_le h0) (Nat.lt_floor_add_one (height N i)).le
    have B : height N i∈bandSet (k:ℝ) := by simpa only [bandSet,mem_setOf_eq,abs_of_nonneg h0,k] using bounds
    have w := mul_le_mul_of_nonneg_right (band_bound rap B)
      (div_nonneg (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖) (Real.cosh_pos _).le)
    simpa only [A,E,hx,if_false,zero_add,F,slot,nativeWeight,regularTerm,if_pos ⟨hx,bounds⟩,
      norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.cosh_pos _).le,k,div_eq_mul_inv,
      mul_comm,mul_assoc,mul_left_comm] using w

def contMass (one : Bool) (m : ℤ) (Φ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖positiveWeight Φ t‖*(continuousMass N one m t/Real.cosh (Real.pi*t))

theorem continuous_diagonal (one : Bool) (m : ℤ) (hm : m≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (contMass N one m (spectralTest ell Y)) := by
  let Φ := spectralTest ell Y
  let A := contMass N one m Φ
  let L := fun t : ℝ => continuousMass N one m t/Real.cosh (Real.pi*t)
  let s := fun k : ℕ => bandSet (k:ℝ)
  obtain ⟨D,hD,rapid⟩ := fixed_regular_decay ell hY 5
  obtain ⟨C,hC,_,bands,_⟩ := native_unit_band N m hm
  have l0 (t : ℝ) : 0≤L t := div_nonneg (continuousMass_nonneg N _ _ _) (Real.cosh_pos _).le
  have a0 (t : ℝ) : 0≤A t := mul_nonneg (norm_nonneg _) (l0 t)
  have ew : positiveWeight Φ=(weightSchwartz ell hY:ℝ → ℂ) := funext fun t => (regular_transform ell hY t).2
  have M : AEStronglyMeasurable A volume := by
    change AEStronglyMeasurable (fun t => ‖positiveWeight Φ t‖*L t) volume
    rw [ew]
    exact (weightSchwartz ell hY).continuous.norm.aestronglyMeasurable.mul
      ((mass_meas N m hm one).div (by fun_prop : Continuous (fun t : ℝ => Real.cosh (Real.pi*t))).aestronglyMeasurable)
  have maj (k : ℕ) : ∀ᵐ t ∂volume.restrict (s k),‖A t‖≤decay D k*L t := by
    filter_upwards [ae_restrict_mem (band_measurable (k:ℝ))] with t ht
    rw [Real.norm_of_nonneg (a0 t)]; exact mul_le_mul_of_nonneg_right (band_bound rapid ht) (l0 t)
  have loc (k : ℕ) : IntegrableOn A (s k) := ((bands one k (Nat.cast_nonneg k)).1.const_mul
    (decay D k)).mono' M.restrict (maj k)
  have H (k : ℕ) : (∫ t in s k,‖A t‖)≤bill D C k := by
    have B := bands one k (Nat.cast_nonneg k)
    calc
      _ ≤ ∫ t in s k,decay D k*L t := integral_mono_ae (loc k).norm (B.1.const_mul _) (maj k)
      _ ≤ decay D k*(C*(1+(k:ℝ))) := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left B.2 (div_nonneg hD (by positivity))
      _ = _ := bill_eq _ _ _
  have U : (⋃ k : ℕ,s k)=univ := eq_univ_of_forall (fun t =>
    mem_iUnion.mpr ⟨⌊|t|⌋₊,Nat.floor_le (abs_nonneg t),(Nat.lt_floor_add_one |t|).le⟩)
  simpa only [U,integrableOn_univ] using integrableOn_iUnion_of_summable_integral_norm loc
    (Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _)) H (summable_bill D C))

end
end ImbalancedChen.Part3.ActualPositiveNativeDiagonal20261112

