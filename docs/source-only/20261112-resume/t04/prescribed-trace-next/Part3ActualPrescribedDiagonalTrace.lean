import ImbalancedChen.Part3ActualPrescribedTraceWeights
import ImbalancedChen.Part3ActualUnitBandSpectralMass
import Mathlib.Analysis.PSeries
import Batteries.Tactic.OpenPrivate

/-! Absolutely summable and integrable diagonal spectral majorants
for the manuscript test, including the unweighted exceptional branch. -/
namespace ImbalancedChen.Part3.ActualPrescribedDiagonalTrace20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups Classical
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedTraceWeights20261112 ActualOppositeBesselTransform20261112
open ActualUnitBandSpectralMass20261112 ActualSingleModeSpectralEnergy20261112
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open private mass_meas from ImbalancedChen.Part3ActualUnitBandSpectralMass

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def basisWeight (Φ : ℝ → ℂ) (i : Idx) : ℝ := ‖8*kTransform (basisOrder N (NeZero.pos N) i) Φ‖

private theorem regular_weight {i : Idx} (hi : ¬exceptional N i) (Φ : ℝ → ℂ) :
    basisWeight N Φ i = ‖oppositeWeight Φ (height N i)‖/Real.cosh (Real.pi*height N i) := by
  rw [basisWeight,order_regular N hi,oppositeWeight,
    show (8:ℂ)*(Real.cosh (Real.pi*height N i):ℂ)*kTransform (((height N i):ℂ)*I) Φ =
      (Real.cosh (Real.pi*height N i):ℂ)*(8*kTransform (((height N i):ℂ)*I) Φ) by ring,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.cosh_pos _).le]
  field_simp [(Real.cosh_pos _).ne']

private def decay (D : ℝ) (k : ℕ) : ℝ := D/(1+(k:ℝ))^5
private def bill (D C : ℝ) (k : ℕ) : ℝ := D*C/(1+(k:ℝ))^4

private theorem summable_bill (D C : ℝ) : Summable (bill D C) := by
  have S : Summable (fun n : ℕ => 1/(n:ℝ)^4) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have H := ((summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^4) 1).mpr S).mul_left (D*C)
  apply H.congr
  intro k
  simp only [bill,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,add_comm]

private theorem bill_eq (D C : ℝ) (k : ℕ) : decay D k*(C*(1+(k:ℝ)))=bill D C k := by
  dsimp only [bill,decay]
  field_simp [show (1+(k:ℝ))≠0 by positivity] <;> ring

private theorem decay_on_band {D : ℝ} {Φ : ℝ → ℂ}
    (h : ∀ t,‖oppositeWeight Φ t‖*(1+|t|)^5≤D) {k : ℕ} {t : ℝ} (ht : t∈bandSet (k:ℝ)) :
    ‖oppositeWeight Φ t‖≤decay D k := by
  apply (le_div_iff₀ (by positivity : 0<(1+(k:ℝ))^5)).mpr
  exact (mul_le_mul_of_nonneg_left (by gcongr; exact ht.1) (norm_nonneg _)).trans (h t)

private theorem regularTerm_nn (g : SL(2,ℤ)) (m : ℤ) (T : ℝ) (i : Idx) :
    0≤regularTerm N g m T i := by unfold regularTerm; split <;> positivity

theorem discrete_diagonal (g : SL(2,ℤ)) (m : ℤ) (hm : m≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun i : Idx => basisWeight N (spectralTest ell Y) i*‖basisR N (NeZero.pos N) i g m‖^2) := by
  let Φ := spectralTest ell Y
  obtain ⟨D,hD,rapid⟩ := regular_fifth_decay ell hY
  obtain ⟨E,hE,ex⟩ := exceptional_bound ell hY
  obtain ⟨C,hC,reg,_,exc⟩ := native_unit_band N m hm
  let slot := fun i : Idx => ⌊height N i⌋₊
  let A := fun i : Idx => basisWeight N Φ i*‖basisR N (NeZero.pos N) i g m‖^2
  have A0 (i : Idx) : 0≤A i := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  apply summable_of_sum_le (c := E*C+∑' k : ℕ,bill D C k) A0
  intro S
  let K := S.image slot
  let row := fun (k : ℕ) (i : Idx) => decay D k*regularTerm N g m (k:ℝ) i
  have R (k : ℕ) (i : Idx) : 0≤row k i := mul_nonneg (div_nonneg hD (by positivity)) (regularTerm_nn N _ _ _ _)
  have splitRow (i : Idx) (hi : i∈S) : A i≤E*exceptionalTerm N g m i+∑ k∈K,row k i := by
    by_cases hx : exceptional N i
    · obtain ⟨α,hα,O⟩ := order_exceptional N hx
      have w : basisWeight N Φ i≤E := by rw [basisWeight,O]; exact (ex α hα).2
      rw [exceptionalTerm,if_pos hx]
      exact (mul_le_mul_of_nonneg_right w (sq_nonneg _)).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => R k i)))
    · have h0 : 0≤height N i := Real.sqrt_nonneg _
      have f := Nat.floor_le h0
      have f' := (Nat.lt_floor_add_one (height N i)).le
      have test : ¬exceptional N i ∧ (slot i:ℝ)≤height N i ∧ height N i≤(slot i:ℝ)+1 := ⟨hx,f,f'⟩
      have band : height N i∈bandSet (slot i:ℝ) := by
        simpa only [bandSet,mem_setOf_eq,abs_of_nonneg h0] using test.2
      have u : A i≤row (slot i) i := by
        dsimp only [A,row]
        rw [regular_weight N hx,regularTerm,if_pos test]
        have q := mul_le_mul_of_nonneg_right (decay_on_band rapid band)
          (div_nonneg (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖) (Real.cosh_pos (Real.pi*height N i)).le)
        simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using q
      rw [exceptionalTerm,if_neg hx,mul_zero,zero_add]
      exact u.trans (Finset.single_le_sum (fun k _ => R k i) (Finset.mem_image_of_mem slot hi))
  calc
    _ ≤ (∑ i∈S,E*exceptionalTerm N g m i)+∑ k∈K,∑ i∈S,row k i := by
      simpa only [Finset.sum_add_distrib,Finset.sum_comm (s := S) (t := K)] using Finset.sum_le_sum splitRow
    _ ≤ E*C+∑ k∈K,bill D C k := by
      apply add_le_add
      · rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ hE
        exact ((exc g).1.sum_le_tsum S (fun i _ => by unfold exceptionalTerm; split <;> positivity)).trans (exc g).2
      · apply Finset.sum_le_sum
        intro k _
        dsimp only [row]
        rw [← Finset.mul_sum,← bill_eq]
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hD (by positivity))
        have h := reg g k (Nat.cast_nonneg k)
        exact (h.1.sum_le_tsum S (fun i _ => regularTerm_nn N _ _ _ _)).trans h.2
    _ ≤ _ := add_le_add_left ((summable_bill D C).sum_le_tsum K (fun k _ => div_nonneg (mul_nonneg hD hC) (by positivity))) _

def weightedContinuousMass (one : Bool) (m : ℤ) (Φ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖oppositeWeight Φ t‖*(continuousMass N one m t/Real.cosh (Real.pi*t))

theorem continuous_diagonal (one : Bool) (m : ℤ) (hm : m≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (weightedContinuousMass N one m (spectralTest ell Y)) := by
  let Φ := spectralTest ell Y
  let A := weightedContinuousMass N one m Φ
  let L := fun t : ℝ => continuousMass N one m t/Real.cosh (Real.pi*t)
  let s := fun k : ℕ => bandSet (k:ℝ)
  obtain ⟨D,hD,rapid⟩ := regular_fifth_decay ell hY
  obtain ⟨C,hC,_,bands,_⟩ := native_unit_band N m hm
  have l0 (t : ℝ) : 0≤L t := div_nonneg (continuousMass_nonneg N _ _ _) (Real.cosh_pos _).le
  have a0 (t : ℝ) : 0≤A t := mul_nonneg (norm_nonneg _) (l0 t)
  have M : AEStronglyMeasurable A volume := (regular_measurable ell hY).norm.aestronglyMeasurable.mul
    ((mass_meas N m hm one).div (by fun_prop : Continuous (fun t : ℝ => Real.cosh (Real.pi*t))).aestronglyMeasurable)
  have maj (k : ℕ) : ∀ᵐ t ∂volume.restrict (s k),‖A t‖≤decay D k*L t := by
    filter_upwards [ae_restrict_mem (band_measurable (k:ℝ))] with t ht
    rw [Real.norm_of_nonneg (a0 t)]
    exact mul_le_mul_of_nonneg_right (decay_on_band rapid ht) (l0 t)
  have localI (k : ℕ) : IntegrableOn A (s k) := ((bands one k (Nat.cast_nonneg k)).1.const_mul
    (decay D k)).mono' M.restrict (maj k)
  have H (k : ℕ) : (∫ t in s k,‖A t‖)≤bill D C k := by
    have B := bands one k (Nat.cast_nonneg k)
    calc
      _ ≤ ∫ t in s k,decay D k*L t := integral_mono_ae (localI k).norm (B.1.const_mul _) (maj k)
      _ ≤ decay D k*(C*(1+(k:ℝ))) := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left B.2 (div_nonneg hD (by positivity))
      _ = _ := bill_eq _ _ _
  have U : (⋃ k : ℕ,s k)=univ := eq_univ_of_forall (fun t =>
    mem_iUnion.mpr ⟨⌊|t|⌋₊,Nat.floor_le (abs_nonneg t),(Nat.lt_floor_add_one |t|).le⟩)
  have I := integrableOn_iUnion_of_summable_integral_norm localI
    (Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _)) H (summable_bill D C))
  simpa only [U,integrableOn_univ] using I

end
end ImbalancedChen.Part3.ActualPrescribedDiagonalTrace20261112
