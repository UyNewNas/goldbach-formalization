import ImbalancedChen.Part3OriginalPrescribedPositiveSpectralWeights
import Mathlib.Analysis.PSeries
import Batteries.Tactic.OpenPrivate

/-! An integrable majorant for the original, unnormalized marked cross
product on the real spectrum. The exponent three pays the unit bands. -/
namespace ImbalancedChen.Part3.ActualMarkedCubicPrice20261112

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology BigOperators MatrixGroups Classical
open ActualUnitBandSpectralMass20261112 ActualSingleModeSpectralEnergy20261112
open ActualCuspBasisWhittakerCoefficients20261102 ActualFullCuspEigenbasis20261026b
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110 ActualContinuousClassFourier20261110
open OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110 OriginalContinuousPoincarePackets20261110
open OriginalMarkedArithmeticTrace20261112 ActualPositiveNativeDiagonal20261112
open OriginalNativeCuspFunctionals20261102 OriginalProjectedContinuousCovariance20261112
open private mass_meas from ImbalancedChen.Part3ActualUnitBandSpectralMass
open private cost marked_sq product_le from ImbalancedChen.Part3ActualMarkedSpectralMajorants
open private regularTerm_nn from ImbalancedChen.Part3ActualPrescribedDiagonalTrace

def cubic (t : ℝ) := 1/(1+|t|)^3
def linePrice (t : ℝ) := cubic t/Real.cosh (Real.pi*t)
def slotPrice (N : ℕ) [NeZero N] (i : actualCuspBasisIndex N (NeZero.pos N)) :=
  if exceptional N i then 0 else linePrice (height N i)

theorem linePrice_pos (t : ℝ) : 0<linePrice t := by unfold linePrice cubic; positivity
theorem slotPrice_nn (N : ℕ) [NeZero N] (i : actualCuspBasisIndex N (NeZero.pos N)) :
    0≤slotPrice N i := by unfold slotPrice; split <;> first | exact le_rfl | exact (linePrice_pos _).le

private theorem charges (C : ℝ) : Summable (fun k : ℕ => cubic k*(C*(1+(k:ℝ)))) := by
  have S := (Real.summable_nat_pow_inv.mpr (by norm_num : 1<2))
  have H := ((summable_nat_add_iff (f:=fun k : ℕ => ((k:ℝ)^2)⁻¹) 1).mpr S).mul_left C
  apply H.congr
  intro k
  dsimp only [cubic]
  rw [abs_of_nonneg (Nat.cast_nonneg k),Nat.cast_add,Nat.cast_one]
  field_simp [show (1+(k:ℝ))≠0 by positivity,show ((k:ℝ)+1)≠0 by positivity] <;> ring

private theorem on_band {k : ℕ} {t : ℝ} (h : t∈bandSet k) : cubic t≤cubic k := by
  simp only [cubic,abs_of_nonneg (Nat.cast_nonneg k)]
  gcongr; exact h.1

theorem discrete_mode (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (hm : m≠0) :
    Summable (fun i : actualCuspBasisIndex N (NeZero.pos N) =>
      slotPrice N i*‖basisR N (NeZero.pos N) i g m‖^2) := by
  obtain ⟨C,c,reg,_,_⟩ := native_unit_band N m hm
  let F := fun p : ℕ×actualCuspBasisIndex N (NeZero.pos N) => cubic p.1*regularTerm N g m p.1 p.2
  have f0 (p) : 0≤F p := mul_nonneg (by unfold cubic; positivity) (regularTerm_nn N _ _ _ _)
  have s : Summable F := by
    apply (summable_prod_of_nonneg f0).mpr
    refine ⟨fun k => ((reg g k (Nat.cast_nonneg k)).1).mul_left _,?_⟩
    apply Summable.of_nonneg_of_le (fun k => tsum_nonneg fun i => f0 (k,i)) _ (charges C)
    intro k; change (∑' i,cubic k*_)≤_
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (reg g k (Nat.cast_nonneg k)).2 (by unfold cubic; positivity)
  let index := fun i : actualCuspBasisIndex N (NeZero.pos N) => (⌊height N i⌋₊,i)
  apply (s.comp_injective (i:=index) (fun _ _ E => congrArg Prod.snd E)).of_nonneg_of_le
    (fun i => mul_nonneg (slotPrice_nn _ _) (sq_nonneg _))
  intro i
  by_cases e : exceptional N i
  · simpa only [slotPrice,if_pos e,zero_mul] using f0 (index i)
  let k := ⌊height N i⌋₊
  have h0 : 0≤height N i := Real.sqrt_nonneg _
  have a := Nat.floor_le h0
  have b := (Nat.lt_floor_add_one (height N i)).le
  have H : height N i∈bandSet k := by simpa only [bandSet,Set.mem_setOf_eq,abs_of_nonneg h0,k] using And.intro a b
  have B := mul_le_mul_of_nonneg_right (on_band H)
    (div_nonneg (sq_nonneg ‖basisR N (NeZero.pos N) i g m‖) (Real.cosh_pos _).le)
  simpa only [F,index,k,regularTerm,if_pos ⟨e,a,b⟩,slotPrice,if_neg e,linePrice,
    div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using B

theorem continuous_mode (N : ℕ) [NeZero N] (b : Bool) (m : ℤ) (hm : m≠0) :
    Integrable (fun t => linePrice t*continuousMass N b m t) := by
  let A := fun t => linePrice t*continuousMass N b m t
  let L := fun t => continuousMass N b m t/Real.cosh (Real.pi*t)
  let S (k : ℕ) := bandSet (k:ℝ)
  obtain ⟨C,_,_,bands,_⟩ := native_unit_band N m hm
  have l0 (t : ℝ) : 0≤L t := div_nonneg (continuousMass_nonneg _ _ _ t) (Real.cosh_pos _).le
  have mA : AEStronglyMeasurable A volume :=
    (by unfold linePrice cubic; fun_prop (disch:=positivity) : Continuous linePrice).aestronglyMeasurable.mul (mass_meas N m hm b)
  have price (k : ℕ) : ∀ᵐ t ∂volume.restrict (S k),‖A t‖≤cubic k*L t := by
    filter_upwards [ae_restrict_mem (band_measurable k)] with t ht
    change ‖linePrice t*continuousMass N b m t‖≤_
    rw [Real.norm_of_nonneg (mul_nonneg (linePrice_pos _).le (continuousMass_nonneg _ _ _ t))]
    simpa [linePrice,L,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_right (on_band ht) (l0 t)
  have I (k : ℕ) : IntegrableOn A (S k) := ((bands b k (Nat.cast_nonneg k)).1.const_mul _).mono' mA.restrict (price k)
  have H (k : ℕ) : (∫ t in S k,‖A t‖)≤cubic k*(C*(1+(k:ℝ))) := by
    apply (integral_mono_ae (I k).norm ((bands b k (Nat.cast_nonneg k)).1.const_mul _) (price k)).trans
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (bands b k (Nat.cast_nonneg k)).2 (by unfold cubic; positivity)
  have U : (⋃ k : ℕ,S k)=univ := eq_univ_of_forall fun t => mem_iUnion.mpr
    ⟨⌊|t|⌋₊,Nat.floor_le (abs_nonneg t),(Nat.lt_floor_add_one |t|).le⟩
  simpa only [U,integrableOn_univ] using integrableOn_iUnion_of_summable_integral_norm I
    ((charges C).of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) H)

theorem discrete_mark (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (S : Finset ℕ) (w : ℕ→ℂ) (f : ℕ→ℤ)
    (nz : ∀ p∈S,f p≠0) : Summable (fun i : actualCuspBasisIndex N (NeZero.pos N) =>
      slotPrice N i*‖markedRow S w f (basisR N (NeZero.pos N) i g)‖^2) := by
  have H := (summable_sum (s:=S) fun p hp => discrete_mode N g (f p) (nz p hp)).mul_left (cost S w)
  apply H.of_nonneg_of_le (fun i => mul_nonneg (slotPrice_nn _ _) (sq_nonneg _))
  intro i
  simpa only [Finset.mul_sum,mul_comm,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_left (marked_sq S w f (basisR N (NeZero.pos N) i g)) (slotPrice_nn N i)

def contBudget (N : ℕ) [NeZero N] (b : Bool) (S : Finset ℕ) (w : ℕ→ℂ) (f : ℕ→ℤ) (t : ℝ) :=
  cost S w*∑ p∈S,linePrice t*continuousMass N b (f p) t

theorem cont_budget_L1 (N : ℕ) [NeZero N] (b : Bool) (S : Finset ℕ) (w : ℕ→ℂ) (f : ℕ→ℤ)
    (nz : ∀ p∈S,f p≠0) : Integrable (contBudget N b S w f) :=
  (integrable_finsetSum S fun p hp => continuous_mode N b (f p) (nz p hp)).const_mul _

theorem cont_mark (N : ℕ) [NeZero N] (b : Bool) (S : Finset ℕ) (w : ℕ→ℂ) (f : ℕ→ℤ) (t : ℝ) :
    (linePrice t/(4*Real.pi))*(∑ a : Parameters N,‖markedRow S w f (fun m => nativeR a b m t)‖^2)≤
      contBudget N b S w f t := by
  let c := linePrice t/(4*Real.pi)
  have p (m : ℤ) : c*(∑ a : Parameters N,‖nativeR a b m t‖^2)=linePrice t*continuousMass N b m t := by
    dsimp [c,continuousMass]; ring
  have H := Finset.sum_le_sum (s:=(Finset.univ:Finset (Parameters N))) (fun a _ => marked_sq S w f (fun m => nativeR a b m t))
  apply (mul_le_mul_of_nonneg_left H (div_nonneg (linePrice_pos _).le (by positivity))).trans_eq
  rw [← Finset.mul_sum,Finset.sum_comm,contBudget,mul_left_comm,Finset.mul_sum]
  simp only [p]

end
end ImbalancedChen.Part3.ActualMarkedCubicPrice20261112
