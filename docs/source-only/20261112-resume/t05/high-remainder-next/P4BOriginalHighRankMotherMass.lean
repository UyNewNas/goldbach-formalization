import ImbalancedChen.P4BOriginalHighRankMotherModes
import ImbalancedChen.P4BOriginalUpperFourierTailPaid

/-! Total normalized L1 of the literal amplitudes in the original upper-pair
modeBank, including every original label, order, hard dyadic word and scalar. -/
namespace ImbalancedChen.P4BOriginalHighRankMotherMass
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BUpperPairOrderedRowModes (amplitude)
open P4BUpperPairOrderedRowGeometry (rowChart pairOwner blockScales blockScales_pos)
open P4BArbitraryWidthUpperPairOccurrence (exists_actual_mixedD_width_budget occurrenceChart occurrenceChart_smooth occurrenceChart_compact)
open P4BOriginalUpperFourierTailPaid (sourceScalarMass sourceScalarMass_le groupScalarMass dyadicConstant dyadicConstant_pos)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.ActualEuclideanPhysicalFourier
open P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.OrderedFactorTupleRectangleReindex
open P5Z.HBRightClosedDyadicRoles
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCap)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank R R_pos)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords)

/-- The same mother amplitude that multiplies each original exact-discrepancy mode. -/
def rowMass {u v : ℕ} (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (j l : ℕ) (bs : Fin (u+v)→Block) :=
  ∫ ξ,‖amplitude (a:=u) (d:=v) b kap s N kap0 j l bs ξ‖

def weightedGroup (j : ℕ) (f : ℕ→List Block→ℝ) :=
  ∑ i∈Finset.range 3,‖P5Z.SmoothChartHBDyadicPartition.scalar i‖*
    ∑ bs∈blockWords (hbCap j) (2*(i+1)),f i bs

def totalMass (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) :=
  ∑ js∈chartBank N 2,weightedGroup (js.getD 0 0) (fun i bs =>
    weightedGroup (js.getD 1 0) (fun l cs =>
      rowMass (u:=2*(i+1)) (v:=2*(l+1)) b kap s N kap0 (js.getD 0 0) (js.getD 1 0)
        (Fin.append (blockVector (2*(i+1)) bs) (blockVector (2*(l+1)) cs))))

private theorem group_le (j : ℕ) (f : ℕ→List Block→ℝ) (E : ℝ)
    (h : ∀ i∈Finset.range 3,∀ bs∈blockWords (hbCap j) (2*(i+1)),f i bs≤E) :
    weightedGroup j f≤groupScalarMass j*E := by
  unfold weightedGroup groupScalarMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ‖P5Z.SmoothChartHBDyadicPartition.scalar i‖*
        (∑ _bs∈blockWords (hbCap j) (2*(i+1)),E) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (h i hi)) (norm_nonneg _)
    _ = _ := by simp [nsmul_eq_mul,mul_assoc]

theorem exists_row_mass :
    ∃ C : ℝ,0≤C ∧ ∀ (b kap s : ℝ) (hb : 0<b),b≤1 → 0<kap → 0<s →
      2*s≤baseline b kap-19/96 → ∀ (N : ℕ),0<N → ∀ (kap0 : ℝ) (cj ck u v : ℕ),
      u+v≤12 → ∀ bs : Fin (u+v)→Block,rowMass (u:=u) (v:=v) b kap s N kap0 cj ck bs≤C/s^24 := by
  obtain ⟨C,hC,H⟩ := exists_actual_mixedD_width_budget
  refine ⟨C,hC,?_⟩
  intro b kap s hb hb' hk hs hg N hN kap0 cj ck u v hdim bs
  have H' : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  let w := occurrenceChart b kap s N (pairOwner u v) (blockScales bs) (![R cj,R ck]) kap0
  have hsmooth := occurrenceChart_smooth hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs H'
    N (pairOwner u v) (blockScales bs) (![R cj,R ck]) kap0
  have hcompact := occurrenceChart_compact b kap s N (pairOwner u v) (blockScales bs) (![R cj,R ck]) kap0
  have hD := H b kap 1 (19/96) s hb hb' hk (by norm_num) (by norm_num) hs H' N (u+v)
    (pairOwner u v) (blockScales bs) (![R cj,R ck]) kap0 (by exact_mod_cast hN) (blockScales_pos bs)
    (fun i => by fin_cases i <;> exact R_pos _) hdim
  have he : rowMass (u:=u) (v:=v) b kap s N kap0 cj ck bs=
      (∫ ξ,‖physicalFourier (u+v) (rowChart b kap s N kap0 cj ck bs) ξ‖)/frequencyScale^(u+v) := by
    have hpos : 0<(frequencyScale^(u+v))⁻¹ := inv_pos.mpr (pow_pos frequencyScale_pos _)
    simp only [rowMass,amplitude,norm_smul,Real.norm_eq_abs,abs_of_pos hpos]
    rw [integral_const_mul]
    ring
  rw [he]
  exact (physicalFourier_normalized_l1_le (u+v) _ (euclideanLift_smooth (u+v) w hsmooth)
    (euclideanLift_compact (u+v) w hcompact)).trans
    ((div_le_div_of_nonneg_right hD (by positivity)).trans
      (div_le_self (div_nonneg hC (pow_nonneg hs.le _)) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))))

/-- This is the integrated scalar mass of all mothers, for every legal width.
No rectangular mode saving or signed density estimate enters this budget. -/
theorem exists_mother_mass :
    ∃ C : ℝ,0≤C ∧ ∀ b kap s : ℝ,0<b → b≤1 → 0<kap → 0<s →
      2*s≤baseline b kap-19/96 → ∀ N : ℕ,0<N → ∀ kap0 : ℝ,
        totalMass b kap s N kap0≤C*logScale (countingScale N)^14/s^24 := by
  obtain ⟨C,hC,H⟩ := exists_row_mass
  refine ⟨49*dyadicConstant^14*C,mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg dyadicConstant_pos.le _)) hC,?_⟩
  intro b kap s hb hb' hk hs hg N hN kap0
  let E := C/s^24
  have e0 : 0≤E := div_nonneg hC (pow_nonneg hs.le _)
  have hr := H b kap s hb hb' hk hs hg N hN kap0
  have all : totalMass b kap s N kap0≤sourceScalarMass N*E := by
    unfold totalMass sourceScalarMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro js _
    refine (group_le _ _ (groupScalarMass (js.getD 1 0)*E) (fun i hi bs _ => ?_)).trans_eq
      (mul_assoc _ _ _).symm
    exact group_le _ _ E (fun l hl cs _ => hr _ _ _ _ (by
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hl
      omega) _)
  exact all.trans ((mul_le_mul_of_nonneg_right (sourceScalarMass_le hN) e0).trans_eq
    (by dsimp only [E]; ring))

/-- The resolution rule can depend on N. Its actual value must satisfy the displayed
growth and physical gap. B and the rule may be prescribed before the targets. -/
theorem exists_resolution_mass (B : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (b kap : ℝ),0<b → b≤1 → 0<kap →
      ∀ (N m : ℕ),0<N → (m+1:ℝ)≤logScale (countingScale N)^B →
      2*(1/(m+1:ℝ))≤baseline b kap-19/96 → ∀ kap0 : ℝ,
      totalMass b kap (1/(m+1:ℝ)) N kap0≤C*logScale (countingScale N)^(14+B*24) := by
  obtain ⟨C,hC,H⟩ := exists_mother_mass
  refine ⟨C,hC,?_⟩
  intro b kap hb hb' hk N m hN hm hg kap0
  let L := logScale (countingScale N)
  have hL : 0≤L := zero_le_one.trans (logScale_one_le (countingScale_one_le hN))
  have h0 : 0<(m+1:ℝ) := by positivity
  have h := H b kap _ hb hb' hk (one_div_pos.mpr h0) hg N hN kap0
  calc
    _ ≤ C*L^14/(1/(m+1:ℝ))^24 := h
    _ = C*L^14*(m+1:ℝ)^24 := by simp [one_div,div_eq_mul_inv]
    _ ≤ C*L^14*(L^B)^24 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ h0.le hm 24) (mul_nonneg hC (pow_nonneg hL _))
    _ = _ := by rw [pow_add,pow_mul]; ring

end
end ImbalancedChen.P4BOriginalHighRankMotherMass
