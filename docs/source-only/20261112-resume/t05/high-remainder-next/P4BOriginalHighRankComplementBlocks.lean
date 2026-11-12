import ImbalancedChen.P4BOriginalHighRankMediumHeads
import ImbalancedChen.P4BOriginalHighRankScheduledCount

/-! Fix the complete complementary dyadic block before the medium arithmetic
test. Its membership is independent of the selected HB integer and of rho. -/
namespace ImbalancedChen.P4BOriginalHighRankComplementBlocks
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos)
open P5Z.HBRightClosedDyadicRoles (Block bank owner owner_mem_bank bank_card)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.CompleteProductTailDivisorBudgets (logScale)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos log2_count_le)
open P4BUpperPairOrderedRowGeometry (integerProfile pairOwner)
open P4BOriginalHighRankMotherScale (completeScale)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOuterRampRoughness (baseline)

def complement {t : ℕ} (i : Fin t) (y : Fin t→ℕ) := ∏ j∈Finset.univ.erase i,y j

theorem independent {t : ℕ} (i : Fin t) {u v : Fin t→ℕ}
    (h : ∀ j,j≠i → u j=v j) : complement i u=complement i v :=
  Finset.prod_congr rfl (fun j hj => h j (Finset.mem_erase.mp hj).1)

theorem quotient_eq {t : ℕ} (i : Fin t) (y : Fin t→ℕ) (hi : 0<y i) :
    completeProduct y/y i=complement i y := by
  rw [completeProduct,←Finset.mul_prod_erase Finset.univ y (Finset.mem_univ i)]
  exact Nat.mul_div_cancel_left _ hi

def fibre {t : ℕ} (bs : Fin t→Block) (i : Fin t) (c : Block) :=
  (rectangle bs).filter (fun y => owner (complement i y)=c)

def cap (N : ℕ) := Nat.floor (countingScale N)

theorem same_scale {t : ℕ} {bs : Fin t→Block} {i : Fin t} {c : Block} {y : Fin t→ℕ}
    (hy : y∈fibre bs i c) : completeScale bs y i=(lower (bs i):ℝ)*lower c := by
  obtain ⟨hrect,heq⟩ := Finset.mem_filter.mp hy
  rw [completeScale,quotient_eq i y (owns_pos ((mem_rectangle bs y).mp hrect i)),heq]

/-- The same finite decomposition of an occupied mother applies to every
integrand, hence to the original integer sum as well as every fixed frequency
of its exact signed congruence-minus-coprime-mean discrepancy. -/
theorem partition {u v N : ℕ} {b kap s kap0 : ℝ} (hb : 0<b) (hk : 0<kap) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v))
    (hsize : u+v≤12) (hnz : ∃ y∈rectangle bs,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0)
    (f : (Fin (u+v)→ℕ)→ℂ) :
    (∑ c∈bank (cap N),∑ y∈fibre bs i c,f y)=∑ y∈rectangle bs,f y := by
  obtain ⟨y,hy,hnz⟩ := hnz
  have hrect {z : Fin (u+v)→ℕ} (hz : z∈rectangle bs) : z∈P4BArbitraryWidthUpperBlockGeometry.rectangle bs := by
    apply Fintype.mem_piFinset.mpr
    intro j
    have ho := (mem_rectangle bs z).mp hz j
    cases hbj : bs j <;> simpa [P4BArbitraryWidthUpperBlockGeometry.blockIntegers,
      P5Z.HBRightClosedDyadicRoles.Owns,hbj] using ho
  have HG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  apply Finset.sum_fiberwise_of_maps_to (s:=rectangle bs) (t:=bank (cap N))
    (g:=fun z => owner (complement i z))
  intro z hz
  obtain ⟨hpos,hsiz⟩ := P4BArbitraryWidthUpperBlockGeometry.rectangle_counting_scale hb hk
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs HG (pairOwner u v) bs
    (![P5Z.ExactOriginalSmoothDyadicPartition.R cj,P5Z.ExactOriginalSmoothDyadicPartition.R ck])
    kap0 hsize ⟨y,hrect hy,hnz⟩ (hrect hz)
  have hdiv : z i∣completeProduct z := Finset.dvd_prod_of_mem z (Finset.mem_univ _)
  have hypos : 0<completeProduct z := Finset.prod_pos (fun j _ => hpos j)
  rw [←quotient_eq i z (hpos i)]
  exact owner_mem_bank (Nat.div_pos (Nat.le_of_dvd hypos hdiv) (hpos i))
    ((Nat.div_le_self _ _).trans (Nat.le_floor hsiz))

theorem complement_count {N : ℕ} (hN : 0<N) :
    ((bank (cap N)).card:ℝ)≤dyadicConstant*logScale (countingScale N) := by
  rw [bank_card]
  have hs := countingScale_one_le hN
  have hcap : (cap N:ℝ)≤countingScale N := Nat.floor_le (zero_le_one.trans hs)
  have hsub : ((cap N-1:ℕ):ℝ)≤cap N := by exact_mod_cast Nat.sub_le (cap N) 1
  exact log2_count_le hs _ (by linarith)

/-- Multiplicity of the genuine complementary partition is included once in
the original all-mother budget, including original order signs and transforms.
The exponent 39 is for this single chosen resolution law. -/
theorem exists_scheduled_split_mass :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ kap0 : ℝ,
      ((bank (cap N)).card:ℝ)*totalMass b kap (outerWidth N) N kap0≤C*(Real.log (N:ℝ))^39 := by
  obtain ⟨C,hC,H⟩ := P4BOriginalHighRankScheduledCount.exists_scheduled_mass
  refine ⟨(2*dyadicConstant)*C,mul_nonneg (by positivity) hC,?_⟩
  intro b kap hb hb1 hk hg
  filter_upwards [H hb hb1 hk hg,P4BOriginalHighRankScheduledCount.eventually_width 1 (by norm_num),
    eventually_one_le_nat_log] with N hm hN hl
  intro kap0
  have hc := (complement_count (N:=N) (by linarith only [hN.1])).trans
    (mul_le_mul_of_nonneg_left hN.2.2.2.2 dyadicConstant_pos.le)
  calc
    _≤((bank (cap N)).card:ℝ)*(C*(Real.log (N:ℝ))^38) :=
      mul_le_mul_of_nonneg_left (hm kap0) (Nat.cast_nonneg _)
    _≤(dyadicConstant*(2*Real.log (N:ℝ)))*(C*(Real.log (N:ℝ))^38) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hC (pow_nonneg (by linarith) _))
    _=_ := by ring

end
end ImbalancedChen.P4BOriginalHighRankComplementBlocks
