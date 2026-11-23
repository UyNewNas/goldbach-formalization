import ImbalancedChen.P1OriginalSingletonMediumRestoringBudget
import ImbalancedChen.P1OriginalSingletonMediumRectangles

/-!
SOURCE ONLY / NOT COMPILED.

One actual chart/HB row is partitioned by its occupied complementary blocks
before Fourier truncation. The same actual singleton profile gives cap2N.
The old per-fibre scalar/amplitude/word-owner cost is then summed over this
genuine finite subbank. No signed M, AvgJ, Fourier-tail, trim reserve or
outer chart/HB-row inventory estimate is asserted.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumLiveRowInventory
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P1OriginalSingletonMediumReconstruction (scalar)
open P1OriginalSingletonMediumFourier (amplitude original original_eq_fourier frequencyMode)
open P1OriginalSingletonMediumRestoringBudget (modulusCost restored_row_amplitude_cost)
open P1OriginalSingletonOneLongRectangle (occurrenceAtom)
open P1OriginalSingletonOneLongProfile (profileHeight)
open P1OriginalSingletonOneLongRestoration (height_one_le)
open P5Z.HBRightClosedDyadicRoles (Block bank bank_card owner owner_mem_bank)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos)
open P5Z.ActualLowerNormalizedAtlasOccurrence (integerProfile scalarProfile_support)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalHighRankComplementBlocks (complement quotient_eq fibre)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos log2_count_le)
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy functional residueKernel)

variable {modeOrder : ℕ} {kap zeta kap0 : ℝ} (I : Index modeOrder kap zeta kap0)

/-- Occupation uses the original complete smooth profile, including its
independent trim. It is not occupation of a truncated Fourier polynomial. -/
def liveComplements : Finset Block :=
  (bank (2*I.P.N)).filter (fun C => ∃ n∈fibre I.bv I.i C,
    integerProfile kap 6 I.P.N I.cj kap0 n≠0)

/-- The cap belongs to the counted singleton prime. All rectangle entries
are positive, so a live complementary product is at most the complete one. -/
theorem live_mem_bank (hkap : kap<1) {C : Block}
    (hlive : ∃ n∈fibre I.bv I.i C,
      integerProfile kap 6 I.P.N I.cj kap0 n≠0) : C∈bank (2*I.P.N) := by
  obtain ⟨n,hn,hp⟩ := hlive
  obtain ⟨hrect,howner⟩ := Finset.mem_filter.mp hn
  have hpos (a : Fin (size I.j)) : 0<n a :=
    owns_pos ((mem_rectangle I.bv n).mp hrect a)
  have hcomp : 0<complement I.i n := Finset.prod_pos (fun a _ => hpos a)
  have hle : complement I.i n≤completeProduct n := by
    rw [←quotient_eq I.i n (hpos I.i)]
    exact Nat.div_le_self _ _
  have hcap : completeProduct n≤2*I.P.N :=
    scalarProfile_support kap hkap 6 I.P.N I.cj kap0 hp
  rw [←howner]
  exact owner_mem_bank hcomp (hle.trans hcap)

theorem mem_liveComplements (hkap : kap<1) {C : Block} :
    C∈liveComplements I ↔ ∃ n∈fibre I.bv I.i C,
      integerProfile kap 6 I.P.N I.cj kap0 n≠0 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨live_mem_bank I hkap h,h⟩

theorem original_complement_mem (hkap : kap<1) : I.C∈liveComplements I :=
  (mem_liveComplements I hkap).mpr I.live

/-- Change only the actual complementary block and its actual occupation
proof. In particular final P, chart, ordered HB row, head, trim, mode and
physical word stay fixed. The same selected Rule is evaluated at this C. -/
def onComplement (C : {C // C∈liveComplements I}) : Index modeOrder kap zeta kap0 :=
  { I with C := C.val,live := (Finset.mem_filter.mp C.property).2 }

theorem amplitude_onComplement (C : {C // C∈liveComplements I}) :
    amplitude (onComplement I C)=amplitude I := rfl

theorem scalar_onComplement (C : {C // C∈liveComplements I}) :
    scalar (onComplement I C)=scalar I := rfl

/-- This is a profile-weighted partition. Arbitrary rectangle points need
not have complete product at most 2N; points outside the actual support
vanish in this exact identity instead of entering an invented mother cap. -/
theorem profile_partition (hkap : kap<1)
    (f g : (Fin (size I.j)→ℕ)→ℂ) :
    (∑ C∈liveComplements I,∑ n∈fibre I.bv I.i C,
      f n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*g n)=
      ∑ n∈rectangle I.bv,f n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*g n := by
  have inner (C : Block) :
      (∑ n∈fibre I.bv I.i C,f n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*g n)=
        ∑ n∈rectangle I.bv,if owner (complement I.i n)=C then
          f n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*g n else 0 := by
    rw [fibre,Finset.sum_filter]
  simp_rw [inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : integerProfile kap 6 I.P.N I.cj kap0 n=0
  · simp [hp]
  · have hc : owner (complement I.i n)∈liveComplements I :=
      (mem_liveComplements I hkap).mpr ⟨n,Finset.mem_filter.mpr ⟨hn,rfl⟩,hp⟩
    simp [hc]

/-- The actual source64 ordered rectangle, with the original signed free
coefficient and exact residueN/coprime mean, is the sum of its live fibres.
The HB row coefficient is kept outside this identity, as in source64. -/
theorem occurrenceAtom_partition (K : ℕ) (hkap : kap<1) :
    occurrenceAtom kap 6 I.P.N I.cj K kap0 I.j.val I.bs
      (products I.P) (fun q => (free I.P q:ℂ))=
      ∑ C∈(liveComplements I).attach,original (onComplement I C) K := by
  change (∑ n∈rectangle I.bv,
    hbSlots (I.Z K) I.truncations I.roles n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*
      (∑ q∈products I.P,(free I.P q:ℂ)*residueKernel q I.P.N (completeProduct n)))=
    ∑ C∈(liveComplements I).attach,∑ n∈fibre I.bv I.i C.val,
      hbSlots (I.Z K) I.truncations I.roles n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)*
        (∑ q∈products I.P,(free I.P q:ℂ)*residueKernel q I.P.N (completeProduct n))
  rw [Finset.sum_attach]
  exact (profile_partition I hkap _ _).symm

/-- The complete original HB scalar occurs once, and each fibre uses the
already proved actual Fourier dictionary. This is a finite identity only. -/
theorem original_row_eq_live_fourier (K : ℕ) (hkap : kap<1) :
    P5Z.SmoothChartHBDyadicPartition.scalar I.j.val*
      (if firstMedium (originalMediumLow zeta [I.cj]) (originalMediumHigh zeta [I.cj]) I.bs=none
       then 0 else occurrenceAtom kap 6 I.P.N I.cj K kap0 I.j.val I.bs
        (products I.P) (fun q => (free I.P q:ℂ)))=
      ∑ C∈(liveComplements I).attach,
        P5Z.SmoothChartHBDyadicPartition.scalar I.j.val*
          (∫ xi,amplitude (onComplement I C) xi*
            exactDiscrepancy (fibre I.bv I.i C.val) (products I.P)
              (fun q => (free I.P q:ℂ)) completeProduct I.P.N
              (frequencyMode (onComplement I C) K xi)) := by
  have hg : ¬firstMedium (originalMediumLow zeta [I.cj])
      (originalMediumHigh zeta [I.cj]) I.bs=none := by rw [I.selected]; simp
  rw [if_neg hg,occurrenceAtom_partition I K hkap,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [original_eq_fourier]

/-- One genuine complementary-owner bank, with the literal 2N cap. -/
theorem liveComplement_count (hN : 1<I.P.N) :
    ((liveComplements I).card:ℝ)≤dyadicConstant*logScale (I.P.N:ℝ) := by
  have hc : ((liveComplements I).card:ℝ)≤((bank (2*I.P.N)).card:ℝ) := by
    have hs : liveComplements I⊆bank (2*I.P.N) := fun C hC => (Finset.mem_filter.mp hC).1
    exact_mod_cast Finset.card_le_card hs
  apply hc.trans
  rw [bank_card]
  apply log2_count_le (by exact_mod_cast hN.le : (1:ℝ)≤I.P.N)
  have hs : ((2*I.P.N-1:ℕ):ℝ)≤2*(I.P.N:ℝ) := by
    exact_mod_cast Nat.sub_le (2*I.P.N) 1
  linarith [Nat.cast_nonneg I.P.N]

def fibreCost : ℝ :=
  ‖P5Z.SmoothChartHBDyadicPartition.scalar I.j.val‖*
    ((∫ xi,‖amplitude I xi‖)*scalar I*modulusCost I)

def liveRowCost : ℝ := ∑ C∈(liveComplements I).attach,fibreCost (onComplement I C)

/-- A paid restoring inventory for this actual live row, uniform before
its chart/HB row/head/complement/mode. The one complementary-block count
costs one logarithm beyond c5e5. No arithmetic M norm is supplied as input
or asserted as a conclusion, and outer banks/reserves/tails remain open. -/
theorem live_row_amplitude_cost (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ (modeOrder : ℕ) (kap zeta kap0 : ℝ)
      (I : Index modeOrder kap zeta kap0),kap<1 → 1<I.P.N →
      I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
      liveRowCost I≤
        C*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*logScale (I.P.N:ℝ)^4 := by
  obtain ⟨C0,hC0,HC⟩ := restored_row_amplitude_cost omega T ho
  refine ⟨dyadicConstant*C0,mul_nonneg dyadicConstant_pos.le hC0,?_⟩
  intro modeOrder kap zeta kap0 I hkap hN hw hT he hell
  let B : ℝ := C0*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*
    logScale (I.P.N:ℝ)^3
  have hL : 0≤logScale (I.P.N:ℝ) :=
    zero_le_one.trans (logScale_one_le (by exact_mod_cast hN.le))
  have hlog : 0≤Real.log ((I.P.N:ℝ)+2) := Real.log_nonneg (by linarith only [show 0≤(I.P.N:ℝ) from Nat.cast_nonneg _])
  have hH := height_one_le I.P.N
  have hB : 0≤B := by dsimp [B]; positivity
  have one (C : {C // C∈liveComplements I}) : fibreCost (onComplement I C)≤B :=
    HC modeOrder kap zeta kap0 (onComplement I C) hkap hN hw hT he hell
  calc
    liveRowCost I≤∑ C∈(liveComplements I).attach,B :=
      Finset.sum_le_sum (fun C _ => one C)
    _=((liveComplements I).card:ℝ)*B := by
      simp only [Finset.sum_const,Finset.card_attach,nsmul_eq_mul]
    _≤(dyadicConstant*logScale (I.P.N:ℝ))*B :=
      mul_le_mul_of_nonneg_right (liveComplement_count I hN) hB
    _=(dyadicConstant*C0)*Real.log ((I.P.N:ℝ)+2)^72*profileHeight I.P.N^6*
        logScale (I.P.N:ℝ)^4 := by dsimp [B]; ring

end
end ImbalancedChen.P1OriginalSingletonMediumLiveRowInventory
