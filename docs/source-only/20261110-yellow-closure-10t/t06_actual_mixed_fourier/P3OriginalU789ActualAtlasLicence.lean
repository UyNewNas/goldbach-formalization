import ImbalancedChen.P3OriginalU789ComplexChartFourier
import ImbalancedChen.P5ActualHBAtlasScalarInventory
import ImbalancedChen.P5ActualSingletonPrimeTestFamily
import ImbalancedChen.P5ActualLowerNormalizedBlockGeometry

/-!
SUPPLEMENT / SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Actual original U789 HB banks, owners, unit/right-closed blocks, signed
HB scalars, original chart labels AND the separate full smooth label grid.
The extra smooth grid is restored exactly and its logarithmic cardinality
is charged, rather than calling a fixed-label child sum one.
All source geometry/phase and mixed/Fourier inputs are constructed in the
two preceding supplements; no abstract Family or scalar-norm field occurs.
-/
namespace ImbalancedChen.P3OriginalU789ActualAtlasLicence
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P3OriginalU789AffinePhaseBudget P3OriginalU789ComplexChartFourier
open P3ActualHBChildMixedFourier P3HBSmoothThreeWayRatioTwo P3HBDyadicTensorPartition
open P5OriginalU789SmoothLogSources P5OriginalU789SmoothChartRoughOne
open P5Z.ActualHBAtlasScalarInventory P5Z.HBRightClosedDyadicRoles
open P5Z.ActualHBDyadicOccurrenceFamily P5Z.ActualHBDyadicProductWindow
open P5Z.ActualEtaPsiOccurrenceBudget P5Z.ActualSingletonPrimeTestFamily
open P5Z.GroupedOccurrenceLogShift P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.ActualEuclideanPhysicalFourier P5Z.AllRankCauchyCubeTail
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.CompleteProductTailDivisorBudgets

def smoothLevel (cap : ℕ) : ℕ := Nat.log2 (cap-1)+1
abbrev SmoothLabels (d cap : ℕ) := Fin d → Fin (smoothLevel cap+1)

def smoothGrid {d cap : ℕ} (label : SmoothLabels d cap) (child : Fin d → Fin 3)
    (n : Fin d → ℕ) : ℂ :=
  ∏ a : Fin d,smoothCoord (fun t => (chi t : ℂ)) (n a : ℝ) (label a).val (child a)

theorem actual_chi_small (t : ℝ) (ht : t≤1) : (chi t : ℂ)=1 := by
  rw [P5Z.ActualSingletonPrimeTestFamily.chi_one ht]
  norm_num
theorem actual_chi_large (t : ℝ) (ht : 2≤t) : (chi t : ℂ)=0 := by
  rw [P5Z.ActualSingletonPrimeTestFamily.chi_zero ht]
  norm_num

/-- Both independent finite sums are present. In particular the first
sum below is over smooth dyadic labels, not over hard HB block labels. -/
theorem smoothGrid_restores {d cap : ℕ} (n : Fin d → ℕ)
    (hn : ∀ a,1≤n a) (hhi : ∀ a,(n a : ℝ)≤(2 : ℝ)^smoothLevel cap) :
    (∑ label : SmoothLabels d cap,∑ child : Fin d → Fin 3,smoothGrid label child n)=1 := by
  have hchild (label : SmoothLabels d cap) :
      (∑ child : Fin d → Fin 3,smoothGrid label child n) =
        ∏ a : Fin d,dyadicPiece (fun t => (chi t : ℂ)) (n a : ℝ) (label a).val := by
    unfold smoothGrid
    rw [← Fintype.prod_sum]
    simp_rw [smoothCoord_sum]
  simp_rw [hchild]
  rw [← Fintype.prod_sum]
  apply Finset.prod_eq_one
  intro a ha
  rw [Fin.sum_univ_eq_sum_range]
  exact dyadic_one (fun t => (chi t : ℂ)) (n a : ℝ) (smoothLevel cap)
    actual_chi_small actual_chi_large (by exact_mod_cast hn a) (hhi a)

/-- Exact complex finite source restoration, valid for the actual
full signed count/mean kernel after it has been fixed. No positivity or
monotonicity of a signed PP functional is used. -/
theorem finite_source_grid_restores {ι : Type*} {d cap : ℕ}
    (S : Finset ι) (n : ι → Fin d → ℕ) (coefficient kernel : ι → ℂ)
    (hn : ∀ t∈S,∀ a,1≤n t a)
    (hhi : ∀ t∈S,∀ a,(n t a : ℝ)≤(2 : ℝ)^smoothLevel cap) :
    (∑ label : SmoothLabels d cap,∑ child : Fin d → Fin 3,
      ∑ t∈S,coefficient t*smoothGrid label child (n t)*kernel t) =
      ∑ t∈S,coefficient t*kernel t := by
  calc
    _ = ∑ label : SmoothLabels d cap,∑ t∈S,∑ child : Fin d → Fin 3,
        coefficient t*smoothGrid label child (n t)*kernel t := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact Finset.sum_comm
    _ = ∑ t∈S,∑ label : SmoothLabels d cap,∑ child : Fin d → Fin 3,
        coefficient t*smoothGrid label child (n t)*kernel t := Finset.sum_comm
    _ = ∑ t∈S,coefficient t*kernel t := by
      apply Finset.sum_congr rfl
      intro t ht
      calc
        _ = coefficient t*(∑ label : SmoothLabels d cap,
            ∑ child : Fin d → Fin 3,smoothGrid label child (n t))*kernel t := by
          simp only [Finset.mul_sum,Finset.sum_mul]
        _ = coefficient t*kernel t := by rw [smoothGrid_restores (n t) (hn t ht) (hhi t ht)]; ring

/-- Original hard HB blocks keep their own unit/right-closed convention. -/
def blockBase : Block → ℝ
  | .unit => 1
  | .dyadic j => (2 : ℝ)^j

theorem blockBase_pos (b : Block) : 0<blockBase b := by cases b <;> simp [blockBase] <;> positivity

theorem owns_closed_bounds {b : Block} {n : ℕ} (hn : Owns b n) :
    blockBase b≤(n : ℝ) ∧ (n : ℝ)≤2*blockBase b := by
  cases b with
  | unit => simp only [Owns] at hn; subst n; norm_num [blockBase]
  | dyadic j =>
      change 2^j<n ∧ n≤2^(j+1) at hn
      constructor
      · exact_mod_cast hn.1.le
      · have h := hn.2
        rw [pow_succ] at h
        exact_mod_cast h

theorem bank_owns_smooth_cap {cap n : ℕ} {b : Block}
    (hb : b∈bank cap) (hn : Owns b n) : 1≤n ∧ (n : ℝ)≤(2 : ℝ)^smoothLevel cap := by
  cases b with
  | unit =>
      change n=1 at hn
      subst n
      exact ⟨le_rfl,one_le_pow₀ (by norm_num)⟩
  | dyadic j =>
      have hj : j<Nat.log2 (cap-1)+1 := by
        have hmem : Block.dyadic j∈(Finset.range (Nat.log2 (cap-1)+1)).image Block.dyadic :=
          (Finset.mem_insert.mp hb).resolve_left (by simp)
        obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hmem
        have heq : k=j := Block.dyadic.inj hkj
        subst k
        exact Finset.mem_range.mp hk
      change 2^j<n ∧ n≤2^(j+1) at hn
      refine ⟨by have := Nat.one_le_pow j 2 (by omega); omega,?_⟩
      have hh : n≤2^smoothLevel cap := hn.2.trans
        (Nat.pow_le_pow_right (by norm_num) (by unfold smoothLevel; omega))
      exact_mod_cast hh

/-- The actual inventory's positional block dictionary, not a separate
convenient owner assignment, supplies the full smooth grid's support. -/
theorem pieceBlocks_mem_bank (cap : ℕ) : ∀ k : ℕ,∀ cs∈hbBank cap k,
    ∀ a : Fin (dimension cs),pieceBlocks cs a∈bank cap := by
  intro k
  induction k with
  | zero =>
      intro cs hcs a
      have heq : cs=[] := by simpa only [hbBank,Finset.mem_singleton] using hcs
      subst cs
      exact Fin.elim0 a
  | succ k ih =>
      intro cs hcs a
      obtain ⟨⟨c,ds⟩,hcd,rfl⟩ := Finset.mem_image.mp hcs
      obtain ⟨hc,hds⟩ := Finset.mem_product.mp hcd
      obtain ⟨hj,hbs⟩ := Finset.mem_sigma.mp hc
      refine Fin.addCases ?_ ?_ a
      · intro i
        exact (blockWords_spec cap _ _ hbs).2 (c.2.get i) (List.get_mem _ _)
      · intro i
        exact ih ds hds i

def pieceScales (cs : List Choice) (a : Fin (dimension cs)) : ℝ := blockBase (pieceBlocks cs a)
theorem pieceScales_pos (cs : List Choice) (a : Fin (dimension cs)) : 0<pieceScales cs a :=
  blockBase_pos _

abbrev ActualPieces (s : Source) (cap : ℕ) := {cs : List Choice // cs∈hbBank cap (rank s)}

def actualOwner (s : Source) (cap : ℕ) (cs : ActualPieces s cap) :
    Fin (dimension cs.val) → Fin (rank s) :=
  rankOwner (hbBank_spec cap (rank s) cs.val cs.property).1

def actualPiece (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    V (dimension cs.val) → ℂ :=
  complexChart s N width (actualOwner s cap cs) (pieceScales cs.val) (originalR js (rank s)) κ₀
    (fun a => Real.log (pieceScales cs.val a/(2 : ℝ)^(label a).val)) child
    (∑ i,t i*Real.log (groupBase (actualOwner s cap cs) (pieceScales cs.val) i))
    (fun a => t (actualOwner s cap cs a))

def actualRectangle (s : Source) (cap : ℕ) (cs : ActualPieces s cap) :=
  P5Z.ActualLowerNormalizedBlockGeometry.rectangle (pieceBlocks cs.val)

theorem actualRectangle_grid_restores (s : Source) (cap : ℕ) (cs : ActualPieces s cap)
    (n : Fin (dimension cs.val) → ℕ) (hn : n∈actualRectangle s cap cs) :
    (∑ label : SmoothLabels (dimension cs.val) cap,
      ∑ child : Fin (dimension cs.val) → Fin 3,smoothGrid label child n)=1 := by
  have ho (a : Fin (dimension cs.val)) : Owns (pieceBlocks cs.val a) (n a) :=
    P5Z.ActualLowerNormalizedBlockGeometry.rectangle_owns (pieceBlocks cs.val) hn a
  have hb (a : Fin (dimension cs.val)) :=
    bank_owns_smooth_cap (pieceBlocks_mem_bank cap (rank s) cs.val cs.property a) (ho a)
  exact smoothGrid_restores n (fun a => (hb a).1) (fun a => (hb a).2)

def actualIntegerWeight (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (n : Fin (dimension cs.val) → ℕ) : ℂ :=
  (integerGeometry s N width (actualOwner s cap cs) (originalR js (rank s)) κ₀ n : ℂ) *
    Complex.exp (((∑ i,t i*Real.log (integerGroupProduct (actualOwner s cap cs) n i : ℝ) : ℝ) : ℂ)*Complex.I)

/-- The actual complex original-group phase and normalized integer
geometry are independent of the auxiliary smooth labels/children. -/
theorem actualPiece_integer (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (n : Fin (dimension cs.val) → ℕ) (hn : n∈actualRectangle s cap cs) :
    actualPiece s N cap width js cs label child κ₀ t
      (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n)) =
      actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n := by
  let o := actualOwner s cap cs
  let U := pieceScales cs.val
  let z := logOccurrence U n
  have hU : ∀ a,0<U a := pieceScales_pos cs.val
  have ho (a : Fin (dimension cs.val)) : Owns (pieceBlocks cs.val a) (n a) :=
    P5Z.ActualLowerNormalizedBlockGeometry.rectangle_owns (pieceBlocks cs.val) hn a
  have hb (a : Fin (dimension cs.val)) := owns_closed_bounds (ho a)
  have hnpos : ∀ a,0<n a := fun a => by exact_mod_cast (hU a).trans_le (hb a).1
  have hraw := complexChart_integer_atom s N width o U (originalR js (rank s)) κ₀
    (fun a => (label a).val) child
    (∑ i,t i*Real.log (groupBase o U i)) (fun a => t (o a)) n hU
    (fun a => (hb a).1) (fun a => (hb a).2)
  have hphi := original_group_phase s o U hU t z
  simp_rw [groupProduct_logOccurrence o U n hU hnpos] at hphi
  have hmode : Complex.exp (((∑ i,t i*Real.log (groupBase o U i) : ℝ) : ℂ)*Complex.I)*
      occurrenceMode U n (fun a => t (o a)) =
      Complex.exp (((∑ i,t i*Real.log (integerGroupProduct o n i : ℝ) : ℝ) : ℂ)*Complex.I) := by
    rw [hphi]
    simp only [Complex.ofReal_add,add_mul,Complex.exp_add,Complex.ofReal_sum,
      Finset.sum_mul,Complex.exp_sum,occurrenceMode,z]
  change actualPiece s N cap width js cs label child κ₀ t (WithLp.toLp 2 z) = _ at hraw
  apply hraw.trans
  change (integerGeometry s N width o (originalR js (rank s)) κ₀ n : ℂ)*
      Complex.exp (((∑ i,t i*Real.log (groupBase o U i) : ℝ) : ℂ)*Complex.I)*
      occurrenceMode U n (fun a => t (o a))*smoothGrid label child n =
        actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n
  rw [mul_assoc _
    (Complex.exp (((∑ i,t i*Real.log (groupBase o U i) : ℝ) : ℂ)*Complex.I))
    (occurrenceMode U n (fun a => t (o a))),hmode]
  rfl

/-- Exact finite actual source insertion on the whole canonical HB
rectangle. The kernel can be the full SAME-rho count-minus-exact-mean;
neither its signs nor any source arithmetic filters are differentiated. -/
theorem actual_rectangle_source_restores (s : Source) (N cap : ℕ) (width : ℝ)
    (js : List ℕ) (cs : ActualPieces s cap) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (coefficient kernel : (Fin (dimension cs.val) → ℕ) → ℂ) :
    (∑ label : SmoothLabels (dimension cs.val) cap,
      ∑ child : Fin (dimension cs.val) → Fin 3,
        ∑ n∈actualRectangle s cap cs,coefficient n*
          actualPiece s N cap width js cs label child κ₀ t
            (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n))*kernel n) =
      ∑ n∈actualRectangle s cap cs,coefficient n*actualIntegerWeight s N cap width js cs κ₀ t n*kernel n := by
  have hh := finite_source_grid_restores (actualRectangle s cap cs) id
    (fun n => coefficient n*actualIntegerWeight s N cap width js cs κ₀ t n) kernel
    (fun n hn a => (bank_owns_smooth_cap
      (pieceBlocks_mem_bank cap (rank s) cs.val cs.property a)
      (P5Z.ActualLowerNormalizedBlockGeometry.rectangle_owns (pieceBlocks cs.val) hn a)).1)
    (fun n hn a => (bank_owns_smooth_cap
      (pieceBlocks_mem_bank cap (rank s) cs.val cs.property a)
      (P5Z.ActualLowerNormalizedBlockGeometry.rectangle_owns (pieceBlocks cs.val) hn a)).2)
  calc
    _ = ∑ label : SmoothLabels (dimension cs.val) cap,
        ∑ child : Fin (dimension cs.val) → Fin 3,
          ∑ n∈actualRectangle s cap cs,
            (coefficient n*actualIntegerWeight s N cap width js cs κ₀ t n)*smoothGrid label child n*kernel n := by
      apply Finset.sum_congr rfl
      intro label hlabel
      apply Finset.sum_congr rfl
      intro child hchild
      apply Finset.sum_congr rfl
      intro n hn
      rw [actualPiece_integer s N cap width js cs label child κ₀ t n hn]
      ring
    _ = _ := hh

theorem actualPiece_smooth (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    ContDiff ℝ ∞ (actualPiece s N cap width js cs label child κ₀ t) :=
  complexChart_smooth s N width _ _ _ κ₀ _ child _ _

theorem actualPiece_compact (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    HasCompactSupport (actualPiece s N cap width js cs label child κ₀ t) :=
  complexChart_compact s N width _ _ _ κ₀ _ child _ _

/-- A true retained ORIGINAL-group box licenses every actual occurrence
phase; its owner is fixed by the HB positional dictionary. -/
theorem exists_actual_piece_budget :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Source) (N cap : ℕ) (width H : ℝ),
      1≤Real.log (N : ℝ) → 0<width → width≤maximumWidth → 0≤H →
      ∀ (js : List ℕ) (cs : ActualPieces s cap)
        (label : SmoothLabels (dimension cs.val) cap) (child : Fin (dimension cs.val) → Fin 3)
        (κ₀ : ℝ) (t : Fin (rank s) → ℝ),t∈(outsideCube (rank s) H)ᶜ →
      mixedD (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) ≤
        C*(1/width+H)^48 := by
  obtain ⟨C,hC,hb⟩ := exists_actual_complex_fourier_budget
  refine ⟨C,hC,?_⟩
  intro s N cap width H hell hw hwMax hH js cs label child κ₀ t ht
  have hdim := (hbBank_spec cap (rank s) cs.val cs.property).2.2
  have hf : ∀ a,|t (actualOwner s cap cs a)|≤H :=
    fun a => retained_frequency_bound ht _
  have hwOne : width≤1 := hwMax.trans (by norm_num [maximumWidth])
  exact (hb s N (dimension cs.val) width H hell hw hwOne hH
    (actualOwner s cap cs) (pieceScales cs.val) (originalR js (rank s)) κ₀ _ child _ _
    (pieceScales_pos cs.val) (originalR_pos js (rank s)) hf
    (by have := source_rank_le_four s; omega)).1

/-- Literal hard-bank scalar norm. The extra smooth labels and children
are NOT counted by this definition; they are charged separately below. -/
def sourceScalarMass (s : Source) (cap : ℕ) : ℝ :=
  ∑ _js∈chartBank cap (rank s),∑ cs∈hbBank cap (rank s),‖hbScalar cs‖

theorem sourceScalarMass_le (s : Source) (cap : ℕ) {X : ℝ}
    (hX : 1≤X) (hcap : (cap : ℝ)≤6*X) :
    sourceScalarMass s cap≤inventoryConstant 4*logScale X^28 := by
  let k : Fin 5 := ⟨rank s,by have := source_rank_le_four s; omega⟩
  have hsingle : sourceScalarMass s cap≤
      ∑ k : Fin 5,∑ _js∈chartBank cap k.val,∑ cs∈hbBank cap k.val,‖hbScalar cs‖ := by
    apply Finset.single_le_sum (fun i hi => ?_) (Finset.mem_univ k)
    exact Finset.sum_nonneg (fun js hjs => Finset.sum_nonneg (fun cs hcs => norm_nonneg _))
  exact hsingle.trans (by simpa using complete_inventory_mass_le 4 cap hX hcap)

def atlasMixedMass (s : Source) (N cap : ℕ) (width : ℝ) (κ₀ : ℝ)
    (t : Fin (rank s) → ℝ) : ℝ :=
  ∑ js∈chartBank cap (rank s),∑ cs∈(hbBank cap (rank s)).attach,
    ‖hbScalar cs.val‖ *
      ∑ label : SmoothLabels (dimension cs.val) cap,
        ∑ child : Fin (dimension cs.val) → Fin 3,
          mixedD (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t)

def atlasFourierMass (s : Source) (N cap : ℕ) (width : ℝ) (κ₀ : ℝ)
    (t : Fin (rank s) → ℝ) : ℝ :=
  ∑ js∈chartBank cap (rank s),∑ cs∈(hbBank cap (rank s)).attach,
    ‖hbScalar cs.val‖ *
      ∑ label : SmoothLabels (dimension cs.val) cap,
        ∑ child : Fin (dimension cs.val) → Fin 3,
          (∫ ξ : Fin (dimension cs.val) → ℝ,
            ‖physicalFourier (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) ξ‖) /
              frequencyScale^(dimension cs.val)

theorem atlasFourierMass_le_mixedMass (s : Source) (N cap : ℕ) (width : ℝ)
    (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    atlasFourierMass s N cap width κ₀ t≤atlasMixedMass s N cap width κ₀ t := by
  unfold atlasFourierMass atlasMixedMass
  apply Finset.sum_le_sum
  intro js hjs
  apply Finset.sum_le_sum
  intro cs hcs
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro label hlabel
  apply Finset.sum_le_sum
  intro child hchild
  exact (physicalFourier_normalized_l1_le (dimension cs.val)
    (actualPiece s N cap width js cs label child κ₀ t)
    (actualPiece_smooth s N cap width js cs label child κ₀ t)
    (actualPiece_compact s N cap width js cs label child κ₀ t)).trans
      (div_le_self (mixedD_nonneg _ _) (one_le_pow₀ (by norm_num)))

abbrev Positions (s : Source) (cap : ℕ) := (cs : ActualPieces s cap) →
  SmoothLabels (dimension cs.val) cap → (Fin (dimension cs.val) → Fin 3) → V (dimension cs.val)

def atlasTruncationMass (s : Source) (N cap : ℕ) (width : ℝ) (κ₀ : ℝ)
    (t : Fin (rank s) → ℝ) (H : ℝ) (position : Positions s cap) : ℝ :=
  ∑ js∈chartBank cap (rank s),∑ cs∈(hbBank cap (rank s)).attach,
    ‖hbScalar cs.val‖ *
      ∑ label : SmoothLabels (dimension cs.val) cap,
        ∑ child : Fin (dimension cs.val) → Fin 3,
          ‖actualPiece s N cap width js cs label child κ₀ t (position cs label child)-
            truncatedPhysical (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t)
              H (position cs label child)‖

theorem atlasTruncationMass_le (s : Source) (N cap : ℕ) (width : ℝ) (κ₀ : ℝ)
    (t : Fin (rank s) → ℝ) (H : ℝ) (hH : 0<H) (position : Positions s cap) :
    atlasTruncationMass s N cap width κ₀ t H position≤
      (24/H)*atlasMixedMass s N cap width κ₀ t := by
  unfold atlasTruncationMass atlasMixedMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro js hjs
  apply Finset.sum_le_sum
  intro cs hcs
  apply Finset.sum_le_sum
  intro label hlabel
  apply Finset.sum_le_sum
  intro child hchild
  let f := actualPiece s N cap width js cs label child κ₀ t
  have hdim : dimension cs.val≤24 := by
    have hh := (hbBank_spec cap (rank s) cs.val cs.property).2.2
    have := source_rank_le_four s
    omega
  have htail := actual_uniform_truncation_error (dimension cs.val) f
    (actualPiece_smooth s N cap width js cs label child κ₀ t)
    (actualPiece_compact s N cap width js cs label child κ₀ t) H hH (position cs label child)
  have hD := mixedD_nonneg (dimension cs.val) f
  have hbound : ‖f (position cs label child)-
      truncatedPhysical (dimension cs.val) f H (position cs label child)‖≤
      (24/H)*mixedD (dimension cs.val) f := by
    calc
      _ ≤ (dimension cs.val : ℝ)*mixedD (dimension cs.val) f/H := htail
      _ ≤ (24 : ℝ)*mixedD (dimension cs.val) f/H :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hdim) hD) hH.le
      _ = _ := by ring
  calc
    _ ≤ ‖hbScalar cs.val‖*((24/H)*mixedD (dimension cs.val) f) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by ring

/-- The actual complete finite atlas, including its independent full
smooth grid, has an explicit norm budget. The extra log^24 is paid;
it is never hidden inside the old hard-bank log^28 inventory. -/
theorem exists_actual_atlas_budget :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Source) (N cap : ℕ) (width H X : ℝ),
      1≤Real.log (N : ℝ) → 0<width → width≤maximumWidth → 0≤H →
      1≤X → (cap : ℝ)≤6*X →
      ∀ (κ₀ : ℝ) (t : Fin (rank s) → ℝ),t∈(outsideCube (rank s) H)ᶜ →
      atlasMixedMass s N cap width κ₀ t≤C*logScale X^52*(1/width+H)^48 := by
  obtain ⟨C₀,hC₀,hpiece⟩ := exists_actual_piece_budget
  let C : ℝ := (3 : ℝ)^24*C₀*inventoryConstant 4*dyadicConstant^24
  refine ⟨C,by
    have hi := inventoryConstant_nonneg 4
    have hd := dyadicConstant_pos
    dsimp [C]
    positivity,?_⟩
  intro s N cap width H X hell hw hwMax hH hX hcap κ₀ t ht
  let L : ℝ := dyadicConstant*logScale X
  have hL : 1≤L := by
    have hc : 1≤dyadicConstant := by
      unfold dyadicConstant
      have hp := Real.log_pos (by norm_num : (1 : ℝ)<2)
      linarith [div_nonneg (by norm_num : (0 : ℝ)≤1) hp.le]
    exact one_le_mul hc (logScale_one_le hX)
  have hcount : ((smoothLevel cap+1 : ℕ) : ℝ)≤L := by
    have hm0 : ((cap-1 : ℕ) : ℝ)≤(cap : ℝ) := by exact_mod_cast Nat.sub_le cap 1
    have hm : ((cap-1 : ℕ) : ℝ)≤6*X := hm0.trans hcap
    simpa [smoothLevel,L,Nat.add_assoc] using log2_count_le hX (cap-1) hm
  have hterm (js : List ℕ) (cs : ActualPieces s cap) :
      (∑ label : SmoothLabels (dimension cs.val) cap,
        ∑ child : Fin (dimension cs.val) → Fin 3,
          mixedD (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t)) ≤
      (3 : ℝ)^24*L^24*C₀*(1/width+H)^48 := by
    have hdim : dimension cs.val≤24 := by
      have hd := (hbBank_spec cap (rank s) cs.val cs.property).2.2
      have := source_rank_le_four s
      omega
    calc
      _ ≤ ∑ _label : SmoothLabels (dimension cs.val) cap,
          ∑ _child : Fin (dimension cs.val) → Fin 3,C₀*(1/width+H)^48 :=
        Finset.sum_le_sum (fun label _ => Finset.sum_le_sum
          (fun child _ => hpiece s N cap width H hell hw hwMax hH js cs label child κ₀ t ht))
      _ = ((smoothLevel cap+1 : ℕ) : ℝ)^(dimension cs.val) *
          (3 : ℝ)^(dimension cs.val)*(C₀*(1/width+H)^48) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        ring
      _ ≤ L^24*(3 : ℝ)^24*(C₀*(1/width+H)^48) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul
        · exact (pow_le_pow_left₀ (by positivity) hcount _).trans
            (pow_le_pow_right₀ hL hdim)
        · exact pow_le_pow_right₀ (by norm_num) hdim
        · positivity
        · positivity
      _ = _ := by ring
  calc
    atlasMixedMass s N cap width κ₀ t ≤
        sourceScalarMass s cap*((3 : ℝ)^24*L^24*C₀*(1/width+H)^48) := by
      unfold atlasMixedMass sourceScalarMass
      simp_rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro js hjs
      rw [← Finset.sum_attach (hbBank cap (rank s))
        (fun cs => ‖hbScalar cs‖*((3 : ℝ)^24*L^24*C₀*(1/width+H)^48))]
      apply Finset.sum_le_sum
      intro cs hcs
      exact mul_le_mul_of_nonneg_left (hterm js cs) (norm_nonneg _)
    _ ≤ (inventoryConstant 4*logScale X^28)*
        ((3 : ℝ)^24*L^24*C₀*(1/width+H)^48) :=
      mul_le_mul_of_nonneg_right (sourceScalarMass_le s cap hX hcap) (by positivity)
    _ = C*logScale X^52*(1/width+H)^48 := by
      dsimp [C,L]
      rw [mul_pow,show (52 : ℕ)=28+24 by omega,pow_add]
      ring

/-- Actual global source cap and its fixed-linear scale. The source's
unchanged productUpper is supported below exp(maximumWidth)*N. -/
def sourceCap (N : ℕ) : ℕ := Nat.ceil (Real.exp maximumWidth*(N : ℝ))
def sourceScale (N : ℕ) : ℝ := (Real.exp maximumWidth+2)*((N : ℝ)+1)

theorem sourceScale_one_le (N : ℕ) : 1≤sourceScale N := by
  have he := Real.exp_pos maximumWidth
  have hn := Nat.cast_nonneg N
  unfold sourceScale
  nlinarith

theorem sourceCap_le (N : ℕ) : (sourceCap N : ℝ)≤6*sourceScale N := by
  have he := Real.exp_pos maximumWidth
  have hn := Nat.cast_nonneg N
  have hc := (Nat.ceil_lt_add_one (mul_nonneg he.le hn)).le
  unfold sourceCap sourceScale
  nlinarith

/-- The genuine finite original prime carrier, before any HB factor
tuple, lies under this same cap. No arithmetic phase/rho is involved. -/
theorem original_prime_le_sourceCap (s : Source) (N : ℕ)
    (u : Fin (rank s) → Fin (N+1)) (i : Fin (rank s)) : (u i).val≤sourceCap N := by
  have hmax : 0≤maximumWidth := by norm_num [maximumWidth]
  have he : 1≤Real.exp maximumWidth := Real.one_le_exp hmax
  have hN : (N : ℝ)≤Real.exp maximumWidth*(N : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)
  have hc : Real.exp maximumWidth*(N : ℝ)≤(sourceCap N : ℝ) := Nat.le_ceil _
  have hu : (u i).val≤N := Nat.le_of_lt_succ (u i).isLt
  have huR : ((u i).val : ℝ)≤(N : ℝ) := by exact_mod_cast hu
  exact_mod_cast huR.trans (hN.trans hc)

/-- One explicit integer resolution is selected from N and fixed B,
before source labels, phases, HB tuples, arithmetic signs and rho. -/
def resolution (B N : ℕ) : ℕ :=
  Nat.ceil (logScale (sourceScale N)^B/maximumWidth)
def chosenWidth (B N : ℕ) : ℝ := 1/(resolution B N+1 : ℝ)
def chosenRadius (F N : ℕ) : ℝ := logScale (sourceScale N)^F

theorem chosenWidth_legal (B N : ℕ) : 0<chosenWidth B N ∧ chosenWidth B N≤maximumWidth := by
  have hm : 0<maximumWidth := by norm_num [maximumWidth]
  have hL : 1≤logScale (sourceScale N) := logScale_one_le (sourceScale_one_le N)
  have hp : 1≤logScale (sourceScale N)^B := one_le_pow₀ hL
  have hc : logScale (sourceScale N)^B/maximumWidth≤(resolution B N : ℝ) :=
    Nat.le_ceil _
  have hcm := (div_le_iff₀ hm).mp hc
  have hr : 0<(resolution B N+1 : ℝ) := by positivity
  refine ⟨one_div_pos.mpr hr,?_⟩
  unfold chosenWidth
  apply (div_le_iff₀ hr).mpr
  nlinarith

theorem chosen_scale_bound (B F N : ℕ) :
    1/chosenWidth B N+chosenRadius F N ≤
      (1/maximumWidth+3)*logScale (sourceScale N)^(max B F) := by
  have hm : 0<maximumWidth := by norm_num [maximumWidth]
  have hL : 1≤logScale (sourceScale N) := logScale_one_le (sourceScale_one_le N)
  have hp : 1≤logScale (sourceScale N)^(max B F) := one_le_pow₀ hL
  have hb : logScale (sourceScale N)^B≤logScale (sourceScale N)^(max B F) :=
    pow_le_pow_right₀ hL (le_max_left _ _)
  have hf : logScale (sourceScale N)^F≤logScale (sourceScale N)^(max B F) :=
    pow_le_pow_right₀ hL (le_max_right _ _)
  have hc : (resolution B N : ℝ)≤logScale (sourceScale N)^B/maximumWidth+1 :=
    (Nat.ceil_lt_add_one (div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hm.le)).le
  have hi : 0≤1/maximumWidth := one_div_nonneg.mpr hm.le
  have hdiv := mul_le_mul_of_nonneg_right hb hi
  simp only [chosenWidth,one_div_one_div,chosenRadius,div_eq_mul_inv] at *
  push_cast
  nlinarith

/-- Complete actual source-atlas mixed/Fourier cost at the explicit
integer resolution and the actual retained phase radius. The logarithmic
degree includes hard inventory28, independent smooth labels24, and all
48 derivative orders of the actual width/phase factors. -/
theorem exists_chosen_actual_source_atlas_budget (B F : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Source) (N : ℕ),1≤Real.log (N : ℝ) →
      ∀ (κ₀ : ℝ) (t : Fin (rank s) → ℝ),
      t∈(outsideCube (rank s) (chosenRadius F N))ᶜ →
      atlasMixedMass s N (sourceCap N) (chosenWidth B N) κ₀ t ≤
        C*logScale (sourceScale N)^(52+48*max B F) := by
  obtain ⟨C₀,hC₀,hb⟩ := exists_actual_atlas_budget
  let C : ℝ := C₀*(1/maximumWidth+3)^48
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s N hell κ₀ t ht
  have hwidth := chosenWidth_legal B N
  have hL : 1≤logScale (sourceScale N) := logScale_one_le (sourceScale_one_le N)
  have hscale := chosen_scale_bound B F N
  have h0 : 0≤1/chosenWidth B N+chosenRadius F N := by
    have hrad : 0≤chosenRadius F N := pow_nonneg (zero_le_one.trans hL) F
    exact add_nonneg (one_div_nonneg.mpr hwidth.1.le) hrad
  have hpow := pow_le_pow_left₀ h0 hscale 48
  have h := hb s N (sourceCap N) (chosenWidth B N) (chosenRadius F N) (sourceScale N)
    hell hwidth.1 hwidth.2 (pow_nonneg (zero_le_one.trans hL) F)
    (sourceScale_one_le N) (sourceCap_le N) κ₀ t ht
  calc
    _ ≤ C₀*logScale (sourceScale N)^52*(1/chosenWidth B N+chosenRadius F N)^48 := h
    _ ≤ C₀*logScale (sourceScale N)^52*
        ((1/maximumWidth+3)*logScale (sourceScale N)^(max B F))^48 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C*logScale (sourceScale N)^(52+48*max B F) := by
      dsimp [C]
      rw [mul_pow,← pow_mul,show 48*max B F=max B F*48 by omega,pow_add]
      ring

/-- Actual finite source licences at the chosen integer resolution:
true mixed integrals, total normalized Fourier L1 and geometric H-tail
all share the same explicit pre-N logarithmic budget. -/
theorem exists_chosen_actual_source_fourier_licence (B F : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Source) (N : ℕ),1≤Real.log (N : ℝ) →
      ∀ (κ₀ : ℝ) (t : Fin (rank s) → ℝ),
      t∈(outsideCube (rank s) (chosenRadius F N))ᶜ →
      atlasMixedMass s N (sourceCap N) (chosenWidth B N) κ₀ t ≤
        C*logScale (sourceScale N)^(52+48*max B F) ∧
      atlasFourierMass s N (sourceCap N) (chosenWidth B N) κ₀ t ≤
        C*logScale (sourceScale N)^(52+48*max B F) ∧
      ∀ H : ℝ,0<H → ∀ position : Positions s (sourceCap N),
        atlasTruncationMass s N (sourceCap N) (chosenWidth B N) κ₀ t H position ≤
          (24/H)*(C*logScale (sourceScale N)^(52+48*max B F)) := by
  obtain ⟨C,hC,hb⟩ := exists_chosen_actual_source_atlas_budget B F
  refine ⟨C,hC,?_⟩
  intro s N hell κ₀ t ht
  have h := hb s N hell κ₀ t ht
  refine ⟨h,(atlasFourierMass_le_mixedMass s N (sourceCap N) (chosenWidth B N) κ₀ t).trans h,?_⟩
  intro H hH position
  exact (atlasTruncationMass_le s N (sourceCap N) (chosenWidth B N) κ₀ t H hH position).trans
    (mul_le_mul_of_nonneg_left h (by positivity))

/-- Existing actual rough insertion, now instantiated with the actual
chosen resolution. Its threshold still precedes all six source labels,
original chart labels, prime tuples and every phase/kernel multiplier. -/
theorem eventually_chosen_source_rough_one (B K : ℕ) (hK : 4≤K) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ s : Source,
      ∀ js∈chartBank N (rank s),∀ u∈Part3.labelledPrimeTuples (rank s) N,
      sourceWeight s N (chosenWidth B N) u≠0 →
      P5Z.ExactOriginalSmoothDyadicPartition.tupleProfile chi js (primeWord u)≠0 →
      Part3.AllKLambdaChartCorrection.roughWord (beforeHBCutoff K js) (primeWord u)=1 := by
  obtain ⟨N0,hb⟩ := exists_actual_chart_rough_one K hK
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  intro s js hjs u hu hs hp
  exact hb N hN (chosenWidth B N) (chosenWidth_legal B N).1 (chosenWidth_legal B N).2
    s js hjs u hu hs hp

end
end ImbalancedChen.P3OriginalU789ActualAtlasLicence
