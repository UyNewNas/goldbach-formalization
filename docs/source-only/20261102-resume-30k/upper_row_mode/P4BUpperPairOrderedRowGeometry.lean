import ImbalancedChen.P5AllGroupOrderedRectangleReindex
import ImbalancedChen.P4BArbitraryWidthUpperPairOccurrence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two ACTUAL original HB groups are concatenated in their original
order. Every occurrence, including a unit and repeated role/block/value,
has its own Fin coordinate. No lower Family/source identity is used.
-/
namespace ImbalancedChen.P4BUpperPairOrderedRowGeometry
noncomputable section
open Classical
open scoped BigOperators
open P5Z.OrderedFactorTupleRectangleReindex P5Z.ActualHBPostModulusLogCutoff
open P5Z.HBRightClosedDyadicRoles P5Z.ActualRoughHeathBrownWords
open P5Z.ActualHBDyadicProductWindow
open P5Z.ActualAllRankOccurrenceFourierBridge P5Z.GroupedOccurrenceLogShift
open P5Z.ActualOccurrencePlateauWordBudget P5Z.ActualEuclideanPhysicalFourier
open P5Z.OccurrenceEuclideanMixedIntegral P5Z.LicensedOriginalIntegerProfile
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.ExactOriginalSmoothDyadicPartition
open P4BArbitraryWidthUpperPairHBNormalization P4BArbitraryWidthUpperPairOccurrence

variable {a d : ℕ}

def leftPart {α : Type*} (n : Fin (a+d) → α) : Fin a → α :=
  fun i => n (Fin.castAdd d i)

def rightPart {α : Type*} (n : Fin (a+d) → α) : Fin d → α :=
  fun i => n (Fin.natAdd a i)

@[simp] theorem leftPart_append {α : Type*} (u : Fin a → α) (v : Fin d → α) :
    leftPart (Fin.append u v) = u := by
  funext i
  exact Fin.append_left u v i

@[simp] theorem rightPart_append {α : Type*} (u : Fin a → α) (v : Fin d → α) :
    rightPart (Fin.append u v) = v := by
  funext i
  exact Fin.append_right u v i

theorem append_parts {α : Type*} (n : Fin (a+d) → α) :
    Fin.append (leftPart n) (rightPart n) = n := by
  funext i
  refine Fin.addCases (m := a) (n := d) ?_ ?_ i
  · intro j; simp [leftPart]
  · intro j; simp [rightPart]

/-- The finite bijection is on labelled coordinates, never product values. -/
theorem sum_rectangle_append (bs : Fin a → Block) (cs : Fin d → Block)
    (F : (Fin (a+d) → ℕ) → ℂ) :
    (∑ u ∈ rectangle bs, ∑ v ∈ rectangle cs, F (Fin.append u v)) =
      ∑ n ∈ rectangle (Fin.append bs cs), F n := by
  rw [← Finset.sum_product]
  apply Finset.sum_bij (fun uv _ => Fin.append uv.1 uv.2)
  · intro uv huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    apply (mem_rectangle _ _).mpr
    intro i
    refine Fin.addCases (m := a) (n := d) ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using (mem_rectangle _ _).mp hu j
    · intro j
      simpa only [Fin.append_right] using (mem_rectangle _ _).mp hv j
  · intro uv huv xy hxy heq
    apply Prod.ext
    · simpa only [leftPart_append] using congrArg leftPart heq
    · simpa only [rightPart_append] using congrArg rightPart heq
  · intro n hn
    have hu : leftPart n ∈ rectangle bs := (mem_rectangle _ _).mpr (fun i => by
      simpa only [Fin.append_left, leftPart] using
        (mem_rectangle _ _).mp hn (Fin.castAdd d i))
    have hv : rightPart n ∈ rectangle cs := (mem_rectangle _ _).mpr (fun i => by
      simpa only [Fin.append_right, rightPart] using
        (mem_rectangle _ _).mp hn (Fin.natAdd a i))
    exact ⟨(leftPart n, rightPart n), Finset.mem_product.mpr ⟨hu, hv⟩, append_parts n⟩
  · intro uv huv; rfl

def pairOwner (a d : ℕ) : Fin (a+d) → Fin 2 :=
  Fin.append (fun _ : Fin a => 0) (fun _ : Fin d => 1)

@[simp] theorem pair_group_zero (n : Fin (a+d) → ℕ) :
    integerGroupProduct (pairOwner a d) n 0 = completeProduct (leftPart n) := by
  rw [integerGroupProduct, Fin.prod_univ_add]
  simp [pairOwner, completeProduct, leftPart]

@[simp] theorem pair_group_one (n : Fin (a+d) → ℕ) :
    integerGroupProduct (pairOwner a d) n 1 = completeProduct (rightPart n) := by
  rw [integerGroupProduct, Fin.prod_univ_add]
  simp [pairOwner, completeProduct, rightPart]

theorem completeProduct_parts (n : Fin (a+d) → ℕ) :
    completeProduct n = completeProduct (leftPart n) * completeProduct (rightPart n) := by
  exact Fin.prod_univ_add n

@[simp] theorem completeProduct_append (u : Fin a → ℕ) (v : Fin d → ℕ) :
    completeProduct (Fin.append u v) = completeProduct u * completeProduct v := by
  rw [completeProduct_parts]
  simp only [leftPart_append, rightPart_append]

theorem original_word (n : Fin (a+d) → ℕ) :
    List.ofFn (integerGroupProduct (pairOwner a d) n) =
      [completeProduct (leftPart n), completeProduct (rightPart n)] := by
  simp [List.ofFn_succ]

def rowRoles (j : ℕ) : Fin (2*(j+1)) → Role :=
  fun i => (roles j)[i.val]'(by rw [roles_length]; exact i.isLt)

theorem ofFn_rowRoles (j : ℕ) : List.ofFn (rowRoles j) = roles j := by
  apply List.ext_getElem
  · simp [roles_length]
  · intro i hi hj; simp [rowRoles]

theorem roughTupleWeight_ofFn (Z y : ℝ) :
    ∀ m (rs : Fin m → Role) (n : Fin m → ℕ),
      roughTupleWeight Z y (List.ofFn rs) (List.ofFn n) =
        ∏ i, actual Z y (rs i) (n i) := by
  intro m
  induction m with
  | zero => intro rs n; simp [roughTupleWeight]
  | succ m ih =>
    intro rs n
    simpa only [List.ofFn_succ, roughTupleWeight, Fin.prod_univ_succ] using
      congrArg (fun c => actual Z y (rs 0) (n 0) * c)
        (ih (fun i => rs i.succ) (fun i => n i.succ))

/-- Each original group keeps its OWN real cube cutoff. -/
theorem pair_role_weight (Z : ℝ) (cj ck j l : ℕ)
    (u : Fin (2*(j+1)) → ℕ) (v : Fin (2*(l+1)) → ℕ) :
    roughTupleWeight Z (hbCutoff cj) (roles j) (List.ofFn u) *
      roughTupleWeight Z (hbCutoff ck) (roles l) (List.ofFn v) =
    hbSlots Z (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) (Fin.append u v) := by
  rw [← ofFn_rowRoles j, ← ofFn_rowRoles l,
    roughTupleWeight_ofFn, roughTupleWeight_ofFn, hbSlots, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The individual tensor phases have the very same positional split as
the two ordered factor tuples. Repeated numerical factors do not merge. -/
theorem occurrenceMode_append (U : Fin a → ℝ) (V : Fin d → ℝ)
    (u : Fin a → ℕ) (v : Fin d → ℕ) (xi : Fin (a+d) → ℝ) :
    occurrenceMode (Fin.append U V) (Fin.append u v) xi =
      occurrenceMode U u (leftPart xi) * occurrenceMode V v (rightPart xi) := by
  rw [occurrenceMode, Fin.prod_univ_add]
  simp only [occurrenceMode, logOccurrence, Fin.append_left, Fin.append_right,
    leftPart, rightPart]

theorem pair_mobius_cutoff (Z : ℝ) (cj ck j l : ℕ)
    (n : Fin (2*(j+1)+2*(l+1)) → ℕ)
    (hn : hbSlots Z (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) n ≠ 0)
    (i : Fin (2*(j+1)+2*(l+1)))
    (hi : Fin.append (rowRoles j) (rowRoles l) i = .mobius) :
    (n i : ℝ) ≤ Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck) i := by
  have hp : actual Z (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck) i)
      (Fin.append (rowRoles j) (rowRoles l) i) (n i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [hi] at hp
  by_contra hc
  exact hp (by simp only [actual, roughMuTrunc, if_neg hc])

def blockScales {m : ℕ} (bs : Fin m → Block) : Fin m → ℝ :=
  fun i => (lower (bs i) : ℝ)

theorem blockScales_pos {m : ℕ} (bs : Fin m → Block) (i : Fin m) :
    0 < blockScales bs i := by exact_mod_cast lower_pos (bs i)

theorem rectangle_bounds {m : ℕ} (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) (i : Fin m) :
    0 < n i ∧ blockScales bs i ≤ (n i : ℝ) ∧ (n i : ℝ) ≤ 2 * blockScales bs i := by
  have ho := (mem_rectangle _ _).mp hn i
  have h := owns_bounds ho
  exact ⟨owns_pos ho, by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Unit atoms use scale 1 and log-coordinate 0. They are retained even
though they do not satisfy the strict nonunit left-endpoint inequality. -/
theorem rectangle_plateau {m : ℕ} (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) : plateau m (logOccurrence (blockScales bs) n) = 1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro i hi
  obtain ⟨hp, hlo, hhi⟩ := rectangle_bounds bs hn i
  apply c_eq_one
  constructor
  · apply Real.log_nonneg
    exact (le_div_iff₀ (blockScales_pos bs i)).mpr hlo
  · apply Real.log_le_log (div_pos (by exact_mod_cast hp) (blockScales_pos bs i))
    exact (div_le_iff₀ (blockScales_pos bs i)).mpr hhi

def integerProfile (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ)
    (cj ck : ℕ) (n : Fin (a+d) → ℕ) : ℝ :=
  groupChart b kappa width N kappa0 (![R cj, R ck])
    (fun i => (integerGroupProduct (pairOwner a d) n i : ℝ))

def rowChart (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ)
    (cj ck : ℕ) (bs : Fin (a+d) → Block) :=
  euclideanChart b kappa width N (pairOwner a d) (blockScales bs) (![R cj, R ck]) kappa0

/-- The full actual upper normalized chart, on unit AND dyadic atoms. -/
theorem rowChart_integer (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ)
    (cj ck : ℕ) (bs : Fin (a+d) → Block) {n : Fin (a+d) → ℕ}
    (hn : n ∈ rectangle bs) :
    rowChart b kappa width N kappa0 cj ck bs
      (WithLp.toLp 2 (logOccurrence (blockScales bs) n)) =
        (integerProfile b kappa width N kappa0 cj ck n : ℂ) := by
  rw [rowChart, euclideanChart, euclideanLift_toLp, occurrenceChart_eq_groupChart,
    rectangle_plateau bs hn, mul_one]
  simp_rw [groupProduct_logOccurrence (pairOwner a d) (blockScales bs) n
    (blockScales_pos bs) (fun i => (rectangle_bounds bs hn i).1)]
  rfl

section ProfileDictionary
variable {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
variable (hgap : 2*width ≤ P4BOuterRampRoughness.baseline b kappa - nu*r)

/-- Exactly TWO original group logs; all eta/psi factors are literal. -/
theorem integerProfile_original_groups (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (n : Fin (a+d) → ℕ) :
    integerProfile b kappa width N kappa0 cj ck n =
      listExtension (normalizedLicence hb hnu hr hw hgap N)
        [completeProduct (leftPart n), completeProduct (rightPart n)] *
      P5Z.ActualEtaPsiOccurrenceBudget.eta ((completeProduct n : ℝ)/(N : ℝ)^(1-kappa0)) *
      P5Z.ActualEtaPsiOccurrenceBudget.psi ((completeProduct (leftPart n) : ℝ)/R cj) *
      P5Z.ActualEtaPsiOccurrenceBudget.psi ((completeProduct (rightPart n) : ℝ)/R ck) := by
  rw [← original_word n, listExtension_ofFn]
  simp only [integerProfile, groupChart, integerExtension, normalizedLicence,
    Fin.prod_univ_two, pair_group_zero, pair_group_one,
    ← Nat.cast_mul, ← completeProduct_parts]
  ring

/-- Totalized division retains the logs of the two ORIGINAL products,
even when one group is a unit. No individual occurrence log replaces it. -/
theorem integerProfile_raw_original_logs (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (n : Fin (a+d) → ℕ) :
    integerProfile b kappa width N kappa0 cj ck n =
      (listExtension (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hw hgap N)
        [completeProduct (leftPart n), completeProduct (rightPart n)] /
        (Real.log (completeProduct (leftPart n) : ℝ) *
          Real.log (completeProduct (rightPart n) : ℝ))) *
      P5Z.ActualEtaPsiOccurrenceBudget.eta ((completeProduct n : ℝ)/(N : ℝ)^(1-kappa0)) *
      P5Z.ActualEtaPsiOccurrenceBudget.psi ((completeProduct (leftPart n) : ℝ)/R cj) *
      P5Z.ActualEtaPsiOccurrenceBudget.psi ((completeProduct (rightPart n) : ℝ)/R ck) := by
  rw [integerProfile_original_groups hb hnu hr hw hgap,
    listExtension_normalization hb hnu hr hw hgap]
  simp only [P5ActualUpperPairHBLogTransport.wordLog, mul_one]

theorem row_dimension {j l : ℕ} (hj : j ∈ Finset.range 3) (hl : l ∈ Finset.range 3) :
    2*(j+1) + 2*(l+1) ≤ 12 := by
  have := Finset.mem_range.mp hj
  have := Finset.mem_range.mp hl
  omega

end ProfileDictionary
end
end ImbalancedChen.P4BUpperPairOrderedRowGeometry
