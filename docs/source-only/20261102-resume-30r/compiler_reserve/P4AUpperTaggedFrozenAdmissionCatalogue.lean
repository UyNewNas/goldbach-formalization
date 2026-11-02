import ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement
import ImbalancedChen.P5PresievedRoughGateMeshReserve

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The actual O fine labels control the charged modulus's OWN canonical
prefix. A disagreement of the literal original upper admission at a
common frozen cap is covered by the total product and all original
odd-cardinality cube rows. The fixed finite cap alphabet yields a fixed
proper wall catalogue. Constant rows are removed by exact finite subtype;
no equality/inherit region is erased.

The final payment is for every actual mixed point whose opposite prefix
admissions use one common cap in that alphabet, with one tau before N.
Membership in this arithmetic subfamily is a definition, not an input
smallness or wall-cover hypothesis. Binding ALL decisions of the complete
R08 policy to this subfamily remains a separate unproved obligation.
-/

namespace ImbalancedChen.P4AUpperTaggedFrozenAdmissionCatalogue

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P2CanonicalWallFullResidualPayment
open P5Z.PresievedRoughSlotAffineGates
open P5Z.PresievedRoughGateMeshReserve

/-- Public conversion for the canonical prefix used by the existing
arithmetic wall supplier; its private prefix_ofFn cannot be imported. -/
theorem canonicalPrefix_ofFn {r d : ℕ} (hr : r ≤ d.primeFactorsList.length) :
    List.ofFn (canonicalPrefix r d) = d.primeFactorsList.reverse.take r := by
  unfold canonicalPrefix
  have hlen : (d.primeFactorsList.reverse.take r).reverse.length = r := by
    simp only [List.length_reverse, List.length_take, Nat.min_eq_left hr]
  simpa only [List.reverse_reverse] using primeHistoryTuple_ofFn hlen

theorem canonicalPrefix_strictAnti {N cap r d : ℕ} {omega v : ℝ}
    (hd : d ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hr : r ≤ d.primeFactorsList.length) : StrictAnti (canonicalPrefix r d) := by
  obtain ⟨hsub, _⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) hd
  have hp := (roughPrimeUniverse_pairwise_gt N cap ((N : ℝ) ^ omega)
    ((N : ℝ) ^ v)).sublist ((List.take_sublist r _).trans hsub)
  rw [← canonicalPrefix_ofFn hr] at hp
  exact List.pairwise_ofFn.mp hp

theorem canonicalPrefix_pos {N cap r d : ℕ} {omega v : ℝ}
    (hd : d ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hr : r ≤ d.primeFactorsList.length) : ∀ i, 0 < canonicalPrefix r d i := by
  have hp := (canonical_prefix_tail_data hd hr).1
  exact fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos

/-- Whole-word label equality gives the exact label of every canonical
prefix slot, without a representative choice or a new mesh. -/
theorem cell_canonicalPrefix_label_eq
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {r d e : ℕ} (he : e ∈ P4AUpperTaggedParityCompiler.cell tag N cap w z tau d)
    (hrd : r ≤ d.primeFactorsList.length) (i : Fin r) :
    primeLabel N tau (canonicalPrefix r d i) =
      primeLabel N tau (canonicalPrefix r e i) := by
  have hre : r ≤ e.primeFactorsList.length := by
    rw [cell_rank_preserved tag N cap w z tau he]
    exact hrd
  have hlabels := (cell_prime_labels tag N cap w z tau he).symm
  have htake :
      (d.primeFactorsList.reverse.take r).map (primeLabel N tau) =
        (e.primeFactorsList.reverse.take r).map (primeLabel N tau) := by
    simpa only [primeWordLabel, P2LowerFiniteCellRounding.label, List.map_take] using
      congrArg (List.take r) hlabels
  have hfun : (fun j : Fin r => primeLabel N tau (canonicalPrefix r d j)) =
      (fun j : Fin r => primeLabel N tau (canonicalPrefix r e j)) := by
    apply List.ofFn_injective
    change List.ofFn ((primeLabel N tau) ∘ canonicalPrefix r d) =
      List.ofFn ((primeLabel N tau) ∘ canonicalPrefix r e)
    rw [← List.map_ofFn, ← List.map_ofFn, canonicalPrefix_ofFn hrd,
      canonicalPrefix_ofFn hre]
    exact htake
  exact congrFun hfun i

theorem cell_canonicalPrefix_norm_sub_le
    (tag : ℕ → List Bool) (N cap : ℕ) (w z : ℝ) {tau : ℝ} (htau : 0 < tau)
    {r d e : ℕ} (he : e ∈ P4AUpperTaggedParityCompiler.cell tag N cap w z tau d)
    (hrd : r ≤ d.primeFactorsList.length) :
    ‖actualPrimeTupleLog N (canonicalPrefix r d) -
      actualPrimeTupleLog N (canonicalPrefix r e)‖ ≤ tau := by
  apply (pi_norm_le_iff_of_nonneg htau.le).mpr
  intro i
  have hi := same_primeLabel_coordinate_distance_lt N htau
    (cell_canonicalPrefix_label_eq tag N cap w z tau he hrd i)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, actualPrimeTupleLog] using hi.le

/-- Truth disagreement derives properness. In particular zero affine
rows, whether true or false, have no wall and cannot be charged. -/
theorem strict_row_disagreement_proper_wall {r : ℕ}
    (L : (Fin r → ℝ) →L[ℝ] ℝ) (c tau : ℝ) (x y : Fin r → ℝ)
    (hclose : ‖x - y‖ ≤ tau) (hdiff : ¬(L x < c ↔ L y < c)) :
    L ≠ 0 ∧ |L x - c| ≤ ‖L‖ * tau := by
  have hproper : L ≠ 0 := by
    intro hz
    exact hdiff (by simp only [hz, ContinuousLinearMap.zero_apply])
  have hosc := L.le_opNorm (x - y)
  rw [map_sub, Real.norm_eq_abs] at hosc
  have hos := hosc.trans (mul_le_mul_of_nonneg_left hclose (norm_nonneg L))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hos
  refine ⟨hproper, abs_le.mpr ?_⟩
  by_cases hx : L x < c
  · have hy : c ≤ L y := le_of_not_gt (fun hy => hdiff (iff_of_true hx hy))
    constructor <;> linarith
  · have hy : L y < c := by
      by_contra hy
      exact hdiff (iff_of_false hx hy)
    have hx' := le_of_not_gt hx
    constructor <;> linarith

/-- Literal original upper admission flip, on the very prefixes of the
two O-cell moduli, meets one proper row at d. All total/cubic tests and
strict endpoint conventions are inherited from the original dictionary. -/
theorem cell_original_admission_disagreement_wall
    (tag : ℕ → List Bool) {N : ℕ} (hN : 1 < N) (cap : ℕ)
    (omega v ell : ℝ) {tau : ℝ} (htau : 0 < tau) {r d e : ℕ}
    (hd : d ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (he : e ∈ P4AUpperTaggedParityCompiler.cell tag N cap
      ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d)
    (hrd : r ≤ d.primeFactorsList.length)
    (hdiff : ¬(ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell)
        (List.ofFn (canonicalPrefix r d)).reverse ↔
      ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell)
        (List.ofFn (canonicalPrefix r e)).reverse)) :
    ∃ g : GateSlot r, row g ≠ 0 ∧
      |row g (actualPrimeTupleLog N (canonicalPrefix r d)) - offset ell g| ≤
        ‖row g‖ * tau := by
  have heU := (Finset.mem_filter.mp he).1
  have hre : r ≤ e.primeFactorsList.length := by
    rw [cell_rank_preserved tag N cap _ _ tau he]
    exact hrd
  have hpD := canonicalPrefix_pos hd hrd
  have hpE := canonicalPrefix_pos heU hre
  have hsD := canonicalPrefix_strictAnti hd hrd
  have hsE := canonicalPrefix_strictAnti heU hre
  have hlogD := (actualPrimeTupleLog_strictAnti_iff hN _ hpD).mpr hsD
  have hlogE := (actualPrimeTupleLog_strictAnti_iff hN _ hpE).mpr hsE
  rw [original_upper_prefix_iff_log hN ell _ hpD hsD,
    original_upper_prefix_iff_log hN ell _ hpE hsE] at hdiff
  have hrough : ¬(actualPrimeTupleLog N (canonicalPrefix r d) ∈ roughRegion r ell ↔
      actualPrimeTupleLog N (canonicalPrefix r e) ∈ roughRegion r ell) := by
    simpa only [roughRegion_dictionary, hlogD, hlogE, and_true] using hdiff
  have hgate : ∃ g : GateSlot r,
      ¬(row g (actualPrimeTupleLog N (canonicalPrefix r d)) < offset ell g ↔
        row g (actualPrimeTupleLog N (canonicalPrefix r e)) < offset ell g) := by
    by_contra hn
    apply hrough
    have hall : ∀ g : GateSlot r,
        row g (actualPrimeTupleLog N (canonicalPrefix r d)) < offset ell g ↔
          row g (actualPrimeTupleLog N (canonicalPrefix r e)) < offset ell g := by
      intro g
      by_contra hg
      exact hn ⟨g, hg⟩
    exact ⟨fun h g => (hall g).mp (h g), fun h g => (hall g).mpr (h g)⟩
  obtain ⟨g, hg⟩ := hgate
  exact ⟨g, strict_row_disagreement_proper_wall (row g) (offset ell g) tau _ _
    (cell_canonicalPrefix_norm_sub_le tag N cap _ _ htau he hrd) hg⟩

abbrev ProperGate (r : ℕ) := {g : GateSlot r // row g ≠ 0}
abbrev CatalogueIndex (levels : Finset ℝ) (r : ℕ) :=
  {ell : ℝ // ell ∈ levels} × ProperGate r

def catalogueForms (levels : Finset ℝ) (r : ℕ) :
    Fin (Fintype.card (CatalogueIndex levels r)) → (Fin r → ℝ) →L[ℝ] ℝ :=
  fun j => row ((Fintype.equivFin (CatalogueIndex levels r)).symm j).2.val

def catalogueBounds (levels : Finset ℝ) (r : ℕ) :
    Fin (Fintype.card (CatalogueIndex levels r)) → ℝ :=
  fun j => let q := (Fintype.equivFin (CatalogueIndex levels r)).symm j
    offset q.1.val q.2.val

theorem catalogueForms_ne_zero (levels : Finset ℝ) (r : ℕ)
    (j : Fin (Fintype.card (CatalogueIndex levels r))) : catalogueForms levels r j ≠ 0 :=
  ((Fintype.equivFin (CatalogueIndex levels r)).symm j).2.property

/-- Fixed catalogue constant: it depends on the rank, never the fine
atom count. Cap values affect only offsets, not this oscillation bound. -/
def rowConstant (r : ℕ) : ℝ := 1 + ∑ g : GateSlot r, ‖row g‖

theorem rowConstant_pos (r : ℕ) : 0 < rowConstant r := by
  have hs : 0 ≤ ∑ g : GateSlot r, ‖row g‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  unfold rowConstant
  linarith

theorem norm_row_le_rowConstant {r : ℕ} (g : GateSlot r) : ‖row g‖ ≤ rowConstant r := by
  have hg := Finset.single_le_sum (f := fun g : GateSlot r => ‖row g‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ g)
  unfold rowConstant
  linarith

/-- The actually charged mixed-point subfamily with a common frozen cap
in the specified finite alphabet. This definition does not assert that
the entire full87/held policy lies in this subfamily. -/
def frozenAdmissionMixed (levels : Finset ℝ) (r : ℕ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) (d : ℕ) : Prop :=
  crossing keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d ∧
  r ≤ d.primeFactorsList.length ∧
  ∃ ell ∈ levels, ∃ e ∈ P4AUpperTaggedParityCompiler.cell tag N cap
      ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d,
    ¬(ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell)
        (List.ofFn (canonicalPrefix r d)).reverse ↔
      ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell)
        (List.ofFn (canonicalPrefix r e)).reverse)

def frozenAdmissionMixedMass (levels : Finset ℝ) (r : ℕ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)).filter
    (frozenAdmissionMixed levels r keep tag N cap omega v tau),
    1 / (Nat.totient d : ℝ)

/-- Constructive complete cover of this explicitly defined actual
subfamily. There is no caller-supplied wall-cover proposition. -/
theorem frozenAdmissionMixed_in_fixed_catalogue
    (levels : Finset ℝ) (r : ℕ) (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    {N : ℕ} (hN : 1 < N) (cap : ℕ) (omega v : ℝ)
    {tau delta : ℝ} (htau : 0 < tau) (hwidth : rowConstant r * tau ≤ delta)
    {d : ℕ} (hd : d ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hm : frozenAdmissionMixed levels r keep tag N cap omega v tau d) :
    d ∈ canonicalWallModuli N cap omega v (catalogueForms levels r)
      (catalogueBounds levels r) delta := by
  obtain ⟨_hc, hr, ell, hell, e, he, hdiff⟩ := hm
  obtain ⟨g, hg, hwall⟩ := cell_original_admission_disagreement_wall
    tag hN cap omega v ell htau hd he hr hdiff
  let q : CatalogueIndex levels r := (⟨ell, hell⟩, ⟨g, hg⟩)
  let j := (Fintype.equivFin (CatalogueIndex levels r)) q
  apply Finset.mem_filter.mpr
  refine ⟨hd, hr, j, ?_⟩
  change |catalogueForms levels r j (actualPrimeTupleLog N (canonicalPrefix r d)) -
    catalogueBounds levels r j| ≤ delta
  have hb := hwall.trans
    ((mul_le_mul_of_nonneg_right (norm_row_le_rowConstant g) htau.le).trans hwidth)
  simpa only [catalogueForms, catalogueBounds, j, Equiv.symm_apply_apply, q] using hb

/-- Literal reciprocal-totient payment for all actual mixed points of
the finite-alphabet admission subfamily, after ALL residual moduli.
The positive fine width and fixed catalogue precede the common N cutoff.
No global compiler reserve is claimed without the remaining policy map. -/
theorem exists_frozenAdmissionMixedMass_lt
    (levels : Finset ℝ) (r : ℕ) (omega v : ℝ)
    (homega : 0 < omega) (hov : omega < v) (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        0 < tau → tau ≤ tau0 →
        frozenAdmissionMixedMass levels r keep tag N cap omega v tau < eta := by
  obtain ⟨delta, hdelta, N0, hN0, hpay⟩ :=
    P4AUpperTaggedMixedWallPayment.exists_uniform_mixedWallMass_lt
      omega v homega hov (catalogueForms levels r) (catalogueBounds levels r)
      (catalogueForms_ne_zero levels r) eta heta
  have hC := rowConstant_pos r
  refine ⟨delta / rowConstant r, div_pos hdelta hC, N0, hN0, ?_⟩
  intro N hN hEven cap keep tag tau htau htau0
  have hN' : 1 < N := by omega
  have hwidth : rowConstant r * tau ≤ delta := by
    have hh := (le_div_iff₀ hC).mp htau0
    simpa only [mul_comm] using hh
  apply lt_of_le_of_lt ?_ (hpay N hN hEven cap keep tag tau)
  unfold frozenAdmissionMixedMass P4AUpperTaggedMixedWallPayment.mixedWallMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdU, hm⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr
      ⟨frozenAdmissionMixed_in_fixed_catalogue levels r keep tag hN' cap
        omega v htau hwidth hdU hm, hm.1⟩
  · intro d _ _
    positivity

end
end ImbalancedChen.P4AUpperTaggedFrozenAdmissionCatalogue
