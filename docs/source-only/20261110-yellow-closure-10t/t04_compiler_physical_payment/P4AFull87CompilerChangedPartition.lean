import ImbalancedChen.P4AFull87CompilerCapRead

namespace ImbalancedChen.P4AFull87CompilerChangedPartition
noncomputable section
open scoped Classical BigOperators
open P4AFull87CompilerCapRead
open P4AUpperTaggedParityCompiler P4AUpperTaggedFirstPrefixDisagreement
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AHeldTaggedFiniteAdmissionPayment

/-- These are the parameters of the actual licensed policy. -/
structure Parameters where
  delta : ℝ
  n : ℕ
  e : ℚ
  q : ℕ
  om : ℝ

abbrev Parameters.keep (P : Parameters) (N : ℕ) :=
  P4AOriginalFull87LicensedSixthPolicy.policy P.delta P.n P.e P.q P.om (N : ℝ) false

abbrev Parameters.tags (P : Parameters) (N : ℕ) (h : ℕ → List Bool) :=
  tag P.delta P.n P.e P.q P.om (N : ℝ) h

abbrev Parameters.read (P : Parameters) (N r d : ℕ) :=
  atRank r (readStage P.delta P.n P.e P.q P.om (N : ℝ) d.primeFactorsList)

abbrev Parameters.caps (P : Parameters) := levels P.n P.e P.q

/-- Catalogue rank for the arithmetic union; no support estimate on
the complementary variable branches enters this rank cutoff. -/
def rankBound (P : Parameters) (omega : ℝ) : ℕ :=
  ⌈(∑ a ∈ P.caps, |a|) / omega⌉₊ + 1

private theorem revPrefix (r d : ℕ) (hr : r ≤ d.primeFactorsList.length) :
    (d.primeFactorsList.reverse.take r).reverse = rosserAncestor r d.primeFactorsList := by
  have hh : (rosserAncestor r d.primeFactorsList).reverse = d.primeFactorsList.reverse.take r := by
    simp only [rosserAncestor,List.reverse_drop]
    congr 1
    omega
  simpa only [List.reverse_reverse] using (congrArg List.reverse hh).symm

private theorem canonical_reverse {r d : ℕ} (hr : r ≤ d.primeFactorsList.length) :
    (List.ofFn (canonicalPrefix r d)).reverse = rosserAncestor r d.primeFactorsList := by
  rw [canonicalPrefix_ofFn hr, revPrefix r d hr]

private theorem admitted_rank {P : Parameters} {N cap r d : ℕ} {omega v a : ℝ}
    (hN : 2 ≤ N) (hw : 0 < omega) (ha : a ∈ P.caps)
    (hd : d ∈ universe N cap ((N : ℝ)^omega) ((N : ℝ)^v))
    (hr : r ≤ d.primeFactorsList.length)
    (hp : ordinaryRosserPrefixAdmissible false ((N : ℝ)^a)
      (rosserAncestor r d.primeFactorsList)) : r < rankBound P omega := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  have hbox := (canonical_prefix_tail_data hd hr).1
  have hprod : (N : ℝ) ^ (omega * (r : ℝ)) ≤
      ((rosserAncestor r d.primeFactorsList).prod : ℝ) := by
    rw [← canonical_reverse hr, List.prod_reverse, List.prod_ofFn, Nat.cast_prod,
      Real.rpow_mul hn0.le, Real.rpow_natCast]
    calc
      _ = ∏ _i : Fin r, (N : ℝ) ^ omega := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hn0.le _)
        (fun i _ => (mem_actualPrimeBoxTuples_iff.mp hbox i).2.2.1)
  have hpow := (Real.rpow_lt_rpow_left_iff hn).mp (hprod.trans_lt hp.1)
  have hsum := Finset.single_le_sum (s := P.caps) (f := fun t : ℝ => |t|)
    (fun t _ => abs_nonneg t) ha
  have hdiv : (r : ℝ) ≤ (∑ t ∈ P.caps, |t|) / omega := by
    apply (le_div_iff₀ hw).mpr
    linarith [le_abs_self a, mul_comm omega (r : ℝ)]
  have hrank : r ≤ ⌈(∑ t ∈ P.caps, |t|) / omega⌉₊ := by
    exact_mod_cast (hdiv.trans (Nat.le_ceil _))
  unfold rankBound
  omega

/-- An unpaid prefix consists of two actual different reads in one cell,
with all earlier decisions equal and no fixed cap selected at this rank.
The definition uses only the real tree and its chronology. -/
def inheritedFirst (P : Parameters) (N cap : ℕ) (history : ℕ → List Bool)
    (w z tau : ℝ) (d : ℕ) : Prop :=
  ∃ f ∈ cell (P.tags N history) N cap w z tau d, ∃ k < d.primeFactorsList.length,
    polarityAfter true (k+1) = false ∧ P.read N (k+1) d = none ∧
    P.keep N (rosserAncestor (k+1) d.primeFactorsList) ≠
      P.keep N (rosserAncestor (k+1) f.primeFactorsList) ∧
    ∀ i < k, decisionAt (oddFirstExitPolicy (P.keep N)) [] true d.primeFactorsList.reverse i =
      decisionAt (oddFirstExitPolicy (P.keep N)) [] true f.primeFactorsList.reverse i

abbrev catalogue (P : Parameters) (N cap : ℕ) (h : ℕ → List Bool) (omega v tau : ℝ) :=
  admissionUnionModuli (rankBound P omega) (fun _ => P.caps)
    (P.keep N) (P.tags N h) N cap omega v tau

/-- Cover every literal changed modulus. Both polarities of change and
the complete rough suffix are retained in the charged modulus. -/
theorem changed_in_catalogue_or_inherited (P : Parameters) (hdlt : 0 < P.delta)
    (N cap : ℕ) (hN : 2 ≤ N) (history : ℕ → List Bool) (omega v tau : ℝ)
    (hw : 0 < omega) {d : ℕ}
    (hd : d ∈ universe N cap ((N : ℝ)^omega) ((N : ℝ)^v))
    (hc : changed (P.keep N) (P.tags N history) N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau d) :
    d ∈ catalogue P N cap history omega v tau ∨
      inheritedFirst P N cap history ((N : ℝ)^omega) ((N : ℝ)^v) tau d := by
  obtain ⟨f,hf,htag,_,k,hk,hodd,hdiff,hbefore⟩ :=
    changed_first_actual_odd_prefix _ _ N cap _ _ tau hd hc
  let r := k+1
  have hrd : r ≤ d.primeFactorsList.length := hk
  have hrf : r ≤ f.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hf]
    exact hrd
  rw [revPrefix (k+1) d hrd,revPrefix (k+1) f hrf] at hdiff
  cases hread : P.read N r d with
  | none => exact Or.inr ⟨f,hf,k,hk,hodd,hread,hdiff,hbefore⟩
  | some a =>
    have heq := reads_eq_of_tag_eq hdlt P.n P.e P.q P.om (N : ℝ) history htag
    have hreadf : P.read N r f = some a := (congrArg (atRank r) heq).trans hread
    have ha := atRank_mem hdlt P.n P.e P.q P.om (N : ℝ) d.primeFactorsList r hread
    have hD := policy_at_read P.delta P.n P.e P.q P.om (N : ℝ) d.primeFactorsList r hrd hread
    have hF := policy_at_read P.delta P.n P.e P.q P.om (N : ℝ) f.primeFactorsList r hrf hreadf
    have hflip : ¬(ordinaryRosserPrefixAdmissible false ((N : ℝ)^a)
          (rosserAncestor r d.primeFactorsList) ↔
        ordinaryRosserPrefixAdmissible false ((N : ℝ)^a)
          (rosserAncestor r f.primeFactorsList)) := by
      intro hh
      apply hdiff
      exact hD.trans ((congrArg (fun p : Prop => decide p) (propext hh)).trans hF.symm)
    have hrank : r < rankBound P omega := by
      by_cases hA : ordinaryRosserPrefixAdmissible false ((N : ℝ)^a)
          (rosserAncestor r d.primeFactorsList)
      · exact admitted_rank (P := P) hN hw ha hd hrd hA
      · have hB : ordinaryRosserPrefixAdmissible false ((N : ℝ)^a)
            (rosserAncestor r f.primeFactorsList) := by
          by_contra hnot
          exact hflip (iff_of_false hA hnot)
        exact admitted_rank (P := P) hN hw ha (Finset.mem_filter.mp hf).1 hrf hB
    left
    apply Finset.mem_filter.mpr
    refine ⟨hd,⟨r,hrank⟩,changed_implies_crossing _ _ _ _ _ _ _ hd hc,
      hrd,a,ha,f,hf,?_⟩
    simpa only [canonical_reverse hrd,canonical_reverse hrf] using hflip

/-- Partition disjointly. Where a modulus has more than one possible
opposite word, the paid catalogue takes it once before any residual. -/
def pending (P : Parameters) (N cap : ℕ) (h : ℕ → List Bool) (omega v tau : ℝ) :=
  ((universe N cap ((N : ℝ)^omega) ((N : ℝ)^v)).filter fun d =>
    changed (P.keep N) (P.tags N h) N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau d ∧
    inheritedFirst P N cap h ((N : ℝ)^omega) ((N : ℝ)^v) tau d) \
    catalogue P N cap h omega v tau

def pendingMass (P : Parameters) (N cap : ℕ) (h : ℕ → List Bool) (omega v tau : ℝ) :=
  ∑ d ∈ pending P N cap h omega v tau, 1 / (Nat.totient d : ℝ)

theorem changedMass_le_catalogue_add_pending (P : Parameters) (hdlt : 0 < P.delta)
    (N cap : ℕ) (hN : 2 ≤ N) (h : ℕ → List Bool) (omega v tau : ℝ) (hw : 0 < omega) :
    changedMass (P.keep N) (P.tags N h) N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau ≤
    admissionUnionMass (rankBound P omega) (fun _ => P.caps) (P.keep N) (P.tags N h)
      N cap omega v tau + pendingMass P N cap h omega v tau := by
  let C := catalogue P N cap h omega v tau
  let U := pending P N cap h omega v tau
  have hdis : Disjoint C U := Finset.disjoint_left.mpr fun d hc hu =>
    (Finset.mem_sdiff.mp hu).2 hc
  change _ ≤ (∑ d ∈ C, 1 / (Nat.totient d : ℝ)) + ∑ d ∈ U, 1 / (Nat.totient d : ℝ)
  rw [← Finset.sum_union hdis]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hu,hc⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_union.mpr
    by_cases hpaid : d ∈ C
    · exact Or.inl hpaid
    · have hpend := (changed_in_catalogue_or_inherited P hdlt N cap hN h omega v tau hw hu hc).resolve_left hpaid
      exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hu,hc,hpend⟩,hpaid⟩)
  · intro d _ _
    positivity

end
end ImbalancedChen.P4AFull87CompilerChangedPartition
