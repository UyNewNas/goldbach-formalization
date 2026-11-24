import ImbalancedChen.P4AHeldTaggedFiniteAdmissionPayment

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.

A finite scalar-cap compiler, with an explicit finite historical tag.  Its
complete changed set, rather than a caller-supplied subfamily, is covered
by R09's paid ordinary-admission catalogue.  The cap values and the tag
length precede N and the fine mesh.  Arbitrary earlier historical Boolean
decisions can be retained in the tag without charging their projections.

This is a constructor and its complete arithmetic coverage proof.  It is
not an assertion that the full87 manuscript policy has already been
converted to these scalar tables.  That actual source instantiation and
its density approximation remain separate obligations.
-/

namespace ImbalancedChen.P4AFiniteCapTaggedConstructor

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedFirstPrefixDisagreement
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AHeldTaggedFiniteAdmissionPayment
open P4AHeldTaggedCompilerSupport
open P5Z.OriginalFifthPhysicalRange

/-- The unchanged physical upper ceiling. Clipping is inactive for every
table whose original scalar entries already satisfy this ceiling. -/
def boundedCap {n : ℕ} (values : Fin n → ℝ) (i : Fin n) : ℝ :=
  min (299 / 500 : ℝ) (values i)

theorem boundedCap_le {n : ℕ} (values : Fin n → ℝ) (i : Fin n) :
    boundedCap values i ≤ (299 / 500 : ℝ) := min_le_left _ _

theorem boundedCap_eq {n : ℕ} (values : Fin n → ℝ) (i : Fin n)
    (hi : values i ≤ (299 / 500 : ℝ)) : boundedCap values i = values i :=
  min_eq_right hi

def capAlphabet {n : ℕ} (values : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image (boundedCap values)

theorem boundedCap_mem {n : ℕ} (values : Fin n → ℝ) (i : Fin n) :
    boundedCap values i ∈ capAlphabet values :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The gate includes, for example, the original first-stop condition.
The selector and gate are evaluated on the prefix actually being tested. -/
def keep {n : ℕ} (values : Fin n → ℝ) (select : List ℕ → Fin n)
    (gate : List ℕ → Bool) (N : ℕ) (pre : List ℕ) : Bool :=
  gate pre && decide (ordinaryRosserPrefixAdmissible false
    ((N : ℝ) ^ boundedCap values (select pre)) pre)

def prefix (r d : ℕ) : List ℕ := (d.primeFactorsList.reverse.take r).reverse

/-- Every supplied historical decision is recorded at its own prefix.
The tag does not remove the projection of any child boundary. -/
abbrev HistoryState (h n : ℕ) := (Fin h → Bool) × Bool × Fin n

def state {h n : ℕ} (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool) (pre : List ℕ) : HistoryState h n :=
  (fun j => history j pre, gate pre, select pre)

abbrev TagKey (J h n : ℕ) := Fin J × HistoryState h n

/-- One-hot encoding is used only to fit the existing List Bool tag API.
No numerical enumeration, proof guard or fine-atom count is involved. -/
def tag {h n : ℕ} (J : ℕ) (select : List ℕ → Fin n)
    (gate : List ℕ → Bool) (history : Fin h → List ℕ → Bool) (d : ℕ) : List Bool :=
  List.ofFn fun j : Fin (Fintype.card (TagKey J h n)) =>
    let q := (Fintype.equivFin (TagKey J h n)).symm j
    decide (state select gate history (prefix q.1.val d) = q.2)

theorem tag_length {h n : ℕ} (J : ℕ) (select : List ℕ → Fin n)
    (gate : List ℕ → Bool) (history : Fin h → List ℕ → Bool) (d : ℕ) :
    (tag J select gate history d).length = Fintype.card (TagKey J h n) := by
  simp only [tag, List.length_ofFn]

theorem same_tag_state {h n : ℕ} (J : ℕ) (select : List ℕ → Fin n)
    (gate : List ℕ → Bool) (history : Fin h → List ℕ → Bool)
    {d e : ℕ} (ht : tag J select gate history e = tag J select gate history d)
    (r : Fin J) :
    state select gate history (prefix r.val e) =
      state select gate history (prefix r.val d) := by
  unfold tag at ht
  have hf := List.ofFn_injective ht
  let q : TagKey J h n := (r, state select gate history (prefix r.val d))
  have heq := congrFun hf ((Fintype.equivFin (TagKey J h n)) q)
  have hb : decide (state select gate history (prefix r.val e) =
      state select gate history (prefix r.val d)) = true := by
    simpa only [Equiv.symm_apply_apply, q, decide_true] using heq
  exact of_decide_eq_true hb

theorem same_tag_history {h n : ℕ} (J : ℕ) (select : List ℕ → Fin n)
    (gate : List ℕ → Bool) (history : Fin h → List ℕ → Bool)
    {d e : ℕ} (ht : tag J select gate history e = tag J select gate history d)
    (r : Fin J) (j : Fin h) :
    history j (prefix r.val e) = history j (prefix r.val d) := by
  exact congrFun (congrArg Prod.fst (same_tag_state J select gate history ht r)) j

theorem keep_implies_root {n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (N : ℕ) (hN : 1 ≤ (N : ℝ)) (positive : Bool) (pre : List ℕ)
    (hp : oddFirstExitPolicy (keep values select gate N) positive pre = true) :
    ordinaryParityRosserPolicy false ((N : ℝ) ^ (299 / 500 : ℝ)) positive pre = true := by
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
      have hk : keep values select gate N pre = true := by
        simpa only [oddFirstExitPolicy, Bool.false_or] using hp
      have ha : ordinaryRosserPrefixAdmissible false
          ((N : ℝ) ^ boundedCap values (select pre)) pre :=
        of_decide_eq_true (Bool.and_eq_true.mp hk).2
      have hb := ordinaryRosserPrefixAdmissible_mono false pre
        (Real.rpow_le_rpow_of_exponent_le hN (boundedCap_le values (select pre))) ha
      simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
        oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using hb

/-- Raw support is derived from the literal ordinary tests of this
constructor. There is no assumed support field. -/
theorem raw_support_lt {n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (N cap : ℕ) (hN : 2 ≤ N) (w z : ℝ) {d : ℕ}
    (hd : d ∈ rawSupport (keep values select gate N) N cap w z) :
    (d : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  let P := oddFirstExitPolicy (keep values select gate N)
  let R := (N : ℝ) ^ (299 / 500 : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := Real.one_lt_rpow hNr (by norm_num)
  change d ∈ fixedRoughSupport (keep values select gate N) N cap w z at hd
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    P (oddFirstExitPolicy_even _) N cap w z] at hd
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection P _ d).mp hd
  have hv := validSelection_mono P (ordinaryParityRosserPolicy false R)
    (keep_implies_root values select gate N hNr.le) [] chosen true hvalid
  have hroot : d ∈ firstExitRetainedModuli (ordinaryParityRosserPolicy false R)
      (roughPrimeUniverse N cap w z) :=
    (mem_firstExitRetainedModuli_iff_validSelection _ _ d).mpr ⟨chosen, hsub, hv, hprod⟩
  rw [ordinaryParityRosserRetainedModuli_eq false R hR _
    (roughPrimeUniverse_pairwise_gt N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hroot
  exact ((mem_ordinaryRosserRetainedModuli_iff false R hR _
    (roughPrimeUniverse_pairwise_gt N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) d).mp hroot).2.1

theorem raw_rank_lt {n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (z : ℝ)
    {d : ℕ} (hd : d ∈ rawSupport (keep values select gate N)
      N cap ((N : ℝ) ^ omega) z) : d.primeFactorsList.length < J0 omega := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  have hlo := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (keep values select gate N) N cap (Real.rpow_nonneg hn0.le omega) z hd
  have hhi := raw_support_lt values select gate N cap hN ((N : ℝ) ^ omega) z hd
  have hp : (N : ℝ) ^ (omega * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (299 / 500 : ℝ) := by
    rw [Real.rpow_mul hn0.le, Real.rpow_natCast]
    exact hlo.trans hhi.le
  have hc := (Real.rpow_le_rpow_left_iff hn).mp hp
  have hsf := fixedRoughSupport_squarefree (keep values select gate N)
    N cap ((N : ℝ) ^ omega) z hd
  have hl : d.primeFactorsList.length = d.primeFactors.card := by
    change d.primeFactorsList.length = d.primeFactorsList.toFinset.card
    exact (List.toFinset_card_of_nodup hsf.nodup_primeFactorsList).symm
  have hdiv : (d.primeFactors.card : ℝ) ≤ (599 / 1000 : ℝ) / omega := by
    apply (le_div_iff₀ homega).mpr
    nlinarith
  have hlt : (d.primeFactors.card : ℝ) < (J0 omega : ℝ) := by
    linarith [J0_spec omega]
  rw [hl]
  exact_mod_cast hlt

theorem crossing_rank_lt {h n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (z tau : ℝ)
    {d : ℕ} (hc : crossing (keep values select gate N)
      (tag (J0 omega) select gate history) N cap ((N : ℝ) ^ omega) z tau d) :
    d.primeFactorsList.length < J0 omega := by
  obtain ⟨e, he⟩ := hc.1
  obtain ⟨hecell, heraw⟩ := Finset.mem_inter.mp he
  rw [← cell_rank_preserved _ _ _ _ _ _ hecell]
  exact raw_rank_lt values select gate omega homega N cap hN z heraw

/-- The entire changed set is paid by the original total/cube admission
catalogue. Same-tag gates and chosen cap indices agree exactly, so neither
owner walls nor historical equality/inherit projections are discarded. -/
theorem changed_mem_admissionUnion {h n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool)
    (omega v : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (tau : ℝ)
    {d : ℕ} (hd : d ∈ universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hc : changed (keep values select gate N) (tag (J0 omega) select gate history)
      N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d) :
    d ∈ admissionUnionModuli (J0 omega) (fun _ => capAlphabet values)
      (keep values select gate N) (tag (J0 omega) select gate history)
      N cap omega v tau := by
  have hcross := changed_implies_crossing _ _ N cap _ _ tau hd hc
  have hrank := crossing_rank_lt values select gate history omega homega
    N cap hN ((N : ℝ) ^ v) tau hcross
  obtain ⟨e, hecell, htag, _hlabels, k, hk, _hodd, hdiff, _hbefore⟩ :=
    changed_first_actual_odd_prefix (keep values select gate N)
      (tag (J0 omega) select gate history) N cap _ _ tau hd hc
  let r : Fin (J0 omega) := ⟨k + 1, by omega⟩
  have hr : k + 1 ≤ d.primeFactorsList.length := by omega
  have hre : k + 1 ≤ e.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hecell]
    exact hr
  have hs := same_tag_state (J0 omega) select gate history htag r
  have hgate : gate (prefix (k + 1) e) = gate (prefix (k + 1) d) :=
    congrArg (fun s : HistoryState h n => s.2.1) hs
  have hselect : select (prefix (k + 1) e) = select (prefix (k + 1) d) :=
    congrArg (fun s : HistoryState h n => s.2.2) hs
  have hadm : ¬(ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ boundedCap values (select (prefix (k + 1) d))) (prefix (k + 1) d) ↔
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ boundedCap values (select (prefix (k + 1) d))) (prefix (k + 1) e)) := by
    intro hh
    apply hdiff
    change gate (prefix (k + 1) d) && decide _ = gate (prefix (k + 1) e) && decide _
    rw [hgate, hselect, propext hh]
  apply Finset.mem_filter.mpr
  refine ⟨hd, r, hcross, hr, boundedCap values (select (prefix (k + 1) d)),
    boundedCap_mem values _, e, hecell, ?_⟩
  simpa only [r, canonicalPrefix_ofFn hr, canonicalPrefix_ofFn hre, prefix] using hadm

theorem changedMass_le_admissionUnion {h n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool)
    (omega v : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (tau : ℝ) :
    changedMass (keep values select gate N) (tag (J0 omega) select gate history)
      N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau ≤
    admissionUnionMass (J0 omega) (fun _ => capAlphabet values)
      (keep values select gate N) (tag (J0 omega) select gate history)
      N cap omega v tau := by
  unfold changedMass admissionUnionMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdU, hc⟩ := Finset.mem_filter.mp hd
    exact changed_mem_admissionUnion values select gate history omega v homega
      N cap hN tau hdU hc
  · intro d _ _
    positivity

end
end ImbalancedChen.P4AFiniteCapTaggedConstructor
