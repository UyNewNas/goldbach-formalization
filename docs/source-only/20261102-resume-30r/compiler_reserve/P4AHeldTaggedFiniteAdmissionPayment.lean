import ImbalancedChen.P4AUpperTaggedFrozenAdmissionCatalogue
import ImbalancedChen.P4AHeldTaggedCompilerSupport

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

R08 supplies the rank bound for the SAME O held compiledRho. R09 consumes
that actual theorem, not a rank field. The first result therefore confines
every actual changed coefficient to finitely many possible first decisions.

The remaining results pay the entire union of all finite-alphabet ordinary
admission subfamilies, at all those ranks, on one pre-N fine mesh. Actual
beta slopes are reused, and occupied products equal the same global rho.
No complete held/full87 decision-to-alphabet map has been supplied. Hence
the union is NOT asserted to contain every changed coefficient, and this
file does NOT assert the full compiler reserve or a final density endpoint.
-/

namespace ImbalancedChen.P4AHeldTaggedFiniteAdmissionPayment

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedFirstPrefixDisagreement
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AHeldTaggedCompilerSupport

/-- The actual R08 support theorem makes the complete O first-disagreement
catalogue finite. No support or rank hypothesis is accepted here. -/
theorem held_changed_bounded_first_prefix
    (data : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ data.e)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N)
    (z tau : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap ((N : ℝ) ^ omega) z)
    (hc : changed (P4ACommonPolicyTaggedCompiler.heldRetain data N)
      (P4ACommonPolicyTaggedCompiler.historicalTag data N)
      N cap ((N : ℝ) ^ omega) z tau d) :
    ∃ e ∈ cell (P4ACommonPolicyTaggedCompiler.historicalTag data N)
        N cap ((N : ℝ) ^ omega) z tau d,
      P4ACommonPolicyTaggedCompiler.historicalTag data N e =
        P4ACommonPolicyTaggedCompiler.historicalTag data N d ∧
      primeWordLabel N tau e = primeWordLabel N tau d ∧
      ∃ k : ℕ, k + 1 < J0 omega ∧ k < d.primeFactorsList.length ∧
        polarityAfter true (k + 1) = false ∧
        P4ACommonPolicyTaggedCompiler.heldRetain data N
            ((d.primeFactorsList.reverse.take (k + 1)).reverse) ≠
          P4ACommonPolicyTaggedCompiler.heldRetain data N
            ((e.primeFactorsList.reverse.take (k + 1)).reverse) ∧
        ∀ i : ℕ, i < k →
          decisionAt (oddFirstExitPolicy (P4ACommonPolicyTaggedCompiler.heldRetain data N))
              [] true d.primeFactorsList.reverse i =
            decisionAt (oddFirstExitPolicy (P4ACommonPolicyTaggedCompiler.heldRetain data N))
              [] true e.primeFactorsList.reverse i := by
  have hrank := held_crossing_rank_lt_J0 data he omega homega N cap hN z tau
    (changed_implies_crossing _ _ N cap _ z tau hd hc)
  obtain ⟨e, hecell, htag, hlabels, k, hk, hodd, hdiff, hbefore⟩ :=
    held_changed_first_actual_odd_prefix data N cap ((N : ℝ) ^ omega) z tau hd hc
  exact ⟨e, hecell, htag, hlabels, k, by omega, hk, hodd, hdiff, hbefore⟩

def admissionUnionModuli (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) : Finset ℕ :=
  (universe N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)).filter fun d =>
    ∃ r : Fin ranks, frozenAdmissionMixed (levels r) r.val keep tag N cap omega v tau d

def admissionUnionMass (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) : ℝ :=
  ∑ d ∈ admissionUnionModuli ranks levels keep tag N cap omega v tau,
    1 / (Nat.totient d : ℝ)

/-- Moduli, rather than fine cells, are summed. Multiple possible prefix
witnesses safely overcount; the actual union has no hidden multiplicity. -/
theorem admissionUnionMass_le_sum (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) :
    admissionUnionMass ranks levels keep tag N cap omega v tau ≤
      ∑ r : Fin ranks, frozenAdmissionMixedMass (levels r) r.val
        keep tag N cap omega v tau := by
  unfold admissionUnionMass admissionUnionModuli frozenAdmissionMixedMass
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d hd
  by_cases h : ∃ r : Fin ranks,
      frozenAdmissionMixed (levels r) r.val keep tag N cap omega v tau d
  · obtain ⟨r, hr⟩ := h
    rw [if_pos ⟨r, hr⟩]
    have hh := Finset.single_le_sum
      (f := fun j : Fin ranks => if frozenAdmissionMixed (levels j) j.val
        keep tag N cap omega v tau d then 1 / (Nat.totient d : ℝ) else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ r)
    simpa only [if_pos hr] using hh
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun r _ => by split_ifs <;> positivity)

/-- Simultaneously pays all fixed prefix ranks and all fixed cap values.
The choices precede N and are uniform in every later actual keep/tag and
in all smaller positive fine widths. No fine-atom count appears. -/
theorem exists_admissionUnionMass_lt
    (ranks : ℕ) (hranks : 0 < ranks) (levels : Fin ranks → Finset ℝ)
    (omega v : ℝ) (homega : 0 < omega) (hov : omega < v)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        0 < tau → tau ≤ tau0 →
        admissionUnionMass ranks levels keep tag N cap omega v tau < eta := by
  let eps : ℝ := eta / ((ranks : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have hsupply := fun r : Fin ranks => exists_frozenAdmissionMixedMass_lt
    (levels r) r.val omega v homega hov eps heps
  choose widths hwidths thresholds hthresholds hpay using hsupply
  have hne : (Finset.univ : Finset (Fin ranks)).Nonempty :=
    ⟨⟨0, hranks⟩, Finset.mem_univ _⟩
  let tau0 : ℝ := Finset.univ.inf' hne widths
  have htau0 : 0 < tau0 := by
    apply (Finset.lt_inf'_iff _).mpr
    exact fun r _ => hwidths r
  let N0 : ℕ := max 2 (Finset.univ.sup thresholds)
  refine ⟨tau0, htau0, N0, le_max_left _ _, ?_⟩
  intro N hN hEven cap keep tag tau htau hsmall
  have hlocal (r : Fin ranks) :
      frozenAdmissionMixedMass (levels r) r.val keep tag N cap omega v tau ≤ eps := by
    have hNr : thresholds r ≤ N :=
      (Finset.le_sup (f := thresholds) (Finset.mem_univ r)).trans
        ((le_max_right _ _).trans hN)
    have ht : tau ≤ widths r := hsmall.trans
      (Finset.inf'_le widths (Finset.mem_univ r))
    exact (hpay r N hNr hEven cap keep tag tau htau ht).le
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin ranks))) => hlocal r)
  have htotal : ∑ r : Fin ranks, eps = (ranks : ℝ) * eps := by simp
  rw [htotal] at hsum
  have heq : eps * ((ranks : ℝ) + 1) = eta :=
    div_mul_cancel₀ _ (by positivity : (ranks : ℝ) + 1 ≠ 0)
  exact (admissionUnionMass_le_sum ranks levels keep tag N cap omega v tau).trans_lt
    (hsum.trans_lt (by nlinarith))

def admissionUnionDensity (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau level : ℝ) (c : ℕ → ℝ) : ℝ :=
  let rough := admissionUnionModuli ranks levels keep tag N cap omega v tau
  let small := actualSmallRosserSupport N cap ((N : ℝ) ^ omega)
  physicalDensitySum (smallRoughModuli small rough)
    (smallRoughRho small rough c
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level))

/-- Every occupied product in the paid subfamily is the SAME global O
rho entry. Sign attachment is read from its actual compiled coefficient. -/
theorem admissionUnion_rho_eq_global_rho
    (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau level : ℝ) {q : ℕ}
    (hq : q ∈ smallRoughModuli (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (admissionUnionModuli ranks levels keep tag N cap omega v tau)) :
    smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (admissionUnionModuli ranks levels keep tag N cap omega v tau)
      (coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau)
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level) q =
      P4AUpperTaggedBetaAttachment.rho keep tag N cap ((N : ℝ) ^ omega)
        ((N : ℝ) ^ v) tau level q := by
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  rw [smallRoughRho_mul
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hm)
    (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap _ _
      (Finset.mem_filter.mp hm).1) _ _ _ ha hd,
    P4AUpperTaggedBetaAttachment.rho_at_product keep tag N cap _ _ tau level
      ha (Finset.mem_filter.mp hd).1]

/-- Literal coefficient norm on the actual paid subfamily. The one-unit
upper parity discrepancy is reused; no coefficient-error premise occurs. -/
theorem coefficient_error_on_admissionUnion_le_mass
    (ranks : ℕ) (levels : Fin ranks → Finset ℝ)
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ) :
    reciprocalTotientDensity (admissionUnionModuli ranks levels keep tag N cap omega v tau)
      (fun d => |coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d -
        raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) d|) ≤
      admissionUnionMass ranks levels keep tag N cap omega v tau := by
  unfold reciprocalTotientDensity admissionUnionMass
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_coefficient_sub_raw keep tag N cap _ _ tau (Finset.mem_filter.mp hd).1]
  split_ifs <;> simp only [zero_div, le_refl] <;> positivity

/-- Same-rho physical payment of the complete finite-rank admission
subfamily, including both beta signs and the exact B/(nu*epsilon^2)
conversion. The beta precision is already fixed; this chooses only tau
and N. This is not a total compiler-reserve theorem. -/
theorem exists_same_rho_admissionUnion_payment
    (ranks : ℕ) (hranks : 0 < ranks) (levels : Fin ranks → Finset ℝ)
    (nu epsilon v : ℝ) (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    (hv : nu * epsilon ^ 2 < v) (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        0 < tau → tau ≤ tau0 →
        let omega := nu * epsilon ^ 2
        let level := (N : ℝ) ^ (nu * epsilon)
        |admissionUnionDensity ranks levels keep tag N cap omega v tau level
            (coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) -
          admissionUnionDensity ranks levels keep tag N cap omega v tau level
            (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))| <
          eta * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  obtain ⟨Nd, hNd, hdensity⟩ := hsupply nu hnu epsilon he he8
  have homega : 0 < nu * epsilon ^ 2 := mul_pos hnu (sq_pos_of_pos he)
  let M : ℝ := B / (nu * epsilon ^ 2)
  have hM : 0 < M := div_pos hB homega
  obtain ⟨tau0, htau0, Nm, hNm, hmass⟩ := exists_admissionUnionMass_lt ranks hranks levels
    (nu * epsilon ^ 2) v homega hv (eta / M) (div_pos heta hM)
  refine ⟨tau0, htau0, max Nd Nm, hNd.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap keep tag tau htau htau0'
  let rough := admissionUnionModuli ranks levels keep tag N cap (nu * epsilon ^ 2) v tau
  have h := hdensity N ((le_max_left _ _).trans hN) hEven cap hcap rough
    (fun _ hd => P2LowerFiniteCellRounding.universe_rough N cap _ _
      (Finset.mem_filter.mp hd).1)
    (coefficient keep tag N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v) tau)
    (raw keep N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v))
  have hcoef := coefficient_error_on_admissionUnion_le_mass ranks levels keep tag N cap
    (nu * epsilon ^ 2) v tau
  have hm := hmass N ((le_max_right _ _).trans hN) hEven cap keep tag tau htau htau0'
  have hpay : M * reciprocalTotientDensity rough
      (fun d => |coefficient keep tag N cap ((N : ℝ) ^ (nu * epsilon ^ 2))
          ((N : ℝ) ^ v) tau d -
        raw keep N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v) d|) < eta := by
    have hsmall := hcoef.trans_lt hm
    have hp := (lt_div_iff₀ hM).mp hsmall
    simpa only [mul_comm] using hp
  have hscale := densityScale_pos (hNd.trans ((le_max_left _ _).trans hN))
  dsimp only at h ⊢
  exact h.trans_lt (mul_lt_mul_of_pos_right hpay hscale)

end
end ImbalancedChen.P4AHeldTaggedFiniteAdmissionPayment
