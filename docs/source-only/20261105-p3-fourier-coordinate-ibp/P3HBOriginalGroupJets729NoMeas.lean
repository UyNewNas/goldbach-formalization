import ImbalancedChen.P3HBOriginalGroupJets729Integrated
import ImbalancedChen.P3HBOriginalGroupTrimAllOrder
import ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-!
P3.6: discharge the remaining higher-jet MEASURABILITY hypothesis of the
genuine geometry-jet x all 729 original smooth HB children integral.

Unlike an arbitrary supplied derivative field, every jet below is the
ordered, repetition-preserving coordinate derivative of the LITERAL
occurrence-indexed product of original grouped dyadic factors and ONE
complete physical-product trim. Continuity is derived from the existing
true all-order finite Leibniz identities, scalar smooth profiles, and
finite sums/products. No measurable-jet assumption remains in the final
integral statement.

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2 and 4(F).
Pinned Lean: v4.33.0-rc1; Mathlib:
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This is only the integrated geometry-jet TIMES HB-tensor contribution.
It does not assert the all-order derivative of their entire product,
nor actual U5/hats, growing m(T), Fourier H-tails or same-rho PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupJets729NoMeas
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalGroupTrimAllOrder
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBOriginalGroupJets729Integrated
open ImbalancedChen.P3HBExplicitSmoothCutoffs

/-- True original finite positional sum is continuous on the six-chart. -/
theorem originalGroupSum_continuous (J : Finset (Fin 6)) :
    Continuous (originalGroupSum J) := by
  change Continuous (fun u : Fin 6 → ℝ => ∑ j ∈ J, u j)
  exact continuous_finsetSum J (fun j _ => continuous_apply j)

/-- Each actual arbitrary ordered jet of ONE original group is continuous.
No commutation of mixed partial derivatives is required. -/
theorem originalGroupFactorJet_continuous
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : ℝ) (J : Finset (Fin 6)) (axes : List (Fin 6)) :
    Continuous (originalOrderedAxisDeriv axes
      (originalGroupDyadicFactor chi c J)) := by
  classical
  by_cases hwithin : axesWithinGroup J axes
  · have hsmooth : ContDiff ℝ ⊤ (groupDyadicLogProfile chi c) :=
      originalGroupProfile_contDiff chi hchi c
    have hscalar : Continuous
        (iteratedDeriv axes.length (groupDyadicLogProfile chi c)) :=
      hsmooth.continuous_iteratedDeriv axes.length le_top
    have heq :
        originalOrderedAxisDeriv axes (originalGroupDyadicFactor chi c J) =
          (fun u => iteratedDeriv axes.length
            (groupDyadicLogProfile chi c) (originalGroupSum J u)) := by
      funext u
      simpa only [if_pos hwithin] using
        (originalGroupOrderedDeriv_exact chi c J axes u)
    rw [heq]
    exact hscalar.comp (originalGroupSum_continuous J)
  · have heq :
        originalOrderedAxisDeriv axes (originalGroupDyadicFactor chi c J) =
          (fun _ : Fin 6 → ℝ => (0 : ℂ)) := by
      funext u
      simpa only [if_neg hwithin] using
        (originalGroupOrderedDeriv_exact chi c J axes u)
    rw [heq]
    exact continuous_const

/-- A literal owner allocation is a finite product of continuous,
genuinely derived group jets (including empty and repeated owners). -/
theorem allocatedGroupJetProduct_continuous {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g) :
    Continuous (allocatedGroupJetProduct chi c J axes owner) := by
  classical
  unfold allocatedGroupJetProduct
  apply continuous_finsetProd Finset.univ
  intro j _
  exact originalGroupFactorJet_continuous chi hchi (c j) (J j)
    (axesAssigned axes owner j)

/-- The exact finite group owner sum, not an abstract jet field,
is continuous in all original positional logarithmic coordinates. -/
theorem allocatedGroupJetSum_continuous {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) :
    Continuous (allocatedGroupJetSum chi c J axes) := by
  classical
  unfold allocatedGroupJetSum
  apply continuous_finsetSum Finset.univ
  intro owner _
  exact allocatedGroupJetProduct_continuous chi hchi c J axes owner

/-- Continuity of every actual group-PRODUCT ordered jet follows from
the proven original Fin.cons owner-sum identity, not by adding smoothness
of a newly postulated derivative family as an assumption. -/
theorem originalGroupProductJet_continuous {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : List (Fin 6)) :
    Continuous (originalOrderedAxisDeriv axes
      (originalGroupProduct chi c J)) := by
  classical
  let a : Fin axes.length → Fin 6 := fun r => axes.get r
  have ha : List.ofFn a = axes := by simp [a]
  have heq :
      originalOrderedAxisDeriv axes (originalGroupProduct chi c J) =
        allocatedGroupJetSum chi c J a := by
    funext u
    rw [← ha]
    exact originalGroupProduct_ordered_eq_allocation
      chi hchi c J axes.length a u
  rw [heq]
  exact allocatedGroupJetSum_continuous chi hchi c J a

/-- Actual complete-product trim jets remain continuous on the WHOLE
real six-chart; no false compact support is ascribed to eta at order 0. -/
theorem physicalTrimJet_continuous
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (s : ℝ) (axes : List (Fin 6)) :
    Continuous (originalOrderedAxisDeriv axes (physicalTrim eta s)) := by
  have hp : ContDiff ℝ ⊤ (trimLogProfile eta s) := by
    unfold trimLogProfile
    fun_prop
  have hscalar : Continuous
      (iteratedDeriv axes.length (trimLogProfile eta s)) :=
    hp.continuous_iteratedDeriv axes.length le_top
  have heq :
      originalOrderedAxisDeriv axes (physicalTrim eta s) =
        (fun u => iteratedDeriv axes.length (trimLogProfile eta s)
          (originalGroupSum Finset.univ u)) := by
    funext u
    exact physicalTrim_orderedDeriv_exact eta s axes u
  rw [heq]
  exact hscalar.comp (originalGroupSum_continuous Finset.univ)

/-- All binary owner terms have the ordinary continuity inherited from
the two genuine factors, before applying any norm or integral. -/
theorem binarySum_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) :
    Continuous (binarySum chi eta c J s axes) := by
  classical
  unfold binarySum
  apply continuous_finsetSum Finset.univ
  intro owner _
  change Continuous (binaryTerm chi eta c J s axes owner)
  unfold binaryTerm
  exact (originalGroupProductJet_continuous chi hchi c J
    (axesAssigned axes owner 0)).mul
    (physicalTrimJet_continuous eta heta s (axesAssigned axes owner 1))

/-- The true whole group x ONE full-product-trim higher ordered jet
is continuous; repetitions, all group occurrences and scales survive. -/
theorem originalGroupPhysicalTrimJet_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) :
    Continuous (originalOrderedAxisDeriv (List.ofFn axes)
      (originalGroupPhysicalTrim chi eta c J s)) := by
  have heq :
      originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupPhysicalTrim chi eta c J s) =
          binarySum chi eta c J s axes := by
    funext u
    exact originalGroupPhysicalTrim_ordered_eq_binary
      chi eta hchi heta c J s k axes u
  rw [heq]
  exact binarySum_continuous chi eta hchi heta c J s axes

/-- The exact previously supplied measurability premise of the 729-child
integrated source follows from genuine source C-infinity and Leibniz. -/
theorem originalGroupPhysicalTrimJet_norm_measurable {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) :
    Measurable (fun u : Fin 6 → ℝ =>
      ‖originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupPhysicalTrim chi eta c J s) u‖) := by
  exact (originalGroupPhysicalTrimJet_continuous
    chi eta hchi heta c J s axes).norm.measurable

/-- The inherited full 729-label geometry-jet times HB tensor L1
statement, now WITHOUT a separate measurable-jet hypothesis. The
geometry is the actual group product x one physical trim.
This is still NOT the complete Leibniz derivative of (geometry * HB). -/
theorem originalGroupJetChildren_integrable_polynomial_no_meas
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ B Ceta C : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧ 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (orders : Fin 6 → ℕ), (∀ i, orders i ≤ K) →
        Integrable (originalGroupJetChildrenMass
          chi eta c J s axes orders) ∧
        (∫ u : Fin 6 → ℝ,
          originalGroupJetChildrenMass chi eta c J s axes orders u) ≤
          ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, hresult⟩ :=
    originalGroupJetChildren_integrable_polynomial
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge K
  refine ⟨B, Ceta, C, hB, hCeta, hC, ?_⟩
  intro g k c J hc s hs axes hk orders horders
  exact hresult g k c J hc s hs axes hk orders horders
    (originalGroupPhysicalTrimJet_norm_measurable
      chi eta hchi heta c J s axes)

/-- Apply the no-measurability result to the actual chosen admissible
C-infinity cutoff and trim, not an arbitrary replacement W_T profile. -/
theorem chosenGroupJetChildren_integrable_polynomial_no_meas (K : ℕ) :
    ∃ B Ceta C : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧ 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (orders : Fin 6 → ℕ), (∀ i, orders i ≤ K) →
        Integrable (originalGroupJetChildrenMass
          chosenChi chosenEta c J s axes orders) ∧
        (∫ u : Fin 6 → ℝ,
          originalGroupJetChildrenMass
            chosenChi chosenEta c J s axes orders u) ≤
          ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
  exact originalGroupJetChildren_integrable_polynomial_no_meas
    chosenChi chosenEta chosenChi_smooth chosenEta_smooth
    chosenChi_left chosenChi_right chosenChi_dyadic_contraction
    chosenEta_left chosenEta_right K

end
end ImbalancedChen.P3HBOriginalGroupJets729NoMeas
