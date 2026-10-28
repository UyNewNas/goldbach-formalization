import ImbalancedChen.P2OriginalElevenAttachedOmittedDensity
import ImbalancedChen.FiniteUpperCarrierCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent canonical omitted source: the first SIX descending actual
prime factors of a genuine retained rough modulus form an original
eleven-cell omitted tuple.  This is a restriction of the actual common
policy's full modulus support, with every remaining rough factor and
every sign-selected small factor preserved.  Its signed density receives
the full normalized payment.  The final theorem exposes the exact same-Q
count and coprime mean; their AP discrepancy is still an unpaid sum.
-/

namespace ImbalancedChen.P2OriginalElevenCanonicalSameQOmission
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthCompactArithmeticFibre P2OriginalSixthOmittedArithmeticMass
open P2OriginalSixthCommonScheduleAndFullQ
open P2OriginalSixthSourceCompactCores P2CompactThirdHistorySelection
open P2OriginalFourthCapProducerInterface P1OriginalVariableFifthContinuation
open P2OriginalElevenFullModulusOmittedCover P2OriginalElevenAttachedOmittedDensity
open P5OriginalCommonRefinedConstructor

def descendingPrefix (p : Fin 6 → ℕ) : List ℕ := [p 0,p 1,p 2,p 3,p 4,p 5]

def CanonicalOmitted (c : Cell) (n N b : ℕ) : Prop :=
  ∃ p ∈ omittedTuples c n N, b.primeFactorsList.reverse.take 6 = descendingPrefix p

def canonicalRough (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (fixedRoughSupport ret N cap w z).filter (CanonicalOmitted c n N)

theorem canonicalRough_subset_cover (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z : ℝ) :
    canonicalRough ret c n N cap w z ⊆ omittedRough ret c n N cap w z := by
  intro b hb
  obtain ⟨hbS,p,hp,hprefix⟩ := Finset.mem_filter.mp hb
  have hsf := fixedRoughSupport_squarefree ret N cap w z hbS
  have hdiv := (List.take_sublist 6 b.primeFactorsList.reverse).prod_dvd_prod
  have hprod : (descendingPrefix p).prod = roughProduct p := by
    norm_num [descendingPrefix,roughProduct] <;> ring
  rw [hprefix,hprod,List.prod_reverse,Nat.prod_primeFactorsList hsf.ne_zero] at hdiv
  exact actual_omitted_prefix_covered ret c n N cap w z hbS hp hdiv

def canonicalModuli (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (canonicalRough ret c n N cap w z)

def canonicalRho (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (canonicalRough ret c n N cap w z)
    (fixedRoughCoefficient ret N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

/-- The source restriction is proved against the independently defined
original rho, not by giving two names to the candidate coefficient. -/
theorem canonicalRho_eq_actual_on_support (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ canonicalModuli ret c n N cap w z) :
    canonicalRho ret c n N cap w z L q = actualSmallRoughRho ret N cap w z L q := by
  obtain ⟨⟨e,b⟩,heb,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he,hb⟩ := Finset.mem_product.mp heb
  have hbS := (Finset.mem_filter.mp hb).1
  rw [canonicalRho,actualSmallRoughRho]
  rw [smallRoughRho_mul (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z
      (Finset.mem_filter.mp hd).1) _ _ _ he hb]
  rw [smallRoughRho_mul (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z hd) _ _ _ he hbS]

def canonicalDensity (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ q ∈ canonicalModuli ret c n N cap w z, actualSmallRoughRho ret N cap w z L q /
    (Nat.totient q : ℝ)

theorem canonicalDensity_eq_restricted (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z L : ℝ) :
    canonicalDensity ret c n N cap w z L =
      restrictedDensity ret N cap w z L (canonicalRough ret c n N cap w z) := by
  apply Finset.sum_congr rfl
  intro q hq
  change actualSmallRoughRho ret N cap w z L q / (Nat.totient q : ℝ) =
    canonicalRho ret c n N cap w z L q / (Nat.totient q : ℝ)
  rw [canonicalRho_eq_actual_on_support ret c n N cap w z L hq]

/-- All eleven actual canonical prefix walls, with the full small and
residual modulus sums, fit one prescribed normalized SIGNED DENSITY
reserve.  The policy may be the actual common-refined policy8 at N. -/
theorem exists_all_eleven_canonical_density_payment (epsilon r eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ ret : List ℕ → Bool,
        (∑ c ∈ allCells.toFinset,
          |canonicalDensity ret c n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)|) <
          eta * singularSeries N / Real.log (N : ℝ) := by
  let k : ℝ := allCells.toFinset.card
  have hk : 0 < k+1 := by dsimp [k]; positivity
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_full_attached_density_payment epsilon r (eta/(k+1))
    he he8 her (div_pos heta hk)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap ret
  have hN2 := hN₀.trans hN
  have hnorm : 0 < singularSeries N / Real.log (N : ℝ) :=
    div_pos (singularSeries_pos N)
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hrow (c : Cell) :
      |canonicalDensity ret c n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)| ≤
        (eta/(k+1))*(singularSeries N/Real.log (N : ℝ)) := by
    rw [canonicalDensity_eq_restricted]
    simpa only [div_eq_mul_inv,mul_assoc] using
      (h n hn N hN hEven cap hcap ret c _
        (canonicalRough_subset_cover ret c n N cap _ _)).le
  calc
    _ ≤ ∑ _c ∈ allCells.toFinset, (eta/(k+1))*(singularSeries N/Real.log (N : ℝ)) :=
      Finset.sum_le_sum (fun c _ => hrow c)
    _ = k*((eta/(k+1))*(singularSeries N/Real.log (N : ℝ))) := by simp [k]
    _ < eta*(singularSeries N/Real.log (N : ℝ)) := by
      have hscalar : k*(eta/(k+1)) < eta := by
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ hk).2
        nlinarith
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hscalar hnorm
    _ = _ := by ring

def commonCanonicalDensity (d : OriginalData) (c : Cell) (n N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ q ∈ canonicalModuli ((policy8 d (N : ℝ)) false) c n N cap w z,
    rho d N cap w z L q / (Nat.totient q : ℝ)

theorem commonCanonicalDensity_eq (d : OriginalData) (c : Cell) (n N cap : ℕ) (w z L : ℝ) :
    commonCanonicalDensity d c n N cap w z L =
      canonicalDensity ((policy8 d (N : ℝ)) false) c n N cap w z L := rfl

/-- The original eleven domains already have a uniform positive t6 floor.
Replacing only the auxiliary roughFloor field avoids a spurious circular
requirement to choose the beta parameter from a later mesh-dependent floor. -/
theorem exists_commonChoice_uniform_roughFloor (n : ℕ) :
    ∃ D : CompactThirdChoice (commonCore n), D.roughFloor = (53/9216 : ℝ) := by
  obtain ⟨D⟩ := exists_commonChoice n
  let D' : CompactThirdChoice (commonCore n) := { D with
    roughFloor := 53/9216
    roughFloor_pos := by norm_num
    rough_margin := by
      intro t ht
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp ht
      have hp := (coreSequence_subset_sourceRegion c n hc).compactCutoff
      linarith }
  exact ⟨D',rfl⟩

/-- One actual finite compact table and one fixed beta/rough choice feed
the SAME common-refined policy8 and its original full-q coefficient.
Every subsequent target uses that already fixed table. -/
theorem exists_common_policy_density_schedule (epsilon r eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r)
    (hefloor : epsilon^2 ≤ (53/9216 : ℝ)) (heta : 0 < eta) :
    ∃ (n N₀ : ℕ) (D : CompactThirdChoice (commonCore n)),
      2 ≤ N₀ ∧ epsilon^2 ≤ D.roughFloor ∧
      ∀ N, N₀ ≤ N → Even N → ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) →
      ∀ (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh)),
      let d := dataOfChoice D (epsilon^2) rows4 licensed4 J5 rows5
      (∑ c ∈ allCells.toFinset,
        |commonCanonicalDensity d c n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)|) <
        eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨n,N₀,hN₀,h⟩ := exists_all_eleven_canonical_density_payment epsilon r eta he he8 her heta
  obtain ⟨D,hD⟩ := exists_commonChoice_uniform_roughFloor n
  refine ⟨n,N₀,D,hN₀,?_,?_⟩
  · simpa only [hD] using hefloor
  · intro N hN hEven cap hcap rows4 licensed4 J5 rows5
    exact h n le_rfl N hN hEven cap hcap
      ((policy8 (dataOfChoice D (epsilon^2) rows4 licensed4 J5 rows5) (N : ℝ)) false)

/-- EXACT original count-minus-coprime-mean, after the ENTIRE full-q
sum and its genuine small/residual pairs.  This identity does not claim
that a small density bounds this AP discrepancy. -/
theorem actual_same_q_AP_pair_identity (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z L b T : ℝ) :
    realPhysicalDistributionError b N T (canonicalModuli ret c n N cap w z)
      (actualSmallRoughRho ret N cap w z L) =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (canonicalRough ret c n N cap w z),
        smallRoughPairCoefficient (fixedRoughCoefficient ret N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) x *
          (realHalfProductCongruenceMass b N T (x.1*x.2) -
            realHalfProductCoprimeMass b N T (x.1*x.2)/(Nat.totient (x.1*x.2) : ℝ)) := by
  have heq : realPhysicalDistributionError b N T (canonicalModuli ret c n N cap w z)
      (actualSmallRoughRho ret N cap w z L) =
      realPhysicalDistributionError b N T (canonicalModuli ret c n N cap w z)
        (canonicalRho ret c n N cap w z L) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [canonicalRho_eq_actual_on_support ret c n N cap w z L hq]
  rw [heq]
  exact sum_smallRoughRho_mul
    (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
    (fun _ hb => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z
      (Finset.mem_filter.mp hb).1) _ _ _ _

end
end ImbalancedChen.P2OriginalElevenCanonicalSameQOmission
