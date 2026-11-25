import ImbalancedChen.P3OriginalU5AllSignedSquares
import ImbalancedChen.ActualSelectedSubproductParameters
import ImbalancedChen.Part3ActualCompactInitialSupport

/-!
# Actual original U5 root V sources for the coefficient allocator

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The original root is the maximum of v(t), v(t+u), and B(a). Its two
selected S-tags do not prescribe which of the first two products is
licensed for (F). Here that choice is computed from the original maximum.
The singleton is the larger original prime t.2; the pair is t.2,t.1.

For an actual last source equal to the original root, the preceding
all-source signed theorem supplies the complete word's full squares.
The existing selected-prefix theorem then supplies the winning prefix's
remaining squares. No tail, small-factor, or greedy algorithm is repeated.

Exact change of base is reused from physical_power_eq_local. The original
buffer pays explicit local-scale and residue perturbations. The critical
interval, the change-of-base identity, and the winning source are outputs.
The local scale is in the manuscript's compact regime x <= N <= x^(1+kappa).
This regime still has to be supplied by an actual physical atom family.

The W outcome, actual fresh-row sources, endpoint atomization, common-Q
family adoption and the whole-coefficient three-factor identity remain
separate. In particular this is a pointwise allocator-input supplier,
not an estimate for PP and not a claim that the carrier .599 is theta_cov.
-/

namespace ImbalancedChen.P3OriginalU5RootVInputs

noncomputable section
open scoped Classical List
open P2LowerCapPlanIntegerRetention (coordinate)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension
open P3OriginalU5AllSourceSquares
open P3OriginalU5AllSignedSquares
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (fullModulus)
open Part3.ActualCompactInitialSupport (physical_power_eq_local)

/-- `false` is the original larger-prime prefix; `true` is both primes. -/
def prefixExponent (N : ℕ) (t : ℕ × ℕ) (both : Bool) : ℝ :=
  if both then coordinate N t.2 + coordinate N t.1 else coordinate N t.2

def factorPrefix (t : ℕ × ℕ) (both : Bool) : List ℕ :=
  if both then [t.2, t.1] else [t.2]

def factorRemainder (t : ℕ × ℕ) (both : Bool) (tail : List ℕ) : List ℕ :=
  if both then tail else t.1 :: tail

theorem factor_words (t : ℕ × ℕ) (both : Bool) (tail : List ℕ) :
    factorPrefix t both ++ factorRemainder t both tail = t.2 :: t.1 :: tail := by
  cases both <;> rfl

/-- Deterministic original-max routing. Ties prefer the singleton, then
    the pair. `none` records the original W alternative, not a failure. -/
def rootRoute (N : ℕ) (t : ℕ × ℕ) : Option Bool :=
  if VariableEnvelope.v (coordinate N t.2 + coordinate N t.1) ≤
        VariableEnvelope.v (coordinate N t.2) ∧
      VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a ≤
        VariableEnvelope.v (coordinate N t.2) then some false
  else if VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a ≤
      VariableEnvelope.v (coordinate N t.2 + coordinate N t.1) then some true
  else none

/-- The original root maximum itself supplies the selected branch value. -/
theorem root_route_sound (N : ℕ) (t : ℕ × ℕ) :
    match rootRoute N t with
    | none => rootLevel false N t =
        VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a
    | some both => rootLevel false N t =
        VariableEnvelope.v (prefixExponent N t both) := by
  unfold rootRoute
  split_ifs with hs hp
  · change max (VariableEnvelope.v (coordinate N t.2))
        (max (VariableEnvelope.v (coordinate N t.2 + coordinate N t.1))
          (VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a)) =
      VariableEnvelope.v (coordinate N t.2)
    exact max_eq_left (max_le hs.1 hs.2)
  · have hsp : VariableEnvelope.v (coordinate N t.2) ≤
        VariableEnvelope.v (coordinate N t.2 + coordinate N t.1) := by
      by_contra hn
      have hps := (lt_of_not_ge hn).le
      exact hs ⟨hps, hp.trans hps⟩
    change max (VariableEnvelope.v (coordinate N t.2))
        (max (VariableEnvelope.v (coordinate N t.2 + coordinate N t.1))
          (VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a)) =
      VariableEnvelope.v (coordinate N t.2 + coordinate N t.1)
    rw [max_eq_left hp, max_eq_right hsp]
  · have hpw : VariableEnvelope.v (coordinate N t.2 + coordinate N t.1) ≤
        VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a :=
      (lt_of_not_ge hp).le
    have hsw : VariableEnvelope.v (coordinate N t.2) ≤
        VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a := by
      by_contra hn
      have hws := (lt_of_not_ge hn).le
      exact hs ⟨hpw.trans hws, hws⟩
    change max (VariableEnvelope.v (coordinate N t.2))
        (max (VariableEnvelope.v (coordinate N t.2 + coordinate N t.1))
          (VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a)) =
      VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a
    rw [max_eq_right hpw, max_eq_right hsw]

def localRatio (N : ℕ) (x : ℝ) : ℝ := Real.log (N : ℝ) / Real.log x

def cover (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  rootLevel false N t - (buffer : ℝ)

def thetaCov (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) (x zeta : ℝ) : ℝ :=
  localRatio N x * cover buffer N t + 2 * zeta

theorem local_ratio_power {N : ℕ} (hN : 0 < (N : ℝ))
    {x : ℝ} (hx : 1 < x) : x ^ localRatio N x = (N : ℝ) := by
  simpa only [localRatio, mul_one, Real.rpow_one] using
    (physical_power_eq_local hN hx (1 : ℝ)).symm

/-- Scale bounds are converted to the manuscript's actual q0, not passed
    as an independent rescaling license. -/
theorem local_ratio_bounds {N : ℕ} (hN : 0 < (N : ℝ))
    {x kappa : ℝ} (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hNx : (N : ℝ) ≤ x ^ (1 + kappa)) :
    1 ≤ localRatio N x ∧ localRatio N x ≤ 1 + kappa := by
  have hp := local_ratio_power hN hx
  constructor
  · apply (Real.rpow_le_rpow_left_iff hx).mp
    simpa only [Real.rpow_one, hp] using hxN
  · apply (Real.rpow_le_rpow_left_iff hx).mp
    simpa only [hp] using hNx

theorem cover_power_identity {N : ℕ} (hN : 0 < (N : ℝ))
    {x : ℝ} (hx : 1 < x) (buffer : ℚ) (t : ℕ × ℕ) (zeta : ℝ) :
    x ^ (thetaCov buffer N t x zeta - 2 * zeta) =
      (N : ℝ) ^ cover buffer N t := by
  have hexp : thetaCov buffer N t x zeta - 2 * zeta =
      localRatio N x * cover buffer N t := by unfold thetaCov; ring
  rw [hexp]
  exact (physical_power_eq_local hN hx (cover buffer N t)).symm

/-- The original root's auxiliary cover remains inside the enhanced
    interval after this buffer, independently of the V/W outcome. -/
theorem cover_enhanced (buffer : ℚ) (hb : 0 < buffer) (hb' : buffer ≤ 1/1000)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    (1/2 : ℝ) < cover buffer N t ∧ cover buffer N t < (153/256 : ℝ) := by
  obtain ⟨hu, hut, hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp
    (coordinates_mem_triangle hN ht)
  change Part5OriginalUpsilon5CausalDictionary.a ≤ coordinate N t.1 at hu
  change coordinate N t.1 < coordinate N t.2 at hut
  change coordinate N t.2 < Part5OriginalUpsilon5CausalDictionary.h at hh
  have hlo := (Part5OriginalUpsilon5CausalDictionary.level_bounds hu hut.le hh.le).1
  change (1 + coordinate N t.2) / 2 ≤ rootLevel false N t at hlo
  have hcap := original_root_seed_bounded false 0 (by norm_num) N t
  simp only [rootSeed, Rat.cast_zero, mul_zero, sub_zero] at hcap
  have hbR : (0 : ℝ) < buffer := by exact_mod_cast hb
  have hbR' : (buffer : ℝ) ≤ 1/1000 := by
    have hcast : (buffer : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := Rat.cast_le.mpr hb'
    norm_num at hcast ⊢
    exact hcast
  dsimp [cover, Part5OriginalUpsilon5CausalDictionary.a] at *
  constructor <;> linarith

/-- Exact base-N to base-x loss for the already proved two-line formula.
    The residue perturbation itself is delegated to the old three-line
    actualSelectedSubproductV_residue_margin theorem below. -/
theorem v_rescale_lower {q kappa : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 1 + kappa)
    (hkappa : 0 ≤ kappa) (s : ℝ) :
    q * VariableEnvelope.v s - kappa ≤ VariableEnvelope.v (q * s) := by
  have hq0 : 0 ≤ q := by linarith
  have ha := mul_le_mul_of_nonneg_left
    (show VariableEnvelope.v s ≤ VariableEnvelope.A s by
      rw [VariableEnvelope.v_eq_min]; exact min_le_left _ _) hq0
  have hc := mul_le_mul_of_nonneg_left
    (show VariableEnvelope.v s ≤ VariableEnvelope.C s by
      rw [VariableEnvelope.v_eq_min]; exact min_le_right _ _) hq0
  rw [VariableEnvelope.v_eq_min]
  dsimp [VariableEnvelope.A, VariableEnvelope.C] at *
  apply le_min <;> nlinarith

private theorem routed_critical_interval
    (buffer : ℚ) (hb : 0 ≤ buffer) (N : ℕ) (t : ℕ × ℕ) (both : Bool)
    (hroute : rootRoute N t = some both)
    (x zeta kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hkappa' : kappa ≤ (buffer : ℝ) / 4)
    (hzeta : zeta ≤ (buffer : ℝ) / 8)
    (hq : 1 ≤ localRatio N x) (hq' : localRatio N x ≤ 1 + kappa) :
    thetaCov buffer N t x zeta + (buffer : ℝ) / 8 ≤
      actualSelectedSubproductV (1 + 3 * kappa)
        (localRatio N x * prefixExponent N t both) ∧
      (2 * thetaCov buffer N t x zeta - 1 ≤
          localRatio N x * prefixExponent N t both ∧
        localRatio N x * prefixExponent N t both ≤
          actualSelectedSubproductUpper (1 + 3 * kappa) (thetaCov buffer N t x zeta)) := by
  have hwin := root_route_sound N t
  rw [hroute] at hwin
  have hscale := v_rescale_lower hq hq' hkappa (prefixExponent N t both)
  rw [← hwin] at hscale
  have hbR : (0 : ℝ) ≤ buffer := by exact_mod_cast hb
  have hpay : (buffer : ℝ) ≤ localRatio N x * (buffer : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hbR
  have hmargin : thetaCov buffer N t x zeta + (buffer : ℝ) / 4 ≤
      VariableEnvelope.v (localRatio N x * prefixExponent N t both) := by
    dsimp [thetaCov, cover]
    nlinarith
  have hpert := actualSelectedSubproductV_residue_margin hbR hkappa' hmargin
  refine ⟨hpert, (actualSelectedSubproduct_critical_iff _ _ _).mp ?_⟩
  linarith

theorem prefix_power {N : ℕ} (hN : 1 < (N : ℝ)) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (both : Bool) :
    (N : ℝ) ^ prefixExponent N t both = ((factorPrefix t both).prod : ℝ) := by
  obtain ⟨hp, hq, _⟩ := chenY5PrimeSelector_ordered_prime_data ht
  cases both <;>
    simp [prefixExponent, factorPrefix, Real.rpow_add (zero_lt_one.trans hN),
      coordinate_power hN hp.pos, coordinate_power hN hq.pos]

/-- Exact pointwise inputs for the old prefix allocator. The full word
    contains the SAME signed small witness, although that witness must
    remain separately grouped in a later fixed-rank whole-atom proof. -/
structure RootVInputs (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) (k s : ℕ)
    (chosen : List ℕ) (both : Bool) (x zeta kappa : ℝ) : Prop where
  route : rootRoute N t = some both
  zeta_pos : 0 < zeta
  source_value : rootLevel false N t = VariableEnvelope.v (prefixExponent N t both)
  residue_parameter : localRatio N x ≤ 1 + 3 * kappa
  level_range : (1/2 : ℝ) < cover buffer N t ∧ cover buffer N t < (153/256 : ℝ)
  level_identity : x ^ (thetaCov buffer N t x zeta - 2 * zeta) =
    (N : ℝ) ^ cover buffer N t
  selected_identity : x ^ (localRatio N x * prefixExponent N t both) =
    ((factorPrefix t both).prod : ℝ)
  critical_reserve : thetaCov buffer N t x zeta + (buffer : ℝ) / 8 ≤
    actualSelectedSubproductV (1 + 3 * kappa) (localRatio N x * prefixExponent N t both)
  critical_interval :
    2 * thetaCov buffer N t x zeta - 1 ≤ localRatio N x * prefixExponent N t both ∧
    localRatio N x * prefixExponent N t both ≤
      actualSelectedSubproductUpper (1 + 3 * kappa) (thetaCov buffer N t x zeta)
  full : actualDwellSupport (x ^ (thetaCov buffer N t x zeta - 2 * zeta))
    (factorPrefix t both ++ factorRemainder t both (chosen ++ s.primeFactorsList.reverse))
  selected : actualDwellSupport
    (x ^ (thetaCov buffer N t x zeta - 2 * zeta) / (factorPrefix t both).prod)
    (factorRemainder t both (chosen ++ s.primeFactorsList.reverse))
  canonical : factorPrefix t both ++
    factorRemainder t both (chosen ++ s.primeFactorsList.reverse) =
      (fullModulus t k).primeFactorsList.reverse

/-- Consume the actual root-origin signed supplier. The two V products
    and the W alternative are determined internally from the original
    max. Neither a winner, critical interval nor remaining budget is an
    input. This is pointwise; no fixed whole-box assignment is claimed. -/
theorem signed_root_V_inputs
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 < buffer) (hb' : buffer ≤ 1/1000)
    (epsilon : ℝ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    {k s : ℕ} {chosen : List ℕ} {slots : List (ℕ × Bool)}
    (hsigned : SignedSupply R bank buffer epsilon N t k s chosen .root slots)
    (x zeta kappa : ℝ) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hNx : (N : ℝ) ≤ x ^ (1 + kappa))
    (hzeta0 : 0 < zeta) (hzeta : zeta ≤ (buffer : ℝ) / 8)
    (hkappa : 0 ≤ kappa) (hkappa' : kappa ≤ (buffer : ℝ) / 4) :
    (rootRoute N t = none ∧ rootLevel false N t =
      VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a) ∨
    ∃ both, RootVInputs buffer N t k s chosen both x zeta kappa := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hNr
  have hword : (appendUnselected slots s.primeFactorsList.reverse).map Prod.fst =
      t.2 :: t.1 :: (chosen ++ s.primeFactorsList.reverse) := by
    rw [appendUnselected_values, hsigned.rough.values]
    rfl
  have hfull : actualDwellSupport ((N : ℝ) ^ cover buffer N t)
      (t.2 :: t.1 :: (chosen ++ s.primeFactorsList.reverse)) := by
    have hg := hsigned.full
    change IntegerSquareGates N (cover buffer N t) 1
      ((appendUnselected slots s.primeFactorsList.reverse).map Prod.fst) at hg
    rw [hword] at hg
    intro i hi
    simpa only [Nat.one_mul, actualNatList_cast_prod] using
      integerSquareGates_at _ hg i hi
  have hq := local_ratio_bounds hNpos hx hxN hNx
  have hpower := cover_power_identity hNpos hx buffer t zeta
  cases hroute : rootRoute N t with
  | none =>
      left
      refine ⟨hroute, ?_⟩
      have h := root_route_sound N t
      simpa only [hroute] using h
  | some both =>
      right
      have hwin := root_route_sound N t
      rw [hroute] at hwin
      have hcrit := routed_critical_interval buffer hb.le N t both hroute
        x zeta kappa hkappa hkappa' hzeta hq.1 hq.2
      have hpref : 0 < (factorPrefix t both).prod := by
        obtain ⟨hp, hq, _⟩ := chenY5PrimeSelector_ordered_prime_data ht
        cases both
        · simpa [factorPrefix] using hq.pos
        · simpa [factorPrefix] using Nat.mul_pos hq.pos hp.pos
      have hfullLocal : actualDwellSupport (x ^ (thetaCov buffer N t x zeta - 2 * zeta))
          (factorPrefix t both ++ factorRemainder t both
            (chosen ++ s.primeFactorsList.reverse)) := by
        rw [hpower, factor_words]
        exact hfull
      refine ⟨both, hroute, hzeta0, hwin, by linarith [hq.2],
        cover_enhanced buffer hb hb' hN ht, hpower, ?_, hcrit.1, hcrit.2,
        hfullLocal, ?_, ?_⟩
      · rw [← physical_power_eq_local hNpos hx]
        exact prefix_power hNr ht both
      · exact actualDwell_selected_prefix_budget (factorPrefix t both)
          (factorRemainder t both (chosen ++ s.primeFactorsList.reverse)) hpref hfullLocal
      · rw [factor_words]
        exact hword.symm.trans hsigned.canonical

/-- The original nonzero native coefficient supplies all witnesses first.
    The additional conclusion applies exactly when that returned actual
    last source is the original root. Fresh-row cases retain their signed
    square supply and are not relabeled as root sources. -/
theorem native_U5_root_V_inputs
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 < buffer) (hb' : buffer ≤ 1/1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1/8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0)
    (x zeta kappa : ℝ) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hNx : (N : ℝ) ≤ x ^ (1 + kappa))
    (hzeta0 : 0 < zeta) (hzeta : zeta ≤ (buffer : ℝ) / 8)
    (hkappa : 0 ≤ kappa) (hkappa' : kappa ≤ (buffer : ℝ) / 4) :
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N) ∧ k = s * chosen.prod ∧
        (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).accepted = true ∧
        ∃ source slots, SignedSupply R bank buffer epsilon N t k s chosen source slots ∧
          (source = .root →
            (rootRoute N t = none ∧ rootLevel false N t =
              VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a) ∨
            ∃ both, RootVInputs buffer N t k s chosen both x zeta kappa) := by
  obtain ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsigned⟩ :=
    native_U5_nonzero_all_signed_squares R bank buffer hb.le hb' epsilon
      hepsilon hepsilon8 hgrid halloc hN ht hk
  refine ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsigned, ?_⟩
  intro hsource
  subst source
  exact signed_root_V_inputs R bank buffer hb hb' epsilon hN ht hsigned
    x zeta kappa hx hxN hNx hzeta0 hzeta hkappa hkappa'

end
end ImbalancedChen.P3OriginalU5RootVInputs
