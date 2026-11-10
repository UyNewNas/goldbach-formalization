import ImbalancedChen.P4AOriginalNewFifthPhysical

/-! The original enlarged eighth tree supplies the physical beta term.
Its tagged ALL/ANY compiler then changes that term by two actual signed
slopes. The compiled coefficient also supplies the real count. -/
namespace ImbalancedChen.P4AOriginalNewFifthCounting
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthPhysical (Joined beforeEight)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87JointPhysicalBudget (cutoff_le_target)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalVariableFifthPhysicalLedger (physical smallPlus smallMinus)
open P5OriginalCommonPositivePresieve (normalize)
open P4AUpperTaggedContinuationAccounting (positiveChangedMass negativeChangedMass
  physical_compiler_change_eq_signed_changed_masses)

abbrev tree (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :=
  P4AOriginalFull87UnionHistory.policy (width r) n e q a (N : ℝ)

def coefficient (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ)
    (tag : ℕ → List Bool) (w tau L : ℝ) : ℕ → ℝ :=
  P4AUpperTaggedBetaAttachment.rho (tree r n e q a N false) tag N N w (cutoff N) tau L

def signedMoves (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ)
    (tag : ℕ → List Bool) (w tau L : ℝ) : ℝ :=
  let keep := tree r n e q a N false
  smallPlus N N w L * positiveChangedMass keep tag N N w (cutoff N) tau +
    smallMinus N N w L * negativeChangedMass keep tag N N w (cutoff N) tau

theorem compiled_density (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ)
    (tag : ℕ → List Bool) (w tau L : ℝ) :
    physicalDensitySum (moduli N w) (coefficient r n e q a N tag w tau L) =
      physical (tree r n e q a N) N N w (cutoff N) L + signedMoves r n e q a N tag w tau L := by
  have h := physical_compiler_change_eq_signed_changed_masses (tree r n e q a N false)
    tag N N w (cutoff N) tau L
  change physicalDensitySum (moduli N w) (coefficient r n e q a N tag w tau L) -
    physical (tree r n e q a N) N N w (cutoff N) L = signedMoves r n e q a N tag w tau L at h
  linarith only [h]

theorem actual_majorant (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ)
    (tag : ℕ → List Bool) (w tau L : ℝ) (hL : 1 < L) (hwL : w ≤ L)
    (hwz : w ≤ cutoff N) (hzN : cutoff N ≤ (N : ℝ)) (x : ℕ) :
    (if Nat.Coprime x (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (moduli N w) (coefficient r n e q a N tag w tau L) x := by
  have h := P4AUpperTaggedBetaAttachment.rho_majorant (tree r n e q a N false) tag N N
    w (cutoff N) tau L hL hwL hwz hzN (x : ℤ)
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  simpa only [Int.natAbs_natCast] using h

def upper (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ)
    (tag : ℕ → List Bool) (w tau L eps : ℝ) : ℝ :=
  (beforeEight n e q a N - (savedGain : ℝ) + eps) * (singularSeries N / Real.log (N : ℝ)) +
    signedMoves r n e q a N tag w tau L

/-- The same fully specified finite compiler coefficient enters the
density and distribution error. The original G2, G3, G5 and G15–G22
and one positive beta projection have already been applied. -/
theorem exists_actual_compiled_count (nu eps betaMax eMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) (heMax : 0 < eMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 ≤ (19/96 : ℝ)/nu ∧
    ∀ b kappa : ℝ, 0 < b → b < 1 → (19/96 : ℝ) < (1-kappa)*(b/(1+b)) →
    Joined eMax (fun r n e q a N =>
      let w := (N : ℝ)^(nu*beta^2)
      let L := (N : ℝ)^(nu*beta)
      let T := manuscriptHalfProductCutoff kappa N
      ∀ (tag : ℕ → List Bool) (tau : ℝ),
        let rho := coefficient r n e q a N tag w tau L
        let U := upper r n e q a N tag w tau L eps
        physicalDensitySum (moduli N w) rho < U ∧
        (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) * U +
          realPhysicalDistributionError b N T (moduli N w) rho + (Nat.ceil (cutoff N) : ℝ) + (T+1)) := by
  obtain ⟨beta,hb,hb8,hbM,hbs,hJoined⟩ :=
    P4AOriginalNewFifthPhysical.exists_joined_positive_presieve nu eps betaMax eMax hnu heps hMax heMax
  refine ⟨beta,hb,hb8,hbM,hbs,?_⟩
  intro b kappa hbpos hb1 hgap
  apply P4AOriginalNewFifthPhysical.joined_eventually_mono hJoined
  have hG := eventually_manuscript_sieve_gate hbpos (by norm_num : (0 : ℝ) ≤ 19/96) hgap
  filter_upwards [hG] with N hgate
  intro r n e q a hN hp
  let w := (N : ℝ)^(nu*beta^2)
  let L := (N : ℝ)^(nu*beta)
  let T := manuscriptHalfProductCutoff kappa N
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hNR
  have hL : 1 < L := Real.one_lt_rpow hNR (mul_pos hnu hb)
  have hb1' : beta < 1 := hb8.trans (by norm_num)
  have hwL : w ≤ L := Real.rpow_le_rpow_of_exponent_le hNR.le
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_lt_mul_of_pos_left hb1' hb] : beta^2 ≤ beta) hnu.le)
  obtain ⟨_,hwz,hphys⟩ := hp
  let V := physical (tree r n e q a N) N N w (cutoff N) L
  have cancel : normalize N V * (singularSeries N / Real.log (N : ℝ)) = V := by
    unfold normalize
    field_simp [(singularSeries_pos N).ne',hlog.ne'] <;> ring
  change normalize N V < beforeEight n e q a N - (savedGain : ℝ) + eps at hphys
  have hV := mul_lt_mul_of_pos_right hphys (densityScale_pos hN)
  rw [cancel] at hV
  intro tag tau
  have hd : physicalDensitySum (moduli N w) (coefficient r n e q a N tag w tau L) <
      upper r n e q a N tag w tau L eps := by
    rw [compiled_density]
    exact add_lt_add_right hV _
  refine ⟨hd,?_⟩
  have hc := RealB_cast_le_same_rho_main_add_distribution_of_gate N (Nat.ceil (cutoff N))
    (moduli N w) (coefficient r n e q a N tag w tau L) hbpos hb1 hgate.1 hgate.2
    (fun _ hm _ => compiled_modulus_dvd N w hwz hm)
    (actual_majorant r n e q a N tag w tau L hL hwL hwz (cutoff_le_target N hNR.le))
  have hm := mul_le_mul_of_nonneg_left hd.le (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hc.trans (add_le_add_right (add_le_add_right (add_le_add_right hm _) _) _)

end
end ImbalancedChen.P4AOriginalNewFifthCounting
