import ImbalancedChen.P5OriginalOrdinaryConditionalPrefix

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The native upper coefficient has a conditional residual factorization as
an arithmetic function, including coefficients outside the finite carrier.
The separation hypotheses allow repeated prime powers, forbidden target
primes and factors beyond the enumeration cap; support membership is proved
rather than assumed in the main theorem. Zero factors are treated separately.
The small level is literally L/d and its sign is selected by the actual
rough prime-factor cardinality. No independent fixed beta is identified.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryResidualArithmeticFactor

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup OriginalOrdinaryConditionalPrefix
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

def roughWeight (N cap : ℕ) (w Z L : ℝ) (d : ℕ) : ℝ :=
  upperWeight (roughProduct N cap w Z) L d

def residualSmallWeight (N cap : ℕ) (w L : ℝ) (d e : ℕ) : ℝ :=
  if Even d.primeFactors.card then actualSmallRosserPlus N cap w (L/(d:ℝ)) e
  else actualSmallRosserMinus N cap w (L/(d:ℝ)) e

/-- Separation determines support exactly, even for nonsquarefree factors.
This is the reason no omitted or repeated-prime row can survive the split. -/
theorem separated_support_iff {N cap e d : ℕ} {w Z : ℝ}
    (hwZ : w≤Z) (he : SmallPrimeSupportedAt w e) (hd : RoughPrimeSupportedAt w d) :
    e*d∈actualSmallRosserSupport N cap Z ↔
      e∈actualSmallRosserSupport N cap w ∧ d∈roughSupport N cap w Z := by
  rw [nativeSupport_eq_products N cap hwZ]
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    have hp : (a,b)=(e,d) := smallRough_factorization_unique
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
      (roughSupport_rough hb) he hd hprod
    have haeq : a=e := congrArg Prod.fst hp
    have hbeq : b=d := congrArg Prod.snd hp
    exact ⟨by simpa only [haeq] using ha,by simpa only [hbeq] using hb⟩
  · rintro ⟨he,hd⟩
    exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hd⟩,rfl⟩

private theorem redundant_cutoff_factor {c r u v : Prop}
    [Decidable c] [Decidable r] [Decidable u] [Decidable v]
    (h : c→r) (a b : ℝ) :
    (if c∧u∧v then a*b else 0)=
      (if r∧u then a else 0)*(if c∧v then b else 0) := by
  by_cases hc : c
  · have hr := h hc
    by_cases hu : u <;> by_cases hv : v <;> simp [hc,hr,hu,hv]
  · simp [hc]

/-- Supported form of the exact coefficient identity, with no active-row
assumption. Strict level failures and all upper/lower prefix failures remain. -/
theorem native_upper_residual_factor_on_support {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w≤Z) (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈roughSupport N cap w Z) :
    actualSmallRosserPlus N cap Z L (e*d)=
      roughWeight N cap w Z L d * residualSmallWeight N cap w L d e := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdpos : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hdR.1
  have heone : (1:ℝ)≤e := by exact_mod_cast Nat.pos_of_ne_zero heS.1
  have hmem : e*d∈actualSmallRosserSupport N cap Z :=
    (separated_support_iff hwZ heS hdR).mpr ⟨he,hd⟩
  have hcut : (e:ℝ)<L/(d:ℝ) ↔ ((e*d:ℕ):ℝ)<L := by
    rw [lt_div_iff₀ hdpos,Nat.cast_mul]
  have hredundant : (((e*d:ℕ):ℝ)<L)→((d:ℝ)<L) := by
    intro h
    have hm := mul_le_mul_of_nonneg_right heone (Nat.cast_nonneg d)
    simp only [one_mul] at hm
    rw [Nat.cast_mul] at h
    exact hm.trans_lt h
  have hcard : (e*d).primeFactors.card=d.primeFactors.card+e.primeFactors.card := by
    rw [Nat.primeFactors_mul heS.1 hdR.1,
      Finset.card_union_of_disjoint (separated_disjoint hdR.2 heS.2).symm]
    omega
  have hmemE : e∈(actualSmallPrimeProduct N cap w).divisors := he
  have hmemD : d∈(roughProduct N cap w Z).divisors := hd
  have hmemZ : e*d∈(actualSmallPrimeProduct N cap Z).divisors := hmem
  by_cases hp : Even d.primeFactors.card
  · have hg := actual_upper_gates_even (L:=L) he hd hp
    simp only [roughWeight,residualSmallWeight,if_pos hp,
      actualSmallRosserPlus,ActualSmallRosserProvider.upperWeight,upperWeight_apply,
      hmemE,hmemD,hmemZ,true_and,hg,hcut,hcard,pow_add]
    exact redundant_cutoff_factor hredundant _ _
  · have hg := actual_upper_gates_odd (L:=L) he hd hp
    simp only [roughWeight,residualSmallWeight,if_neg hp,
      actualSmallRosserPlus,actualSmallRosserMinus,ActualSmallRosserProvider.upperWeight,
      ActualSmallRosserProvider.lowerWeight,upperWeight_apply,lowerWeight_apply,
      hmemE,hmemD,hmemZ,true_and,hg,hcut,hcard,pow_add]
    exact redundant_cutoff_factor hredundant _ _

theorem residualSmallWeight_eq_zero_of_not_mem {N cap d e : ℕ} {w L : ℝ}
    (he : e∉actualSmallRosserSupport N cap w) : residualSmallWeight N cap w L d e=0 := by
  unfold residualSmallWeight
  split_ifs
  · by_contra h
    exact he (actualSmallRosserPlus_active h).1
  · by_contra h
    exact he (actualSmallRosserMinus_active h).1

theorem roughWeight_eq_zero_of_not_mem {N cap d : ℕ} {w Z L : ℝ}
    (hd : d∉roughSupport N cap w Z) : roughWeight N cap w Z L d=0 := by
  by_contra h
  exact hd (upperWeight_active h).1

/-- Full separated arithmetic-function identity. Neither finite support,
squarefreeness nor coefficient nonvanishing is an input. In particular a
forbidden prime, an omitted cap prime or a repeated power gives zero on
both sides by the proved support equivalence. -/
theorem native_upper_residual_factor {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w≤Z) (he : SmallPrimeSupportedAt w e) (hd : RoughPrimeSupportedAt w d) :
    actualSmallRosserPlus N cap Z L (e*d)=
      roughWeight N cap w Z L d * residualSmallWeight N cap w L d e := by
  by_cases heM : e∈actualSmallRosserSupport N cap w
  · by_cases hdM : d∈roughSupport N cap w Z
    · exact native_upper_residual_factor_on_support hwZ heM hdM
    · have hz : actualSmallRosserPlus N cap Z L (e*d)=0 := by
        by_contra h
        exact hdM ((separated_support_iff hwZ he hd).mp (actualSmallRosserPlus_active h).1).2
      rw [hz,roughWeight_eq_zero_of_not_mem hdM,zero_mul]
  · have hz : actualSmallRosserPlus N cap Z L (e*d)=0 := by
      by_contra h
      exact heM ((separated_support_iff hwZ he hd).mp (actualSmallRosserPlus_active h).1).1
    rw [hz,residualSmallWeight_eq_zero_of_not_mem heM,mul_zero]

/-- Literal arithmetic functions vanish at zero, even when the level is
nonpositive. Hence zero factors require no artificial positivity premise. -/
theorem native_upper_residual_factor_zero_left (N cap d : ℕ) (w Z L : ℝ) :
    actualSmallRosserPlus N cap Z L (0*d)=
      roughWeight N cap w Z L d * residualSmallWeight N cap w L d 0 := by
  simp [residualSmallWeight,actualSmallRosserPlus,actualSmallRosserMinus]

theorem native_upper_residual_factor_zero_right (N cap e : ℕ) (w Z L : ℝ) :
    actualSmallRosserPlus N cap Z L (e*0)=
      roughWeight N cap w Z L 0 * residualSmallWeight N cap w L 0 e := by
  simp [roughWeight,actualSmallRosserPlus]

/-- One total statement includes either zero factor as well as every
cutoff-separated nonzero pair. The arithmetic functions retain all zeros. -/
theorem native_upper_residual_factor_total {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w≤Z) (he : e=0 ∨ SmallPrimeSupportedAt w e)
    (hd : d=0 ∨ RoughPrimeSupportedAt w d) :
    actualSmallRosserPlus N cap Z L (e*d)=
      roughWeight N cap w Z L d * residualSmallWeight N cap w L d e := by
  rcases he with rfl|he
  · exact native_upper_residual_factor_zero_left N cap d w Z L
  rcases hd with rfl|hd
  · exact native_upper_residual_factor_zero_right N cap e w Z L
  exact native_upper_residual_factor hwZ he hd

end
end ImbalancedChen.P5Z.OriginalOrdinaryResidualArithmeticFactor
