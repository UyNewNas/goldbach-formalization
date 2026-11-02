import ImbalancedChen.Part3OriginalActualFrozenSmoothPackets
import ImbalancedChen.Part3OriginalGevreyPreliminaryE2Partition
import ImbalancedChen.Part3ComplexDispersion
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.

This is a source-connected first Cauchy step for the actual H frozen
packet. The integer f is signed; q*d is cancelled inside the inverse,
and the original q*w1*w2 denominator is factored, not changed. All
endpoint, factor-fibre and clean restrictions remain inside row fibres.
In particular these rows are NOT asserted equal to the production
unrestricted reciprocal row: the arithmetic-mask removal is still open.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102

attribute [local instance] Classical.propDecidable

/-- The quotient is taken on the original signed difference, never its
natAbs. Its divisibility is proved from the actual clean congruence. -/
def signedF (B : FixedBlock) (t : Index) : ℤ :=
  ((t.n1 : ℤ) - t.n2) / ((t.q * B.d : ℕ) : ℤ)

theorem signedF_mul (B : FixedBlock) {t : Index} (ht : t ∈ B.carrier) :
    ((t.q * B.d : ℕ) : ℤ) * signedF B t = (t.n1 : ℤ) - t.n2 := by
  have hc := (Finset.mem_filter.mp ht).2
  obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := hc
  exact Int.mul_ediv_cancel' (Int.natCast_modEq_iff.mpr hmod).symm.dvd

/-- n1 is forced by the original q,n2 and SIGNED quotient. Thus
recording n1 in an outer label does not introduce an extra free index. -/
theorem signedF_reconstruct_n1 (B : FixedBlock) {t : Index}
    (ht : t ∈ B.carrier) :
    (((t.n2 : ℤ) + ((t.q*B.d : ℕ) : ℤ)*signedF B t).toNat) = t.n1 := by
  have he : (t.n2 : ℤ) + ((t.q*B.d : ℕ) : ℤ)*signedF B t = (t.n1 : ℤ) := by
    rw [signedF_mul B ht]
    omega
  rw [he]
  simp

theorem signedF_forces_n1 (B : FixedBlock) {t t' : Index}
    (ht : t ∈ B.carrier) (ht' : t' ∈ B.carrier)
    (hq : t.q = t'.q) (hn2 : t.n2 = t'.n2)
    (hf : signedF B t = signedF B t') : t.n1 = t'.n1 := by
  rw [← signedF_reconstruct_n1 B ht, ← signedF_reconstruct_n1 B ht', hq, hn2, hf]

theorem signedF_ne_zero (B : FixedBlock) (hx : 1 < B.x)
    {t : Index} (ht : t ∈ B.carrier) : signedF B t ≠ 0 := by
  intro hf
  have he := signedF_mul B ht
  rw [hf, mul_zero] at he
  have hn : t.n1 = t.n2 := by exact_mod_cast (sub_eq_zero.mp he.symm)
  have hc := (Finset.mem_filter.mp ht).2
  obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := hc
  have hp : 0 < B.atom.U / Real.log B.x ^ B.separationOrder :=
    div_pos B.U_pos (pow_pos (Real.log_pos hx) _)
  rw [hn, sub_self, Int.natAbs_zero, Nat.cast_zero] at hsep
  exact (not_le_of_gt hp) hsep

private theorem alpha_bounds (B : FixedBlock) {n : ℕ}
    (hn : n ∈ B.atom.alphaCarrier) : B.atom.U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*B.atom.U := by
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1),
    (show (n : ℝ) ≤ (Nat.floor (2*B.atom.U) : ℝ) by exact_mod_cast hi.2).trans
      (Nat.floor_le (by positivity))⟩

/-- The tight original f support, before any enlargement after Cauchy.
There is no +1, absolute-value reindexing or q -> q*d substitution. -/
theorem signedF_original_bound (B : FixedBlock) {t : Index}
    (ht : t ∈ B.carrier) :
    |(signedF B t : ℝ)| * ((t.q * B.d : ℕ) : ℝ) ≤ B.atom.U := by
  obtain ⟨hn1, hn2⟩ := carrier_n_support B ht
  have h1 := alpha_bounds B hn1
  have h2 := alpha_bounds B hn2
  have he : ((t.q * B.d : ℕ) : ℝ) * (signedF B t : ℝ) =
      (t.n1 : ℝ) - t.n2 := by exact_mod_cast signedF_mul B ht
  have hdiff : |(t.n1 : ℝ) - t.n2| ≤ B.atom.U :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [← he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at hdiff
  simpa only [mul_comm] using hdiff

/-- Cancelling a common multiplicative factor in a licensed inverse.
Both inverse congruences are used; this does not divide congruences by
a possibly nonunit. The statement also includes modulus one. -/
private theorem inverse_cancel (m delta n : ℕ)
    (hfull : (delta*n).Coprime m) :
    Int.ModEq m
      ((delta : ℤ) * CanonicalReciprocalPhase.wPhaseInverse (delta*n) m)
      (CanonicalReciprocalPhase.wPhaseInverse n m) := by
  have hn : n.Coprime m := hfull.of_dvd_left (dvd_mul_left delta n)
  have hf := CanonicalReciprocalPhase.wPhaseInverse_spec hfull
  have hr := CanonicalReciprocalPhase.wPhaseInverse_spec hn
  calc
    _ ≡ ((delta : ℤ) * CanonicalReciprocalPhase.wPhaseInverse (delta*n) m) *
        ((n : ℤ) * CanonicalReciprocalPhase.wPhaseInverse n m) [ZMOD m] := by
      simpa only [mul_one] using (hr.mul_left
        ((delta : ℤ) * CanonicalReciprocalPhase.wPhaseInverse (delta*n) m)).symm
    _ = CanonicalReciprocalPhase.wPhaseInverse n m *
        (((delta*n : ℕ) : ℤ) * CanonicalReciprocalPhase.wPhaseInverse (delta*n) m) := by
      push_cast
      ring
    _ ≡ CanonicalReciprocalPhase.wPhaseInverse n m [ZMOD m] := by
      simpa only [mul_one] using hf.mul_left (CanonicalReciprocalPhase.wPhaseInverse n m)

/-- The actual original first phase, with q*d really cancelled using
the clean congruence. The denominator remains n1*w2. -/
theorem firstPhase_eq_signed_reciprocal (B : FixedBlock) {t : Index}
    (ht : t ∈ B.carrier) :
    B.firstPhase t =
      fourier (B.atom.residue*t.h*signedF B t)
        (((CanonicalReciprocalPhase.wPhaseInverse (t.n2*t.w1) (t.n1*t.w2) : ℝ) /
          ((t.n1*t.w2 : ℕ) : ℝ) : ℝ) : UnitAddCircle) := by
  have hc := (Finset.mem_filter.mp ht).2
  have hfull : ((t.q*B.d)*(t.n2*t.w1)).Coprime (t.n1*t.w2) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using (E3_clean_inverse_licenses hc).2.2
  have hi := inverse_cancel (t.n1*t.w2) (t.q*B.d) (t.n2*t.w1) hfull
  have hmod : Int.ModEq (t.n1*t.w2)
      (B.atom.residue*((t.n1 : ℤ)-t.n2)*
        CanonicalReciprocalPhase.wPhaseInverse (t.n2*t.q*B.d*t.w1) (t.n1*t.w2))
      (B.atom.residue*signedF B t*
        CanonicalReciprocalPhase.wPhaseInverse (t.n2*t.w1) (t.n1*t.w2)) := by
    have hh := hi.mul_left (B.atom.residue*signedF B t)
    rw [← signedF_mul B ht]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hn1 := (alpha_bounds B (carrier_n_support B ht).1).1
  have hn1pos : 0 < t.n1 := by
    have : (0 : ℝ) < t.n1 := B.U_pos.trans_le hn1
    exact_mod_cast this
  have hw2 : t.w2 ∈ B.wCarrier := by
    have hr := (Finset.mem_filter.mp ht).1
    obtain ⟨q, hq, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨w1, hw1, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨w2, hw2, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨n1, hn1, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨n2, hn2, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨h, hh, he⟩ := Finset.mem_image.mp hr
    cases he
    exact hw2
  have hw2pos : 0 < t.w2 :=
    (Nat.ceil_pos.mpr B.rough_pos).trans_le (Finset.mem_Icc.mp hw2).1
  have hcircle := CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq
    (Nat.mul_pos hn1pos hw2pos) hmod
  rw [actual_E3_firstPhase_eq_canonical ht, congrArg (fourier t.h) hcircle]
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  ring

abbrev Source := Index × (Factor × Factor)

/-- A complete, literal flattening of one H frozen upper packet. -/
def sourceCarrier (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ) : Finset Source :=
  ((B.carrier.filter R.contains) ×ˢ
    (choicesWithoutProductWindow atom z y k small ×ˢ
      choicesWithoutProductWindow atom z y k small)).filter (fun s =>
        s.1.w1 ≤ Br ∧ s.1.w2 ≤ Bs ∧
        s.2.1.u*s.2.1.v = s.1.w1 ∧ s.2.2.u*s.2.2.v = s.1.w2 ∧
        smoothTag s.2.1 = st ∧ smoothTag s.2.2 = st')

theorem frozenUpperPacket_eq_source (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    frozenUpperPacket B atom z y k small R Br Bs st st' e f g =
      ∑ s ∈ sourceCarrier B atom z y k small R Br Bs st st',
        frozenDiagonal atom st st' s.1 s.2.1 s.2.2 e f g * physicalKernel B s.1 := by
  unfold frozenUpperPacket sourceCarrier smoothFibre productFibre
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hR : R.contains t
  · simp only [if_pos hR]
    by_cases hcut : t.w1 ≤ Br ∧ t.w2 ≤ Bs
    · rw [if_pos hcut]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpw : p.u*p.v = t.w1
      · by_cases hpt : smoothTag p = st
        · simp only [if_pos hpw, if_pos hpt]
          apply Finset.sum_congr rfl
          intro p' hp'
          by_cases hpw' : p'.u*p'.v = t.w2 <;>
            by_cases hpt' : smoothTag p' = st' <;>
            simp [hcut.1, hcut.2, hpw, hpt, hpw', hpt']
        · simp [hcut.1, hcut.2, hpw, hpt]
      · simp [hcut.1, hcut.2, hpw]
    · rcases not_and_or.mp hcut with h1 | h2
      · simp [h1]
      · simp [h2]
  · simp [hR]

/-- Freeze precisely the variables outside the S/h row. f remains
redundantly recorded, so its sign and original ownership cannot disappear. -/
structure Outer where
  q n1 n2 r1 s2 r2 : ℕ
  f : ℤ
  deriving DecidableEq

def outer (B : FixedBlock) (s : Source) : Outer :=
  ⟨s.1.q, s.1.n1, s.1.n2, s.2.1.v, s.2.2.u, s.2.2.v, signedF B s.1⟩

def lambdaS (atom : MediumAtom) (st st' : ℕ × ℕ) (e : Fin 4) : ℕ → ℂ :=
  diagonal (gamma2Slot atom st.1) (gamma2Slot atom st'.1) e

def lambdaR (atom : MediumAtom) (st st' : ℕ × ℕ) (f : Fin 4) : ℕ → ℂ :=
  diagonal (gamma3Slot atom st.2) (gamma3Slot atom st'.2) f

def lambdaN (atom : MediumAtom) (g : Fin 4) : ℕ → ℂ :=
  diagonal (alphaSlot atom) (alphaSlot atom) g

def outerCoefficient (atom : MediumAtom) (st st' : ℕ × ℕ)
    (e f g : Fin 4) (o : Outer) : ℂ :=
  (star (lambdaS atom st st' e o.s2) *
    (lambdaR atom st st' f o.r1 * star (lambdaR atom st st' f o.r2)) *
    (lambdaN atom g o.n1 * star (lambdaN atom g o.n2))) /
      ((o.q*o.r1*o.s2*o.r2 : ℕ) : ℂ)

/-- The original b,c substitution. No inverse uses q*d after cancellation. -/
def packetB (o : Outer) : ℕ := o.n2*o.r1
def packetC (o : Outer) : ℕ := o.n1*o.r2*o.s2

def rowAtom (B : FixedBlock) (atom : MediumAtom) (st st' : ℕ × ℕ)
    (e : Fin 4) (s : Source) : ℂ :=
  (lambdaS atom st st' e s.2.1.u / (s.2.1.u : ℂ)) *
    ActualReciprocalSquarePoissonSourceOnly.phase B.atom.residue (signedF B s.1)
      (packetB (outer B s)) (packetC (outer B s)) (s.2.1.u, s.1.h)

/-- Exact pointwise source factorization. The only hypotheses here are
literal membership facts from the already defined original source. -/
theorem sourceTerm_eq_outer_mul_rowAtom (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) {s : Source}
    (hs : s ∈ sourceCarrier B atom z y k small R Br Bs st st') :
    frozenDiagonal atom st st' s.1 s.2.1 s.2.2 e f g * physicalKernel B s.1 =
      outerCoefficient atom st st' e f g (outer B s) * rowAtom B atom st st' e s := by
  have hmem := Finset.mem_filter.mp hs
  have ht := (Finset.mem_filter.mp (Finset.mem_product.mp hmem.1).1).1
  have hprod1 := hmem.2.2.2.1
  have hprod2 := hmem.2.2.2.2.1
  have hp := firstPhase_eq_signed_reciprocal B ht
  have hphase : B.firstPhase s.1 =
      ActualReciprocalSquarePoissonSourceOnly.phase B.atom.residue (signedF B s.1)
        (packetB (outer B s)) (packetC (outer B s)) (s.2.1.u, s.1.h) := by
    rw [hp]
    unfold ActualReciprocalSquarePoissonSourceOnly.phase packetB packetC outer
    dsimp only
    rw [← hprod1, ← hprod2]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  unfold physicalKernel
  rw [hphase]
  unfold frozenDiagonal diagonalProduct outerCoefficient rowAtom
    lambdaS lambdaR lambdaN packetB packetC outer
  dsimp only
  rw [← hprod1, ← hprod2]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

def row (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) : ℂ :=
  ∑ s ∈ (sourceCarrier B atom z y k small R Br Bs st st').filter
      (fun s => outer B s = o), rowAtom B atom st st' e s

/-- Original H packet -> actual reciprocal rows, with exact fibre
multiplicity. No source-equality premise or unrestricted-row replacement. -/
theorem frozenUpperPacket_eq_rows (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    frozenUpperPacket B atom z y k small R Br Bs st st' e f g =
      ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
        outerCoefficient atom st st' e f g o *
          row B atom z y k small R Br Bs st st' e o := by
  rw [frozenUpperPacket_eq_source]
  let U := sourceCarrier B atom z y k small R Br Bs st st'
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := U) (t := U.image (outer B)) (g := outer B)
    (fun s hs => Finset.mem_image_of_mem _ hs)
    (fun s => frozenDiagonal atom st st' s.1 s.2.1 s.2.2 e f g * physicalKernel B s.1)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro o ho
  unfold row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hU := (Finset.mem_filter.mp hs).1
  have hout := (Finset.mem_filter.mp hs).2
  rw [sourceTerm_eq_outer_mul_rowAtom B atom z y k small R Br Bs st st' e f g hU,
    hout]

/-- The actual positive Cauchy inequality, before f/support enlargement
or arithmetic-mask removal. The energy and rows are constructed from H. -/
theorem frozenUpperPacket_positive_Cauchy (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖^2 ≤
      (∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
        ‖outerCoefficient atom st st' e f g o‖^2) *
      ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
        ‖row B atom z y k small R Br Bs st st' e o‖^2 := by
  rw [frozenUpperPacket_eq_rows]
  exact complex_finset_cauchy_norm_sq _ _ _

end ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
