import ImbalancedChen.Part3ActualCompletedSquarePushforward
import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity

/-!
SOURCEONLY / UNCOMPILED. Actual closed t is split BEFORE its square.
Each remaining signed upper-f fibre is mapped explicitly into the owned
positive-f, half-open equal-S count carrier, preserving the JOINT output.
The first section reuses old716a L12-234 with one proven positivity fix;
no old Original23CountBeta / FrozenKernel hypothesis adapter is imported.
-/
namespace ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff
open ActualPositiveLatticeSmoothCoverSourceOnly ActualReciprocalSquarePoissonSourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- n depends only on the original fixed feature S, never on b,c,f,m,nu. -/
def ceilIndex (S : ℝ) : ℕ := Nat.ceil S

def tChart (S : ℝ) (upper : Bool) : Finset ℕ :=
  (factorCarrier S).filter (fun t =>
    if upper then 2*ceilIndex S ≤ t else t < 2*ceilIndex S)

def countScaleNat (S : ℝ) (upper : Bool) : ℕ :=
  if upper then 2*ceilIndex S else ceilIndex S

def countScale (S : ℝ) (upper : Bool) : ℝ := countScaleNat S upper

theorem ceilIndex_pos {S : ℝ} (hS : 0 < S) : 0 < ceilIndex S := by
  have hc : S ≤ (ceilIndex S:ℝ) := Nat.le_ceil S
  by_contra hn
  have he : ceilIndex S = 0 := Nat.eq_zero_of_not_pos hn
  rw [he,Nat.cast_zero] at hc
  linarith

theorem countScale_ge_one {S : ℝ} (hS : 0 < S) (upper : Bool) :
    1 ≤ countScale S upper := by
  have hn := ceilIndex_pos hS
  cases upper with
  | false =>
      change (1:ℝ) ≤ (ceilIndex S:ℝ)
      exact_mod_cast (show 1 ≤ ceilIndex S from hn)
  | true =>
      change (1:ℝ) ≤ ((2*ceilIndex S:ℕ):ℝ)
      exact_mod_cast (show 1 ≤ 2*ceilIndex S by omega)

/-- Only actual source labels are partitioned: no new t is inserted. -/
theorem tChart_partition (S : ℝ) :
    factorCarrier S = tChart S false ∪ tChart S true := by
  ext t
  simp only [tChart,Bool.false_eq_true,if_false,if_true,mem_union,mem_filter]
  constructor
  · intro ht
    rcases lt_or_ge t (2*ceilIndex S) with h | h
    · exact Or.inl ⟨ht,h⟩
    · exact Or.inr ⟨ht,h⟩
  · rintro (⟨ht,h⟩ | ⟨ht,h⟩) <;> exact ht

theorem tChart_disjoint (S : ℝ) : Disjoint (tChart S false) (tChart S true) := by
  apply disjoint_left.mpr
  intro t ht hu
  have hlo : t < 2*ceilIndex S := (mem_filter.mp ht).2
  have hhi : 2*ceilIndex S ≤ t := (mem_filter.mp hu).2
  omega

/-- The upper chart is at most ONE endpoint, not a larger dyadic box. -/
theorem upper_chart_mem {S : ℝ} (hS : 0 < S) {t : ℕ} (ht : t ∈ tChart S true) :
    t = 2*ceilIndex S := by
  obtain ⟨ht,hlo⟩ := mem_filter.mp ht
  change 2*ceilIndex S ≤ t at hlo
  have hhi : t ≤ Nat.floor (2*S) := (mem_Icc.mp ht).2
  have hS0 : 0 ≤ S := hS.le
  have htR : (t:ℝ) ≤ 2*S :=
    (by exact_mod_cast hhi : (t:ℝ) ≤ (Nat.floor (2*S):ℝ)).trans
      (Nat.floor_le (by positivity))
  have hn : S ≤ (ceilIndex S:ℝ) := Nat.le_ceil S
  have hupper : t ≤ 2*ceilIndex S := by exact_mod_cast (show (t:ℝ) ≤ 2*(ceilIndex S:ℝ) by linarith)
  exact Nat.le_antisymm hupper hlo

/-- In particular the endpoint chart vanishes when S is not an integer. -/
theorem upper_chart_empty_of_lt_ceil {S : ℝ} (hSp : 0 < S)
    (hS : S < (ceilIndex S:ℝ)) :
    tChart S true = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have he := upper_chart_mem hSp ht
  have hhi := (mem_Icc.mp (mem_filter.mp ht).1).2
  have hT : (t:ℝ) ≤ 2*S := (by exact_mod_cast hhi : (t:ℝ) ≤ (Nat.floor (2*S):ℝ)).trans
    (Nat.floor_le (by linarith))
  have heR : (t:ℝ) = 2*(ceilIndex S:ℝ) := by exact_mod_cast he
  linarith

/-- The full small-S range is now covered, even though the OLD sharp
supplier assumes its OWN count scale is at least one. -/
theorem small_scale_charts {S : ℝ} (hS : 0 < S) (hS1 : S < 1) :
    ceilIndex S = 1 ∧ tChart S true = ∅ ∧ tChart S false = factorCarrier S := by
  have hn0 := ceilIndex_pos hS
  have hn1 : ceilIndex S ≤ 1 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_one] using hS1.le
  have hn : ceilIndex S = 1 := by omega
  have he : tChart S true = ∅ := upper_chart_empty_of_lt_ceil hS (by simpa only [hn,Nat.cast_one] using hS1)
  refine ⟨hn,he,?_⟩
  have hp := tChart_partition S
  rw [he,union_empty] at hp
  exact hp.symm

/-- No change in the actual signed h window is hidden in the count carrier. -/
theorem old_frequencyCarrier_nat (H : ℕ) :
    LichtmanSignedDifferenceMultiplicity.frequencyCarrier (H:ℝ) =
      poissonNonzeroFrequencyWindow H := by
  simp only [LichtmanSignedDifferenceMultiplicity.frequencyCarrier,
    poissonNonzeroFrequencyWindow,Nat.floor_natCast]
private theorem closed_factor_bounds {S : ℝ} (hS : 0 < S) {t : ℕ}
    (ht : t ∈ factorCarrier S) : 0 < t ∧ S ≤ (t:ℝ) ∧ (t:ℝ) ≤ 2*S := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp ht
  have hp : 0 < Nat.ceil S := Nat.ceil_pos.mpr hS
  exact ⟨by omega,(Nat.le_ceil S).trans (by exact_mod_cast hlo),
    (show (t:ℝ) ≤ (Nat.floor (2*S):ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by positivity))⟩
/-- Both true charts embed into one of the OLD half-open count carriers.
The physical output z=t1*t2 and its original S-based support are unchanged. -/
theorem tChart_subset_old {S : ℝ} (hS : 0 < S) (upper : Bool) :
    tChart S upper ⊆ LichtmanSignedDifferenceMultiplicity.dyadicCarrier (countScale S upper) := by
  intro t ht
  have hpos : 0 < t := (closed_factor_bounds hS (mem_filter.mp ht).1).1
  apply mem_filter.mpr
  refine ⟨mem_Ioc.mpr ⟨hpos,?_⟩,?_,?_⟩
  · apply Nat.le_floor
    cases upper with
    | false =>
        have hh : t < 2*ceilIndex S := (mem_filter.mp ht).2
        change (t:ℝ) ≤ 2*(ceilIndex S:ℝ)
        exact_mod_cast hh.le
    | true =>
        have he := upper_chart_mem hS ht
        change (t:ℝ) ≤ 2*((2*ceilIndex S:ℕ):ℝ)
        rw [he]
        have hnonneg : (0 : ℝ) ≤ ((2*ceilIndex S : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
  · cases upper with
    | false =>
        have hh : ceilIndex S ≤ t := (mem_Icc.mp (mem_filter.mp ht).1).1
        change (ceilIndex S:ℝ) ≤ (t:ℝ)
        exact_mod_cast hh
    | true =>
        have he := upper_chart_mem hS ht
        change ((2*ceilIndex S:ℕ):ℝ) ≤ t
        exact_mod_cast he.ge
  · cases upper with
    | false =>
        have hh : t < 2*ceilIndex S := (mem_filter.mp ht).2
        change (t:ℝ) < 2*(ceilIndex S:ℝ)
        exact_mod_cast hh
    | true =>
        have he := upper_chart_mem hS ht
        have hn := ceilIndex_pos hS
        change (t:ℝ) < 2*((2*ceilIndex S:ℕ):ℝ)
        rw [he]
        exact_mod_cast (show 2*ceilIndex S < 2*(2*ceilIndex S) by omega)

/-- The count scale differs by only an absolute factor on the actual S>=1/2
range. It is an auxiliary counting scale, NOT a replacement physical Z or rho. -/
theorem countScale_le_six {S : ℝ} (hS : (1:ℝ)/2 ≤ S) (upper : Bool) :
    countScale S upper ≤ 6*S := by
  have hS0 : 0 ≤ S := by linarith
  have hn : (ceilIndex S:ℝ) < S+1 := Nat.ceil_lt_add_one hS0
  cases upper with
  | false =>
      change (ceilIndex S:ℝ) ≤ 6*S
      linarith
  | true =>
      change ((2*ceilIndex S:ℕ):ℝ) ≤ 6*S
      push_cast
      linarith

/-- Exact original reciprocal row split, before taking any norm. Every
fixed lambda/omega, both unit gates, f and full signed H remain identical. -/
theorem finiteRow_closed_split (A : ℕ) (a : ℤ) (S : ℝ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) :
    finiteReciprocalRow A a (factorCarrier S) H lambda omega k =
      finiteReciprocalRow A a (tChart S false) H lambda omega k+
      finiteReciprocalRow A a (tChart S true) H lambda omega k := by
  unfold finiteReciprocalRow
  rw [tChart_partition S,sum_union (tChart_disjoint S)]

theorem complex_two_piece_sq (u v : ℂ) :
    ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 2
  have hs := sq_nonneg (‖u‖-‖v‖)
  nlinarith

/-- The only new Cauchy payment is this visible factor TWO. -/
theorem finiteRow_closed_square (A : ℕ) (a : ℤ) (S : ℝ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) :
    ‖finiteReciprocalRow A a (factorCarrier S) H lambda omega k‖^2 ≤
      2*‖finiteReciprocalRow A a (tChart S false) H lambda omega k‖^2+
      2*‖finiteReciprocalRow A a (tChart S true) H lambda omega k‖^2 := by
  rw [finiteRow_closed_split]
  exact complex_two_piece_sq _ _

/-- Actual six positive smooth pieces: same b,c,f lattice, same psi,
no additional factor six, no new spectral m, and no mutation of rho. -/
theorem sixSmoothMass_closed_split (A : ℕ) (a : ℤ) (S : ℝ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (B C : ℝ) (L : Finset Packet) :
    sixSmoothMass B C L (finiteReciprocalRow A a (factorCarrier S) H lambda omega) ≤
      2*sixSmoothMass B C L (finiteReciprocalRow A a (tChart S false) H lambda omega)+
      2*sixSmoothMass B C L (finiteReciprocalRow A a (tChart S true) H lambda omega) := by
  rw [← cover_mass_eq_six,← cover_mass_eq_six,← cover_mass_eq_six]
  calc
    _ ≤ ∑ k ∈ L,packetWeight B C k*
        (2*‖finiteReciprocalRow A a (tChart S false) H lambda omega k‖^2+
         2*‖finiteReciprocalRow A a (tChart S true) H lambda omega k‖^2) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (finiteRow_closed_square A a S H lambda omega k) (packetWeight_nonneg B C k))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Actual quotient feature: no assumed dyadic identity for the t carrier. -/
theorem actual_base_sixSmoothMass_closed_split (e : MediumAtom) (hQ2 : 0 ≤ e.Q2)
    {q : ℕ} (hq : 0 < q) (A : ℕ) (a : ℤ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (B C : ℝ) (L : Finset Packet) :
    sixSmoothMass B C L (finiteReciprocalRow A a
      (ActualSeparatedRowPacketMatchSourceOnly.baseCarrier e q) H lambda omega) ≤
      2*sixSmoothMass B C L (finiteReciprocalRow A a (tChart (e.Q2/(q:ℝ)) false) H lambda omega)+
      2*sixSmoothMass B C L (finiteReciprocalRow A a (tChart (e.Q2/(q:ℝ)) true) H lambda omega) := by
  rw [ActualSeparatedRowPacketMatchSourceOnly.baseCarrier_eq_factorCarrier_div e hQ2 hq]
  exact sixSmoothMass_closed_split A a _ H lambda omega B C L

/-- Exact H=0 boundary; it is not fed to the H>=1 sharp count supplier. -/
theorem finiteRow_height_zero (A : ℕ) (a : ℤ) (T : Finset ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) :
    finiteReciprocalRow A a T 0 lambda omega k = 0 := by
  have he : (Icc 1 (0:ℕ)) = ∅ := Icc_eq_empty_of_lt (by omega)
  simp only [finiteReciprocalRow,poissonNonzeroFrequencyWindow,he,
    image_empty,union_empty,sum_empty,mul_zero,ite_self,sum_const_zero]

/- The next stage splits only signed f, AFTER the t-row split above. -/
abbrev CountSource := (ℕ × ℕ × ℕ) × (ℤ × ℤ)

def fKey (s : Source) : ℕ × Bool := (Nat.log 2 s.1.natAbs, decide (s.1 < 0))

def upperSource (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool) (H : ℕ) (F : ℝ) :
    Finset Source :=
  nonzeroSource (carrier A a (tChart S upper) H (Icc (Int.ceil (-F)) (Int.floor F)))

def fBlock (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool) (H : ℕ) (F : ℝ)
    (j : ℕ × Bool) : Finset Source :=
  (upperSource A a S upper H F).filter (fun s => fKey s = j)

/-- The chart retains only original labels. Together with the owned
baseCarrier equality this lets actual gamma/log norm suppliers be reused. -/
theorem fBlock_subset_fullSource (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) (j : ℕ × Bool) :
    fBlock A a S upper H F j ⊆
      nonzeroSource (carrier A a (factorCarrier S) H
        (Icc (Int.ceil (-F)) (Int.floor F))) := by
  intro s hs
  obtain ⟨hU,_⟩ := mem_filter.mp hs
  obtain ⟨hc,hy⟩ := mem_filter.mp hU
  obtain ⟨hr,hgate⟩ := mem_filter.mp hc
  obtain ⟨hf,hpair⟩ := mem_product.mp hr
  obtain ⟨h1,h2⟩ := mem_product.mp hpair
  obtain ⟨ht1,hh1⟩ := mem_product.mp h1
  obtain ⟨ht2,hh2⟩ := mem_product.mp h2
  exact mem_filter.mpr ⟨mem_filter.mpr
    ⟨mem_product.mpr ⟨hf,mem_product.mpr
      ⟨mem_product.mpr ⟨(mem_filter.mp ht1).1,hh1⟩,
       mem_product.mpr ⟨(mem_filter.mp ht2).1,hh2⟩⟩⟩,hgate⟩,hy⟩

private theorem upperSource_f_data {A : ℕ} {a : ℤ} {S : ℝ} {upper : Bool}
    {H : ℕ} {F : ℝ} {s : Source} (hs : s ∈ upperSource A a S upper H F) :
    s.1 ≠ 0 ∧ (s.1.natAbs : ℝ) ≤ F := by
  have hc := (mem_filter.mp hs).1
  obtain ⟨hr,hgate⟩ := mem_filter.mp hc
  have hf := (mem_product.mp hr).1
  have hlo : -F ≤ (s.1 : ℝ) := (Int.le_ceil (-F)).trans
    (by exact_mod_cast (mem_Icc.mp hf).1)
  have hhi : (s.1 : ℝ) ≤ F :=
    (show (s.1 : ℝ) ≤ ((Int.floor F : ℤ) : ℝ) by
      exact_mod_cast (mem_Icc.mp hf).2).trans (Int.floor_le F)
  have habs : (s.1.natAbs : ℝ) = |(s.1 : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  exact ⟨hgate.1, by rw [habs]; exact abs_le.mpr ⟨hlo,hhi⟩⟩

/-- Includes negative F and the entire subunit upper-f boundary. -/
theorem upperSource_empty_of_F_lt_one {A : ℕ} {a : ℤ} {S : ℝ} {upper : Bool}
    {H : ℕ} {F : ℝ} (hF : F < 1) : upperSource A a S upper H F = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hf,hbound⟩ := upperSource_f_data hs
  have hn : 1 ≤ s.1.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hf)
  have hnR : (1 : ℝ) ≤ s.1.natAbs := by exact_mod_cast hn
  linarith

/-- Exact finite label budget. Recombination by unweighted Cauchy pays
at most this factor, not a hidden absolute constant independent of F. -/
theorem upper_f_label_card_le (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) :
    ((upperSource A a S upper H F).image fKey).card ≤
      2*(Nat.log 2 (Nat.floor F)+1) := by
  have hsub : (upperSource A a S upper H F).image fKey ⊆
      range (Nat.log 2 (Nat.floor F)+1) ×ˢ (univ : Finset Bool) := by
    intro j hj
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hj
    have hle := Nat.log_mono_right (b := 2) (Nat.le_floor (upperSource_f_data hs).2)
    exact mem_product.mpr ⟨mem_range.mpr (by change Nat.log 2 s.1.natAbs < _; omega),
      mem_univ _⟩
  have hc := card_le_card hsub
  simpa only [card_product, card_range, card_univ, Fintype.card_bool, Nat.mul_comm] using hc

def fScale (j : ℕ) : ℝ := ((2 : ℕ)^j : ℕ)

def twist (negative : Bool) (h : ℤ) : ℤ := if negative then -h else h

def toCount (negative : Bool) (s : Source) : CountSource :=
  ((s.2.2.1, s.2.1.1, s.1.natAbs), (twist negative s.2.1.2, twist negative s.2.2.2))

def fromCount (negative : Bool) (p : CountSource) : Source :=
  (twist negative (p.1.2.2 : ℤ),
    ((p.1.2.1, twist negative p.2.1), (p.1.1, twist negative p.2.2)))

private theorem twist_twice (negative : Bool) (h : ℤ) :
    twist negative (twist negative h) = h := by
  cases negative <;> simp [twist]

private theorem f_sign_from_key {s : Source} {j : ℕ × Bool} (hj : fKey s = j) :
    twist j.2 (s.1.natAbs : ℤ) = s.1 := by
  have hd : decide (s.1 < 0) = j.2 := congrArg Prod.snd hj
  rcases j with ⟨n,b⟩
  cases b with
  | false =>
      have hn : ¬s.1 < 0 := of_decide_eq_false hd
      simp only [twist, Bool.false_eq_true, if_false, Int.natCast_natAbs,
        abs_of_nonneg (le_of_not_gt hn)]
  | true =>
      have hn : s.1 < 0 := of_decide_eq_true hd
      simp only [twist, if_true, Int.natCast_natAbs, abs_of_neg hn, neg_neg]

theorem fromCount_toCount {s : Source} {j : ℕ × Bool} (hj : fKey s = j) :
    fromCount j.2 (toCount j.2 s) = s := by
  have hf := f_sign_from_key hj
  rcases s with ⟨f, ⟨t1,h1⟩, ⟨t2,h2⟩⟩
  change (twist j.2 (f.natAbs : ℤ),
    ((t1,twist j.2 (twist j.2 h1)), (t2,twist j.2 (twist j.2 h2)))) =
      (f,((t1,h1),(t2,h2)))
  rw [twist_twice,twist_twice]
  exact Prod.ext hf rfl

/-- Swapping t1,t2 AND reflecting both h for negative f preserves y,
not merely |y|. Thus every original nu|y test is preserved verbatim. -/
theorem toCount_output {s : Source} {j : ℕ × Bool} (hj : fKey s = j) :
    LichtmanSignedDifferenceMultiplicity.output (toCount j.2 s) = output s := by
  have hf := f_sign_from_key hj
  apply Prod.ext
  · exact Nat.mul_comm _ _
  · rcases j with ⟨n, negative⟩
    cases negative with
    | false =>
        change (s.1.natAbs : ℤ) *
          (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ)) =
          s.1 * (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ))
        have hf' : (s.1.natAbs : ℤ) = s.1 := hf
        exact congrArg (fun f : ℤ =>
          f * (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ))) hf'
    | true =>
        change (s.1.natAbs : ℤ) *
          ((-s.2.1.2) * (s.2.2.1 : ℤ) - (-s.2.2.2) * (s.2.1.1 : ℤ)) =
          s.1 * (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ))
        have hf' : -(s.1.natAbs : ℤ) = s.1 := hf
        calc
          _ = -(s.1.natAbs : ℤ) *
              (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ)) := by ring
          _ = _ := congrArg (fun f : ℤ =>
            f * (s.2.1.2 * (s.2.2.1 : ℤ) - s.2.2.2 * (s.2.1.1 : ℤ))) hf'

private theorem twist_mem_frequency (negative : Bool) {H : ℕ} {h : ℤ}
    (hh : h ∈ poissonNonzeroFrequencyWindow H) :
    twist negative h ∈ LichtmanSignedDifferenceMultiplicity.frequencyCarrier (H : ℝ) := by
  rw [old_frequencyCarrier_nat]
  cases negative with
  | false => exact hh
  | true =>
      change -h ∈ poissonNonzeroFrequencyWindow H
      rcases mem_union.mp hh with hh | hh
      · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
        exact mem_union.mpr (Or.inr (mem_image.mpr ⟨n,hn,rfl⟩))
      · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨n,hn,by simp⟩))

private theorem f_mem_dyadic {s : Source} {j : ℕ × Bool}
    (hf : s.1 ≠ 0) (hj : fKey s = j) :
    s.1.natAbs ∈ LichtmanSignedDifferenceMultiplicity.dyadicCarrier (fScale j.1) := by
  have hn : s.1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hf
  have hlog : Nat.log 2 s.1.natAbs = j.1 := congrArg Prod.fst hj
  have hlo : 2^j.1 ≤ s.1.natAbs := by
    simpa only [hlog] using Nat.pow_log_le_self 2 hn
  have hhi : s.1.natAbs < 2*2^j.1 := by
    simpa only [hlog, pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) s.1.natAbs
  have hloR : fScale j.1 ≤ (s.1.natAbs : ℝ) := by
    change (((2 : ℕ)^j.1 : ℕ) : ℝ) ≤ (s.1.natAbs : ℝ)
    exact_mod_cast hlo
  have hhiR : (s.1.natAbs : ℝ) < 2*fScale j.1 := by
    change (s.1.natAbs : ℝ) < 2*(((2 : ℕ)^j.1 : ℕ) : ℝ)
    exact_mod_cast hhi
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn, Nat.le_floor hhiR.le⟩,
    hloR, hhiR⟩

theorem nonempty_fScale_le_upper {A : ℕ} {a : ℤ} {S : ℝ} {upper : Bool}
    {H : ℕ} {F : ℝ} {j : ℕ × Bool} (hU : (fBlock A a S upper H F j).Nonempty) :
    fScale j.1 ≤ F := by
  obtain ⟨s,hs⟩ := hU
  obtain ⟨hsource,hkey⟩ := mem_filter.mp hs
  obtain ⟨hf,hbound⟩ := upperSource_f_data hsource
  exact ((mem_filter.mp (f_mem_dyadic hf hkey)).2.1).trans hbound

/-- Constructed from actual membership, not an assumed packet embedding.
The upper f cutoff and both fixed unit gates remain in fBlock; only the
positive counting envelope enlarges those filters away. -/
theorem fBlock_maps_to_count {A : ℕ} {a : ℤ} {S : ℝ} (hS : 0 < S)
    {upper : Bool} {H : ℕ} {F : ℝ} {j : ℕ × Bool} {s : Source}
    (hs : s ∈ fBlock A a S upper H F j) :
    toCount j.2 s ∈ LichtmanSignedDifferenceMultiplicity.sourceCarrier
      (countScale S upper) (H : ℝ) (fScale j.1) := by
  obtain ⟨hU,hkey⟩ := mem_filter.mp hs
  obtain ⟨hc,hy⟩ := mem_filter.mp hU
  obtain ⟨hr,hgate⟩ := mem_filter.mp hc
  have hp := mem_product.mp (mem_product.mp hr).2
  have ht1 := (mem_product.mp hp.1).1
  have ht2 := (mem_product.mp hp.2).1
  have hh1 := (mem_product.mp hp.1).2
  have hh2 := (mem_product.mp hp.2).2
  have hk : LichtmanSignedDifferenceMultiplicity.difference (toCount j.2 s) ≠ 0 := by
    intro hz
    have hout := congrArg Prod.snd (toCount_output hkey)
    have hout0 : (output s).2 = 0 := by
      rw [← hout]
      simp only [LichtmanSignedDifferenceMultiplicity.output, hz, mul_zero]
    exact hy hout0
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_product.mpr
    ⟨tChart_subset_old hS upper ht2,
      mem_product.mpr ⟨tChart_subset_old hS upper ht1, f_mem_dyadic hgate.1 hkey⟩⟩,
    mem_product.mpr ⟨twist_mem_frequency j.2 hh1, twist_mem_frequency j.2 hh2⟩⟩,hk⟩

/-- One sign/dyadic-f chart is injective, so its count has cost ONE.
The factor for combining different sign/f charts must be paid separately. -/
theorem fBlock_fiber_card_le {A : ℕ} {a : ℤ} {S : ℝ} (hS : 0 < S)
    (upper : Bool) (H : ℕ) (F : ℝ) (j : ℕ × Bool) (zy : Output) :
    (fiber (fBlock A a S upper H F j) zy).card ≤
      LichtmanSignedDifferenceMultiplicity.multiplicity
        (countScale S upper) (H : ℝ) (fScale j.1) zy.1 zy.2 := by
  unfold LichtmanSignedDifferenceMultiplicity.multiplicity
  apply card_le_card_of_injOn (toCount j.2)
  · intro s hs
    obtain ⟨hs,hy⟩ := mem_filter.mp hs
    exact mem_filter.mpr ⟨fBlock_maps_to_count hS hs,
      (toCount_output (mem_filter.mp hs).2).trans hy⟩
  · intro s hs t ht heq
    have hskey := (mem_filter.mp (mem_filter.mp hs).1).2
    have htkey := (mem_filter.mp (mem_filter.mp ht).1).2
    have heq' := congrArg (fromCount j.2) heq
    simpa only [fromCount_toCount hskey, fromCount_toCount htkey] using heq'

def chartCountEnergy (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool) (H : ℕ)
    (F : ℝ) (j : ℕ × Bool) (nu : ℕ) : ℝ :=
  let U := fBlock A a S upper H F j
  ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then ((fiber U zy).card : ℝ)^2 else 0

theorem chartCountEnergy_le_owned {A : ℕ} {a : ℤ} {S : ℝ} (hS : 0 < S)
    (upper : Bool) (H : ℕ) (F : ℝ) (j : ℕ × Bool) (nu : ℕ) :
    chartCountEnergy A a S upper H F j nu ≤
      LichtmanSignedDifferenceMultiplicity.multiplicityL2
        (countScale S upper) (H : ℝ) (fScale j.1) nu := by
  let U := fBlock A a S upper H F j
  let P := LichtmanSignedDifferenceMultiplicity.sourceCarrier
    (countScale S upper) (H : ℝ) (fScale j.1)
  let W (zy : Output) : ℝ := if (nu : ℤ) ∣ zy.2 then
    (LichtmanSignedDifferenceMultiplicity.multiplicity
      (countScale S upper) (H : ℝ) (fScale j.1) zy.1 zy.2 : ℝ)^2 else 0
  have hsub : U.image output ⊆ P.image LichtmanSignedDifferenceMultiplicity.output := by
    intro zy hzy
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hzy
    exact mem_image.mpr ⟨toCount j.2 s, fBlock_maps_to_count hS hs,
      toCount_output (mem_filter.mp hs).2⟩
  change (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    ((fiber U zy).card : ℝ)^2 else 0) ≤ ∑ zy ∈ P.image LichtmanSignedDifferenceMultiplicity.output, W zy
  calc
    _ ≤ ∑ zy ∈ U.image output, W zy := by
      apply sum_le_sum
      intro zy _
      by_cases hd : (nu : ℤ) ∣ zy.2
      · simp only [W, if_pos hd]
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
        exact_mod_cast fBlock_fiber_card_le (A := A) (a := a) hS upper H F j zy
      · simp only [W, if_neg hd, le_refl]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun zy _ _ => by
      dsimp only [W]
      split_ifs <;> positivity)

/-- A TRUE original-carrier slice now receives the existing 576/nu bound,
including its exact empty-output endpoint. F is still the original upper
cutoff; only the counting scale is the proved power of two fScale(j). -/
theorem actual_chart_count_576 {A : ℕ} {a : ℤ} {S : ℝ} (hS : 0 < S)
    (upper : Bool) (H : ℕ) (hH : 1 ≤ H) (F : ℝ) (j : ℕ × Bool)
    (nu : ℕ) (hnu : 0 < nu) :
    let R := countScale S upper
    let G := fScale j.1
    chartCountEnergy A a S upper H F j nu ≤
      576*(LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ)^5*
        (harmonic (Nat.floor (2*R)) : ℝ)*(1+(H : ℝ)/R)*((H : ℝ)*R)^2*G/(nu : ℝ) ∧
      (8*G*(H : ℝ)*R ≤ (nu : ℝ) → chartCountEnergy A a S upper H F j nu = 0) := by
  dsimp only
  have hG : 1 ≤ fScale j.1 := by
    change (1 : ℝ) ≤ (((2 : ℕ)^j.1 : ℕ) : ℝ)
    have hp : 0 < (2 : ℕ)^j.1 := pow_pos (by decide) _
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hb := LichtmanSignedDifferenceMultiplicity.signedDifference_multiplicityL2_bound
    (countScale S upper) (H : ℝ) (fScale j.1)
    (countScale_ge_one hS upper) hHR hG nu hnu
  have hd := chartCountEnergy_le_owned (A := A) (a := a) hS upper H F j nu
  refine ⟨hd.trans hb.1,?_⟩
  intro hlarge
  apply le_antisymm
  · simpa only [hb.2 hlarge] using hd
  · unfold chartCountEnergy
    dsimp only
    exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

/-- Exact finite partition of the SAME complex joint source. This is
valid for actualModeLambda/actualModeOmega with gamma2 outside branch;
the proof neither conjugates weights nor drops a future kernel m gate. -/
theorem weighted_upper_f_partition (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (K : Output → ℂ) :
    (∑ s ∈ upperSource A a S upper H F, weight lambda omega s*K (output s)) =
      ∑ j ∈ (upperSource A a S upper H F).image fKey,
        ∑ zy ∈ (fBlock A a S upper H F j).image output,
          beta (fBlock A a S upper H F j) lambda omega zy*K zy := by
  have hp := (sum_fiberwise_of_maps_to
    (s := upperSource A a S upper H F)
    (t := (upperSource A a S upper H F).image fKey) (g := fKey)
    (fun s hs => mem_image_of_mem fKey hs)
    (fun s => weight lambda omega s*K (output s))).symm
  calc
    _ = ∑ j ∈ (upperSource A a S upper H F).image fKey,
        ∑ s ∈ fBlock A a S upper H F j, weight lambda omega s*K (output s) := hp
    _ = _ := by
      apply sum_congr rfl
      intro j _
      exact weighted_pushforward _ lambda omega K

end
end ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly

/-!
SOURCEONLY / UNCOMPILED APPEND. Load AFTER ROOT's independently repaired
successor of 552-line count-license b9705fa4; same public namespace below.
Actual imports already include Part3ComplexDispersion. No fictitious
future module is imported; no parent copied or changed. No spectral bound
or count/one-norm conclusion is a hypothesis of these finite inequalities.
-/
namespace ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly
noncomputable section
open Classical Finset ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A finite weighted inequality, with coefficients unchanged. -/
theorem finite_weighted_complex_cauchy {ι : Type*} (I : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (b : ι → ℂ) :
    ‖∑ i ∈ I, b i‖^2 ≤ (∑ i ∈ I, (w i)^2)*
      ∑ i ∈ I, ‖b i‖^2/(w i)^2 := by
  have hc := complex_finset_cauchy_norm_sq I
    (fun i => (w i : ℂ)) (fun i => b i/(w i : ℂ))
  have he : (∑ i ∈ I, (w i : ℂ)*(b i/(w i : ℂ))) = ∑ i ∈ I, b i := by
    apply sum_congr rfl
    intro i _
    have hn : (w i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hw i))
    simpa only [mul_comm] using div_mul_cancel₀ (b i) hn
  have hn (i : ι) : ‖(w i : ℂ)‖ = w i := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw i)]
  rw [he] at hc
  simpa only [norm_div, hn, div_pow] using hc

def rootWeight (j : ℕ) : ℝ := (Real.sqrt 2)^j

theorem rootWeight_pos (j : ℕ) : 0 < rootWeight j :=
  pow_pos (Real.sqrt_pos.mpr (by norm_num)) j

theorem rootWeight_sq (j : ℕ) : (rootWeight j)^2 = fScale j := by
  simp only [rootWeight, fScale, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Explicit geometric cost: the eventual two sign copies cost at most
8*rootWeight J in L1 and 64*2^J in squared coefficient energy. -/
theorem rootWeight_sum_le_four (J : ℕ) :
    (∑ j ∈ range (J+1), rootWeight j) ≤ 4*rootWeight J := by
  have hq0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hq2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : (4 : ℝ) ≤ 3*Real.sqrt 2 := by
    by_contra hn
    have hh : Real.sqrt (2 : ℝ) ≤ 4/3 := by linarith
    have hm := mul_le_mul hh hh hq0 (by norm_num : (0 : ℝ) ≤ 4/3)
    nlinarith
  induction J with
  | zero => norm_num [rootWeight]
  | succ J ih =>
      rw [Finset.sum_range_succ]
      change (∑ j ∈ range (J+1), rootWeight j)+rootWeight (J+1) ≤
        4*rootWeight (J+1)
      have hp : 0 ≤ rootWeight J := (rootWeight_pos J).le
      have he : rootWeight (J+1) = rootWeight J*Real.sqrt 2 := by
        simp only [rootWeight, pow_succ]
      rw [he]
      have hm := mul_le_mul_of_nonneg_left hq hp
      linarith

theorem two_sign_root_sum_sq_le (J : ℕ) :
    (∑ j ∈ range (J+1) ×ˢ (univ : Finset Bool), rootWeight j.1)^2 ≤
      64*fScale J := by
  have he : (∑ j ∈ range (J+1) ×ˢ (univ : Finset Bool), rootWeight j.1) =
      2*∑ j ∈ range (J+1), rootWeight j := by
    simp only [sum_product, sum_const, card_univ, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_ofNat, mul_sum]
  have hsum : (∑ j ∈ range (J+1) ×ˢ (univ : Finset Bool), rootWeight j.1) ≤
      8*rootWeight J := by
    rw [he]
    linarith [rootWeight_sum_le_four J]
  calc
    _ ≤ (8*rootWeight J)^2 := pow_le_pow_left₀
      (sum_nonneg (fun j _ => (rootWeight_pos j.1).le)) hsum 2
    _ = 64*(rootWeight J)^2 := by ring
    _ = _ := by rw [rootWeight_sq]

/-- Actual finite label geometry, from the original upper f cutoff. -/
theorem actual_labels_subset_rectangle (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) :
    (upperSource A a S upper H F).image fKey ⊆
      range (Nat.log 2 (Nat.floor F)+1) ×ˢ (univ : Finset Bool) := by
  intro j hj
  obtain ⟨s,hs,hkey⟩ := mem_image.mp hj
  have hblock : (fBlock A a S upper H F j).Nonempty :=
    ⟨s,mem_filter.mpr ⟨hs,hkey⟩⟩
  have hG := nonempty_fScale_le_upper hblock
  have hp : (2 : ℕ)^j.1 ≤ Nat.floor F := Nat.le_floor hG
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ)) hp
  exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_univ _⟩

/-- The complete actual sign/dyadic-f weighting costs at most 64F.
This is independent of kappa, mode, nu, and all future Poisson variables. -/
theorem actual_label_root_sum_sq_le_64F (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) (hF : 1 ≤ F) :
    (∑ j ∈ (upperSource A a S upper H F).image fKey, rootWeight j.1)^2 ≤ 64*F := by
  have hsub := actual_labels_subset_rectangle A a S upper H F
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => (rootWeight_pos j.1).le)
  have hFn : 1 ≤ Nat.floor F := Nat.le_floor
    (show ((1 : ℕ) : ℝ) ≤ F by simpa only [Nat.cast_one] using hF)
  have hpow := Nat.pow_log_le_self 2 (show Nat.floor F ≠ 0 by omega)
  have hscale : fScale (Nat.log 2 (Nat.floor F)) ≤ F := by
    have hp : fScale (Nat.log 2 (Nat.floor F)) ≤ (Nat.floor F : ℝ) := by
      change (((2 : ℕ)^Nat.log 2 (Nat.floor F) : ℕ) : ℝ) ≤ (Nat.floor F : ℝ)
      exact_mod_cast hpow
    exact hp.trans (Nat.floor_le (by linarith))
  calc
    _ ≤ (∑ j ∈ range (Nat.log 2 (Nat.floor F)+1) ×ˢ (univ : Finset Bool),
        rootWeight j.1)^2 := pow_le_pow_left₀
          (sum_nonneg (fun j _ => (rootWeight_pos j.1).le)) hsum 2
    _ ≤ 64*fScale (Nat.log 2 (Nat.floor F)) := two_sign_root_sum_sq_le _
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)

/-- Exact coefficient reconstruction on every joint output, not just a
bound or a presumed embedding. All original complex weights remain. -/
theorem beta_eq_sum_fBlocks (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta (upperSource A a S upper H F) lambda omega zy =
      ∑ j ∈ (upperSource A a S upper H F).image fKey,
        beta (fBlock A a S upper H F j) lambda omega zy := by
  let U := upperSource A a S upper H F
  have hp := (sum_fiberwise_of_maps_to (s := fiber U zy) (t := U.image fKey)
    (g := fKey) (fun s hs => mem_image_of_mem fKey (mem_filter.mp hs).1)
    (weight lambda omega)).symm
  have he (j : ℕ × Bool) :
      (fiber U zy).filter (fun s => fKey s = j) =
        fiber (fBlock A a S upper H F j) zy := by
    ext s
    simp only [fiber, fBlock, U, mem_filter]
    tauto
  simpa only [he, beta] using hp

/-- Zero extension between literal finite output images. This uses the
proved support of the actual beta, not an energy premise. -/
theorem joint_energy_extend (U V : Finset Source) (hVU : V ⊆ U)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (nu : ℕ) :
    (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta V lambda omega zy‖^2 else 0) =
    ∑ zy ∈ V.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta V lambda omega zy‖^2 else 0 := by
  have hi : V.image output ⊆ U.image output := by
    intro zy hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem output (hVU hs)
  symm
  apply sum_subset hi
  intro zy _ hout
  have hb : beta V lambda omega zy = 0 := by
    by_contra hn
    exact hout (beta_ne_zero_mem_image hn)
  simp only [hb, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ite_self]

/-- The actual fKey recombination cost, with fixed geometric weights.
No positive coefficient/count bound is assumed. The nu|y test is literal
and neither the physical t charts nor a future Poisson m are mixed here. -/
theorem actual_fKey_weighted_energy (A : ℕ) (a : ℤ) (S : ℝ) (upper : Bool)
    (H : ℕ) (F : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (nu : ℕ) :
    let U := upperSource A a S upper H F
    let I := U.image fKey
    (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta U lambda omega zy‖^2 else 0) ≤
      (∑ j ∈ I, rootWeight j.1)*
        ∑ j ∈ I, (∑ zy ∈ (fBlock A a S upper H F j).image output,
          if (nu : ℤ) ∣ zy.2 then
            ‖beta (fBlock A a S upper H F j) lambda omega zy‖^2 else 0)/rootWeight j.1 := by
  dsimp only
  let U := upperSource A a S upper H F
  let I := U.image fKey
  let Q : ℝ := ∑ j ∈ I, rootWeight j.1
  have hp (zy : Output) : ‖beta U lambda omega zy‖^2 ≤
      Q*∑ j ∈ I, ‖beta (fBlock A a S upper H F j) lambda omega zy‖^2/rootWeight j.1 := by
    rw [beta_eq_sum_fBlocks]
    have hh := finite_weighted_complex_cauchy I
      (fun j => Real.sqrt (rootWeight j.1))
      (fun j => Real.sqrt_pos.mpr (rootWeight_pos j.1))
      (fun j => beta (fBlock A a S upper H F j) lambda omega zy)
    have hs (j : ℕ × Bool) : (Real.sqrt (rootWeight j.1))^2 = rootWeight j.1 :=
      Real.sq_sqrt (rootWeight_pos _).le
    simpa only [hs] using hh
  change (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    ‖beta U lambda omega zy‖^2 else 0) ≤ _
  calc
    _ ≤ ∑ zy ∈ U.image output, Q*∑ j ∈ I,
        if (nu : ℤ) ∣ zy.2 then
          ‖beta (fBlock A a S upper H F j) lambda omega zy‖^2/rootWeight j.1 else 0 := by
      apply sum_le_sum
      intro zy _
      by_cases hd : (nu : ℤ) ∣ zy.2
      · simpa only [if_pos hd] using hp zy
      · simp only [if_neg hd, sum_const_zero, mul_zero, le_refl]
    _ = Q*∑ j ∈ I, (∑ zy ∈ U.image output,
        if (nu : ℤ) ∣ zy.2 then
          ‖beta (fBlock A a S upper H F j) lambda omega zy‖^2 else 0)/rootWeight j.1 := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [sum_div]
      apply sum_congr rfl
      intro zy _
      by_cases hd : (nu : ℤ) ∣ zy.2
      · simp only [if_pos hd]
      · simp only [if_neg hd, zero_div]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro j _
      rw [joint_energy_extend U (fBlock A a S upper H F j)
        (filter_subset _ _) lambda omega nu]

end
end ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly
