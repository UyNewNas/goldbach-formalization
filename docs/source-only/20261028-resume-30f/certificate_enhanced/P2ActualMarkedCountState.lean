import ImbalancedChen.P2FrozenReceiverCountActions
import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A concrete finite count enclosure, initialized by actual Rosser divisor
polynomials and iterated using genuine frozen-receiver Buchstab actions.
Every candidate in one round reads the immutable previous state. There
is no supplied Sound state: the public count bounds are proved from the
initial arithmetic polynomials by induction. Its finite defects need not
be positive. In particular this does not license the original 2327/100000
seed, the frozen184 state, any W1/W2 switched cost, or H248.
-/
namespace ImbalancedChen.P2ActualMarkedCountState

noncomputable section
open Set Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open MathlibNt.SieveTheory.LinearSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

abbrev Query := {s : ℝ // s∈Icc (1:ℝ) 5}

def rootLevel (Q : ℝ) (d : ℕ) : ℕ := ⌊Q/(d:ℝ)⌋₊+1

theorem root_level_geometry {Q s : ℝ} {d : ℕ}
    (hR : 1<Q/(d:ℝ)) (hs : 1≤s) :
    1<rootLevel Q d ∧ cutoff Q d s≤(rootLevel Q d:ℝ) := by
  have hfloor : 1≤⌊Q/(d:ℝ)⌋₊ := Nat.le_floor hR.le
  have hs0 : 0<s := by linarith
  have he : 1/s≤1 := (div_le_one hs0).mpr hs
  have hcut : cutoff Q d s≤Q/(d:ℝ) := by
    unfold cutoff
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR.le he
  have hlevel : Q/(d:ℝ)<(rootLevel Q d:ℝ) := by
    simpa only [rootLevel,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (Q/(d:ℝ))
  exact ⟨by dsimp [rootLevel];omega,hcut.trans hlevel.le⟩

theorem root_coefficient_full_Q {side : Bool} {N d r : ℕ} {Q z : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ))
    (hr : ordinaryRosserWeight side N d (rootLevel Q d) z r≠0) :
    ((d*r:ℕ):ℝ)≤Q ∧ r.Coprime (d*N) := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hlevel : r<rootLevel Q d := by
    cases side
    · exact lowerRosserWeight_lt_level hr
    · exact upperRosserWeight_lt_level hr
  have hdiv : r∣ordinarySievePrimeProduct (d*N) z := by
    cases side
    · exact lowerRosserWeight_dvd hr
    · exact upperRosserWeight_dvd hr
  have hfloor : r≤⌊Q/(d:ℝ)⌋₊ := by
    dsimp [rootLevel] at hlevel
    omega
  have hres : (r:ℝ)≤Q/(d:ℝ) :=
    (Nat.le_floor_iff (by linarith : (0:ℝ)≤Q/(d:ℝ))).mp hfloor
  refine ⟨?_,(ordinarySievePrimeProduct_coprime (d*N) z).of_dvd_left hdiv⟩
  simpa only [Nat.cast_mul,mul_comm] using (le_div_iff₀ hdR).mp hres

/-- The initial true finite count envelope, with each original prefix
level still under the common full modulus Q. -/
def rootPolynomial {ι : Type*} (side : Bool) (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (s : ℝ) : ℝ :=
  ∑ a∈L,sigma a*frozenPolynomial side N (B a) (rootLevel Q (B a)) (E a) (cutoff Q (B a) s)

theorem root_count_enclosure {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) {s : ℝ}
    (hsigma : ∀a∈L,0≤sigma a) (hR : ∀a∈L,1<Q/(B a:ℝ)) (hs : 1≤s) :
    rootPolynomial false N Q L B sigma E s≤markedPhi N Q L B sigma E s ∧
    markedPhi N Q L B sigma E s≤rootPolynomial true N Q L B sigma E s := by
  constructor
  · unfold rootPolynomial markedPhi
    apply sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (frozenRosser_lower_finite (E a)
      (root_level_geometry (hR a ha) hs).2) (hsigma a ha)
  · unfold rootPolynomial markedPhi
    apply sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (frozenRosser_upper_finite (E a)
      (root_level_geometry (hR a ha) hs).1 (root_level_geometry (hR a ha) hs).2)
      (hsigma a ha)

structure CountState where
  upper : Query → ℝ
  lower : Query → ℝ

def initial {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) : CountState :=
  ⟨fun s => rootPolynomial true N Q L B sigma E s.val,
   fun s => rootPolynomial false N Q L B sigma E s.val⟩

def upperCandidate {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (old : CountState) (anchor s : Query) : ℝ :=
  if 2≤s.val ∧ s.val≤anchor.val then
    old.upper anchor-markedChildPolynomial false N Q L B sigma E s.val anchor.val
  else old.upper s

def lowerCandidate {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (old : CountState) (anchor s : Query) : ℝ :=
  if 2≤s.val ∧ s.val≤anchor.val then
    old.lower anchor-markedChildPolynomial true N Q L B sigma E s.val anchor.val
  else old.lower s

def upperAlternatives {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (old : CountState) :
    List Query → Query → ℝ
  | [],s => old.upper s
  | a::as,s => min (upperAlternatives N Q L B sigma E old as s)
      (upperCandidate N Q L B sigma E old a s)

def lowerAlternatives {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (old : CountState) :
    List Query → Query → ℝ
  | [],s => old.lower s
  | a::as,s => max (lowerAlternatives N Q L B sigma E old as s)
      (lowerCandidate N Q L B sigma E old a s)

def oneRound {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (old : CountState) : CountState :=
  ⟨upperAlternatives N Q L B sigma E old bank,
   lowerAlternatives N Q L B sigma E old bank⟩

def iterate {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (bank : List Query) :
    ℕ → CountState
  | 0 => initial N Q L B sigma E
  | n+1 => oneRound N Q L B sigma E bank (iterate N Q L B sigma E bank n)

/-- No final count inequality or initial state licence is supplied.
The induction begins at the independently defined actual prime-sequence
Rosser polynomial. Only its arithmetic positivity/physical-level gates
are inputs. This theorem concerns the explicit ordinary count actions. -/
theorem iterate_actual_count_enclosure {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (bank : List Query)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (rounds : ℕ) (s : Query) :
    (iterate N Q L B sigma E bank rounds).lower s≤markedPhi N Q L B sigma E s.val ∧
    markedPhi N Q L B sigma E s.val≤(iterate N Q L B sigma E bank rounds).upper s := by
  induction rounds generalizing s with
  | zero => exact root_count_enclosure N Q L B sigma E hsigma hR s.property.1
  | succ n ih =>
      let old := iterate N Q L B sigma E bank n
      have hup (a s : Query) : markedPhi N Q L B sigma E s.val≤
          upperCandidate N Q L B sigma E old a s := by
        unfold upperCandidate
        split_ifs with hg
        · have hc := marked_actual_upper_transfer N Q L B sigma E hB hsigma hR hg.1 hg.2
          have ho := (ih a).2
          change markedPhi N Q L B sigma E a.val≤old.upper a at ho
          linarith
        · exact (ih s).2
      have hlo (a s : Query) : lowerCandidate N Q L B sigma E old a s≤
          markedPhi N Q L B sigma E s.val := by
        unfold lowerCandidate
        split_ifs with hg
        · have hc := marked_actual_lower_transfer N Q L B sigma E hB hsigma hR hg.1 hg.2
          have ho := (ih a).1
          change old.lower a≤markedPhi N Q L B sigma E a.val at ho
          linarith
        · exact (ih s).1
      have hupper : ∀ as : List Query,markedPhi N Q L B sigma E s.val≤
          upperAlternatives N Q L B sigma E old as s := by
        intro as
        induction as with
        | nil => exact (ih s).2
        | cons a as ha => exact le_min ha (hup a s)
      have hlower : ∀ as : List Query,lowerAlternatives N Q L B sigma E old as s≤
          markedPhi N Q L B sigma E s.val := by
        intro as
        induction as with
        | nil => exact (ih s).1
        | cons a as ha => exact max_le ha (hlo a s)
      exact ⟨hlower bank,hupper bank⟩

/-- The literal positive marked-family normalization, before any label
product collapse. Equal products keep their original multiplicities. -/
def markedTheta {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) : ℝ :=
  4*logarithmicIntegral N*∑ a∈L,sigma a*wuSingularSeries (B a*N)/
    ((Nat.totient (B a):ℝ)*Real.log (Q/(B a:ℝ)))

theorem markedTheta_pos {ι : Type*} {N : ℕ} (hN : 4≤N) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (hB : ∀a∈L,0<B a)
    (hsigma : ∀a∈L,0≤sigma a) (hR : ∀a∈L,1<Q/(B a:ℝ))
    (hpositive : ∃a∈L,0<sigma a) : 0<markedTheta N Q L B sigma := by
  have hNpos : 0<N := by omega
  have hNreal : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hli : 0<logarithmicIntegral N :=
    (div_pos (Nat.cast_pos.mpr hNpos)
      (mul_pos (by norm_num) (Real.log_pos hNreal))).trans_le (box_trueLi_lower hN)
  have hden (a : ι) (ha : a∈L) :
      0<(Nat.totient (B a):ℝ)*Real.log (Q/(B a:ℝ)) :=
    mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (hB a ha))) (Real.log_pos (hR a ha))
  have hseries (a : ι) (ha : a∈L) : 0<wuSingularSeries (B a*N) :=
    wuSingularSeries_pos _ (mul_pos (hB a ha) hNpos)
  unfold markedTheta
  apply mul_pos (mul_pos (by norm_num) hli)
  apply sum_pos'
  · intro a ha
    exact div_nonneg (mul_nonneg (hsigma a ha) (hseries a ha).le) (hden a ha).le
  · obtain ⟨a,ha,hpos⟩ := hpositive
    exact ⟨a,ha,div_pos (mul_pos hpos (hseries a ha)) (hden a ha)⟩

def upperDefect {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (state : CountState) (s : Query) : ℝ :=
  wuUpperCoefficient s.val-state.upper s/markedTheta N Q L B sigma

def lowerDefect {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (state : CountState) (s : Query) : ℝ :=
  state.lower s/markedTheta N Q L B sigma-wuLowerCoefficient s.val

/-- Actual H/h *count* semantics for the constructed finite state. The
normalizer is independently the original marked sum. No ordinary rho
density is redefined; no positive adopted seed or table is inferred. -/
theorem iterate_actual_defect_comparison {ι : Type*} {N : ℕ} (hN : 4≤N)
    (Q : ℝ) (L : Finset ι) (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (hpositive : ∃a∈L,0<sigma a)
    (rounds : ℕ) (s : Query) :
    wuLowerCoefficient s.val+
        lowerDefect N Q L B sigma (iterate N Q L B sigma E bank rounds) s≤
      markedPhi N Q L B sigma E s.val/markedTheta N Q L B sigma ∧
    markedPhi N Q L B sigma E s.val/markedTheta N Q L B sigma≤
      wuUpperCoefficient s.val-
        upperDefect N Q L B sigma (iterate N Q L B sigma E bank rounds) s := by
  have ht := (markedTheta_pos hN Q L B sigma hB hsigma hR hpositive).le
  have hc := iterate_actual_count_enclosure N Q L B sigma E bank hB hsigma hR rounds s
  constructor
  · have hl := div_le_div_of_nonneg_right hc.1 ht
    dsimp [lowerDefect]
    linarith
  · have hu := div_le_div_of_nonneg_right hc.2 ht
    dsimp [upperDefect]
    linarith

end
end ImbalancedChen.P2ActualMarkedCountState
