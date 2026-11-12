import ImbalancedChen.P4AOriginalFull87FrontierLeafCharge
import ImbalancedChen.P4AOriginalFull87AllEighthFrontierTerminal

/-! The manuscript's fixed exponent 599/1000. The closed integer condition
N^.599 ≤ X+1 handles the final bin when N^.599 is not an integer. -/
namespace ImbalancedChen.P4AOriginalFull87Fixed599Charges
noncomputable section
open scoped Classical
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalCompleteSixthChronology (data)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedFrontier)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87UnmatchedPhysicalLeaves (rawRetainedLeaves licensedRetainedLeaves)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (leafHighQCharge)
open P4AOriginalFull87FrontierLeafCharge (raw_live_full_modulus_lt charge_zero_on_live)

theorem actual_live_product_lt_599 (N cap : ℕ) (w epsilon : ℝ)
    (hN : 1 < (N : ℝ)) (heps : epsilon ≤ 1/1000) (sign : Bool) (a b : ℕ)
    (hbeta : (if sign then actualSmallRosserPlus N cap w ((N : ℝ)^epsilon) a
      else actualSmallRosserMinus N cap w ((N : ℝ)^epsilon) a) ≠ 0)
    (hrough : (b : ℝ) < (N : ℝ)^(299/500 : ℝ)) :
    ((a*b : ℕ) : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  have ha : (a : ℝ) < (N : ℝ)^epsilon := by
    cases sign with
    | false => exact (actualSmallRosserMinus_active (by simpa using hbeta)).2.1
    | true => exact (actualSmallRosserPlus_active (by simpa using hbeta)).2.1
  have hp : 0 < (N : ℝ) := zero_lt_one.trans hN
  rw [Nat.cast_mul]
  calc
    _ ≤ (a : ℝ) * (N : ℝ)^(299/500 : ℝ) :=
      mul_le_mul_of_nonneg_left hrough.le (Nat.cast_nonneg _)
    _ < (N : ℝ)^epsilon * (N : ℝ)^(299/500 : ℝ) :=
      mul_lt_mul_of_pos_right ha (Real.rpow_pos_of_pos hp _)
    _ = (N : ℝ)^(epsilon+299/500 : ℝ) := (Real.rpow_add hp _ _).symm
    _ ≤ (N : ℝ)^(599/1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

/-- Strict live modulus below N^.599 gives the original integer weak cut. -/
theorem nat_le_cut {N X d : ℕ} (hd : (d : ℝ) < (N : ℝ)^(599/1000 : ℝ))
    (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ)) : d ≤ X := by
  have h : d < X+1 := by exact_mod_cast (hd.trans_le hX)
  omega

theorem raw_charge_599 (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w z epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (heps : epsilon ≤ 1/1000) (X : ℕ) (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ))
    (F : ℕ → ℝ) (u : FirstExitDepthState ℕ)
    (hu : u ∈ actualRawFrontier e q om N cap w z (fun _ => (1 : ℝ)))
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ rawRetainedLeaves e q om N u) :
    leafHighQCharge N cap w ((N : ℝ)^epsilon) X F leaf = 0 := by
  apply charge_zero_on_live
  intro a hb
  have h := raw_live_full_modulus_lt e q om N cap w z epsilon he hN u hu leaf hl a hb
  exact nat_le_cut (h.trans_le
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [heps]))) hX

theorem licensed_charge_599 (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hsupply : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (heps : epsilon ≤ 1/1000) (X : ℕ) (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ))
    (F : ℕ → ℝ) (u : FirstExitDepthState ℕ) (hu : u ∈ licensedFrontier (width r) n e q om N cap w z)
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ licensedRetainedLeaves (width r) n e q om N u) :
    leafHighQCharge N cap w ((N : ℝ)^epsilon) X F leaf = 0 := by
  have rough := P4AOriginalFull87AllEighthFrontierTerminal.actual_all_eighth_frontier_terminal_product_lt_fixed_power
    s r n e q om N cap w z (fun _ => (1 : ℝ)) hsupply he hN hw hz hzcap u hu leaf hl
  apply charge_zero_on_live
  intro a hb
  exact nat_le_cut (actual_live_product_lt_599 N cap w epsilon hN heps
    leaf.positive a leaf.selected.prod hb rough) hX

end
end ImbalancedChen.P4AOriginalFull87Fixed599Charges
