import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CouretUnification.Core

def U30 : Finset (ZMod 30) := {1, 7, 11, 13, 17, 19, 23, 29}
def TC : Finset (ZMod 30) := {1, 11, 29}

theorem card_U30 : U30.card = 8 := by native_decide
theorem card_TC : TC.card = 3 := by native_decide
theorem TC_subset : TC ⊆ U30 := by native_decide

theorem phantom_product : (11 * 29 : ZMod 30) = 19 := by native_decide
theorem phantom_not_in_TC : (19 : ZMod 30) ∉ TC := by native_decide

theorem TC_not_subgroup : ¬(∀ a b : ZMod 30, a ∈ TC → b ∈ TC → a * b ∈ TC) := by
  intro h
  have h1 := h 11 29 (by native_decide) (by native_decide)
  rw [phantom_product] at h1; exact phantom_not_in_TC h1

theorem sq_1  : (1  * 1  : ZMod 30) = 1  := by native_decide
theorem sq_7  : (7  * 7  : ZMod 30) = 19 := by native_decide
theorem sq_11 : (11 * 11 : ZMod 30) = 1  := by native_decide
theorem sq_29 : (29 * 29 : ZMod 30) = 1  := by native_decide

def squareImage : Finset (ZMod 30) := U30.image (· * ·)
theorem squareImage_eq : U30.image (fun x => x * x) = {1, 19} := by native_decide

theorem order_11 : (11 : ZMod 30) ^ 2 = 1 := by native_decide
theorem order_7  : (7 : ZMod 30) ^ 4 = 1 := by native_decide
theorem crt_table :
    ({(11:ZMod 30)^0*7^0, 11^0*7^1, 11^0*7^2, 11^0*7^3,
      11^1*7^0, 11^1*7^1, 11^1*7^2, 11^1*7^3} : Finset (ZMod 30))
    = U30 := by native_decide

theorem phi_30   : Nat.totient 30   = 8   := by native_decide
theorem phi_210  : Nat.totient 210  = 48  := by native_decide
theorem phi_2310 : Nat.totient 2310 = 480 := by native_decide

theorem TC_dim_odd  : ¬ 2 ∣ TC.card  := by native_decide
theorem U30_dim_even : 2 ∣ U30.card := by native_decide

def mem_U30_iff (x : ZMod 30) :
    x ∈ U30 ↔ x = 1 ∨ x = 7 ∨ x = 11 ∨ x = 13 ∨ x = 17 ∨ x = 19 ∨ x = 23 ∨ x = 29 := by
  simp [U30]

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Core
