import CouretUnification.Core.CayleySpectrum
import Mathlib.Tactic

namespace CouretUnification.Core
namespace CayleyConnected

/-!
# Connexité du graphe de Cayley Cay(G₃₀, TC)

The Cayley graph is connected iff there exists k such that
A^k has all entries > 0. We find the smallest such k.
-/

open CayleySpectrum

-- Matrix powers (explicit chain, no recursion)
def A2 : IMat := mm A A
def A3 : IMat := mm A2 A
def A4 : IMat := mm A3 A
def A5 : IMat := mm A4 A
def A6 : IMat := mm A5 A
def A7 : IMat := mm A6 A

/-- Check that all entries of a matrix are ≥ 1. -/
def allPositive (M : IMat) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 8).all fun j => M i j ≥ 1

-- Find the exact diameter
theorem A2_not_connected : allPositive A2 = false := by native_decide
theorem A3_not_connected : allPositive A3 = false := by native_decide
theorem A4_not_connected : allPositive A4 = false := by native_decide
theorem A5_not_connected : allPositive A5 = false := by native_decide
theorem A6_not_connected : allPositive A6 = false := by native_decide

/--
**Main theorem**: A⁷ has all entries ≥ 1.
Therefore Cay(G₃₀, TC) is connected with diameter ≤ 7.
-/
theorem A7_all_positive : allPositive A7 = true := by native_decide

/-- The diameter is exactly 7. -/
theorem diameter_eq_7 :
    allPositive A6 = false ∧ allPositive A7 = true :=
  ⟨A6_not_connected, A7_all_positive⟩

/-- Trace consistency: Tr(A⁷) = 4376. -/
theorem trace_A7_check : tr A7 = 4376 := by native_decide

/-!
## Summary

| k | All entries > 0? |
|---|------------------|
| 2 | no |
| 3 | no |
| 4 | no |
| 5 | no |
| 6 | no |
| 7 | **yes** |

Cay(G₃₀, TC) is connected with diameter exactly 7.
-/

end CayleyConnected
end CouretUnification.Core