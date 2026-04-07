import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Core
namespace ParsevalL5

/-!
# Parseval mass at L5 (q = 2310) and the E = 2 correction

The Parseval identity on the multiplicative group (ℤ/qℤ)× gives:
  P(q) = φ(q) · |TC ∩ (ℤ/qℤ)×|

At L5 (q = 2310 = 2·3·5·7·11), the element 11 ∈ TC satisfies
11 | 2310, so 11 ∉ (ℤ/2310ℤ)×. Only {1, 29} survive:
  P(2310) = 480 · 2 = 960,  E = 960/480 = 2.

This corrects the v17 claim E = 3 at all levels.
The true invariant is E/|TC_coprime(q)| = 1 at every level.
-/

-- ═══════════════════════════════════════════
-- Level arithmetic (all by native_decide)
-- ═══════════════════════════════════════════

/-- q₃ = 30, q₄ = 210, q₅ = 2310. -/
theorem q3_def : 2 * 3 * 5 = (30 : Nat) := by norm_num
theorem q4_def : 2 * 3 * 5 * 7 = (210 : Nat) := by norm_num
theorem q5_def : 2 * 3 * 5 * 7 * 11 = (2310 : Nat) := by norm_num

/-- Euler totients. -/
theorem phi_30 : Nat.totient 30 = 8 := by native_decide
theorem phi_210 : Nat.totient 210 = 48 := by native_decide
theorem phi_2310 : Nat.totient 2310 = 480 := by native_decide

-- ═══════════════════════════════════════════
-- TC elements: coprimality at each level
-- ═══════════════════════════════════════════

/-- At L3 (q = 30): all three elements are coprime. -/
theorem gcd_1_30 : Nat.gcd 1 30 = 1 := by native_decide
theorem gcd_11_30 : Nat.gcd 11 30 = 1 := by native_decide
theorem gcd_29_30 : Nat.gcd 29 30 = 1 := by native_decide

/-- At L4 (q = 210): all three elements are coprime. -/
theorem gcd_1_210 : Nat.gcd 1 210 = 1 := by native_decide
theorem gcd_11_210 : Nat.gcd 11 210 = 1 := by native_decide
theorem gcd_29_210 : Nat.gcd 29 210 = 1 := by native_decide

/-- At L5 (q = 2310): 11 divides 2310, so 11 ∉ (ℤ/2310ℤ)×. -/
theorem gcd_1_2310 : Nat.gcd 1 2310 = 1 := by native_decide
theorem gcd_11_2310 : Nat.gcd 11 2310 = 11 := by native_decide
theorem gcd_29_2310 : Nat.gcd 29 2310 = 1 := by native_decide

/-- 11 is NOT coprime to 2310. This is why E drops from 3 to 2. -/
theorem eleven_not_coprime_2310 : Nat.gcd 11 2310 ≠ 1 := by native_decide

-- ═══════════════════════════════════════════
-- TC coprime count at each level
-- ═══════════════════════════════════════════

/-- Number of TC elements coprime to q. -/
def tcCoprime (q : Nat) : Nat :=
  (if Nat.gcd 1 q = 1 then 1 else 0) +
  (if Nat.gcd 11 q = 1 then 1 else 0) +
  (if Nat.gcd 29 q = 1 then 1 else 0)

theorem tcCoprime_30 : tcCoprime 30 = 3 := by native_decide
theorem tcCoprime_210 : tcCoprime 210 = 3 := by native_decide
theorem tcCoprime_2310 : tcCoprime 2310 = 2 := by native_decide

-- ═══════════════════════════════════════════
-- Parseval mass: P(q) = φ(q) · |TC_coprime(q)|
-- ═══════════════════════════════════════════

/-- Parseval mass formula. -/
def parsevalMass (q : Nat) : Nat :=
  Nat.totient q * tcCoprime q

theorem parseval_30 : parsevalMass 30 = 24 := by native_decide
theorem parseval_210 : parsevalMass 210 = 144 := by native_decide

/-- **Main result**: Parseval(2310) = 960, not 1440. -/
theorem parseval_2310 : parsevalMass 2310 = 960 := by native_decide

/-- The wrong value (from v17): 3 · φ(2310) = 1440 ≠ 960. -/
theorem wrong_parseval_2310 : 3 * Nat.totient 2310 = 1440 := by native_decide
theorem parseval_correction : (960 : Nat) ≠ 1440 := by norm_num

-- ═══════════════════════════════════════════
-- Energy invariant E = P(q)/φ(q)
-- ═══════════════════════════════════════════

/-- Energy at each level. -/
noncomputable def energy (q : Nat) : ℚ :=
  (parsevalMass q : ℚ) / (Nat.totient q : ℚ)

theorem energy_30 : energy 30 = 3 := by
  simp [energy, parseval_30, phi_30]; norm_num

theorem energy_210 : energy 210 = 3 := by
  simp [energy, parseval_210, phi_210]; norm_num

/-- **E(2310) = 2**, not 3. -/
theorem energy_2310 : energy 2310 = 2 := by
  simp [energy, parseval_2310, phi_2310]; norm_num

-- ═══════════════════════════════════════════
-- The true invariant: E/|TC_coprime| = 1 always
-- ═══════════════════════════════════════════

noncomputable def normalizedEnergy (q : Nat) : ℚ :=
  energy q / (tcCoprime q : ℚ)

theorem normalized_energy_30 : normalizedEnergy 30 = 1 := by
  simp [normalizedEnergy, energy, parseval_30, phi_30, tcCoprime_30]; norm_num

theorem normalized_energy_210 : normalizedEnergy 210 = 1 := by
  simp [normalizedEnergy, energy, parseval_210, phi_210, tcCoprime_210]; norm_num

theorem normalized_energy_2310 : normalizedEnergy 2310 = 1 := by
  simp [normalizedEnergy, energy, parseval_2310, phi_2310, tcCoprime_2310]; norm_num

/-!
## Summary

| Level | q | φ(q) | |TC_cop| | Parseval | E | E/|TC_cop| |
|-------|------|------|---------|----------|---|------------|
| L3 | 30 | 8 | 3 | 24 | 3 | 1 |
| L4 | 210 | 48 | 3 | 144 | 3 | 1 |
| L5 | 2310 | 480 | 2 | 960 | 2 | 1 |

The correction v17→v18: at L5, 11 | 2310 forces χ(11) = 0 for all
Dirichlet characters mod 2310. The coprime count drops from 3 to 2,
giving P = 960 (not 1440) and E = 2 (not 3).

The **stable invariant** is E/|TC_coprime(q)| = 1 at every level.
-/

end ParsevalL5
end CouretUnification.Core