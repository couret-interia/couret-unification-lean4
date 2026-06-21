import CouretUnification.Core.Classification63
import Mathlib.Tactic

namespace CouretUnification.Core.Classification63Detail

/-!
# Ventilation des 63 sous-ensembles à spectre entier par cardinalité

| |S| | C(8,k) | Spectre entier | Ratio |
|-----|--------|----------|-------|
| 1 | 8 | 4 | 50.0% |
| 2 | 28 | 8 | 28.6% |
| 3 | 56 | 12 | 21.4% |
| 4 | 70 | 14 | 20.0% |
| 5 | 56 | 12 | 21.4% |
| 6 | 28 | 8 | 28.6% |
| 7 | 8 | 4 | 50.0% |
| 8 | 1 | 1 | 100% |
| **Σ** | **255** | **63** | **24.7%** |

La distribution est parfaitement palindromique : count(k) = count(8−k).
Cela provient de la symétrie par complément : F̂(Sᶜ)(χ) = −F̂(S)(χ) pour χ ≠ χ₀,
donc S possède un spectre entier si et seulement si Sᶜ en possède un.
-/

open Classification63

def popcount (mask : Nat) : Nat :=
  (List.finRange 8).countP fun i => bitSet mask i

def intSpecByCard (k : Nat) : Nat :=
  (List.range 255).countP fun m => hasIntSpec (m + 1) && (popcount (m + 1) == k)

def totalByCard (k : Nat) : Nat :=
  (List.range 255).countP fun m => popcount (m + 1) == k

-- ═══════════════════════════════════════════
-- Valeurs certifiées
-- ═══════════════════════════════════════════

theorem intSpec_1 : intSpecByCard 1 = 4 := by native_decide
theorem intSpec_2 : intSpecByCard 2 = 8 := by native_decide
theorem intSpec_3 : intSpecByCard 3 = 12 := by native_decide
theorem intSpec_4 : intSpecByCard 4 = 14 := by native_decide
theorem intSpec_5 : intSpecByCard 5 = 12 := by native_decide
theorem intSpec_6 : intSpecByCard 6 = 8 := by native_decide
theorem intSpec_7 : intSpecByCard 7 = 4 := by native_decide
theorem intSpec_8 : intSpecByCard 8 = 1 := by native_decide

-- ═══════════════════════════════════════════
-- Somme = 63
-- ═══════════════════════════════════════════

theorem ventilation_sum :
    intSpecByCard 1 + intSpecByCard 2 + intSpecByCard 3 + intSpecByCard 4 +
    intSpecByCard 5 + intSpecByCard 6 + intSpecByCard 7 + intSpecByCard 8 = 63 := by
  native_decide

-- ═══════════════════════════════════════════
-- Palindrome : count(k) = count(8−k)
-- ═══════════════════════════════════════════

theorem palindrome_17 : intSpecByCard 1 = intSpecByCard 7 := by native_decide
theorem palindrome_26 : intSpecByCard 2 = intSpecByCard 6 := by native_decide
theorem palindrome_35 : intSpecByCard 3 = intSpecByCard 5 := by native_decide

-- ═══════════════════════════════════════════
-- Faits structurels
-- ═══════════════════════════════════════════

/-- Seuls 4 des 8 singletons possèdent un spectre entier
    (ceux dont la coordonnée C₄ est paire). -/
theorem half_singletons : intSpecByCard 1 = totalByCard 1 / 2 := by native_decide

/-- Le groupe complet possède toujours un spectre entier. -/
theorem full_group : intSpecByCard 8 = 1 := intSpec_8

/-- TC = {1,11,29} est l’un des 12 triplets à spectre entier. -/
theorem couretMask_card : popcount couretMask = 3 := by native_decide
theorem couretMask_int_spec : hasIntSpec couretMask = true := by native_decide

/-- Pic en |S| = 4 (14 sous-ensembles). -/
theorem peak_at_4 : intSpecByCard 4 = 14 := intSpec_4

end CouretUnification.Core.Classification63Detail
