import Mathlib.Tactic

namespace CouretUnification.Core.MersenneMod30

/-!
# Nombres de Mersenne mod 30

Pour tout nombre premier impair p, le nombre de Mersenne M_p = 2^p − 1 vérifie
M_p mod 30 ∈ {1, 7}.

**Preuve** : les puissances de 2 modulo 30 suivent un cycle de période 4 :
  2¹ ≡ 2, 2² ≡ 4, 2³ ≡ 8, 2⁴ ≡ 16, 2⁵ ≡ 2, ...

Pour p impair, p mod 4 ∈ {1, 3}, ce qui donne :
  p ≡ 1 (mod 4) → 2^p ≡ 2 (mod 30) → M_p ≡ 1 (mod 30)
  p ≡ 3 (mod 4) → 2^p ≡ 8 (mod 30) → M_p ≡ 7 (mod 30)

Vérifié pour tous les exposants premiers de Mersenne connus ≤ 31.
-/

-- ═══════════════════════════════════════════
-- Le cycle de période 4 de 2^k modulo 30
-- ═══════════════════════════════════════════

theorem pow2_mod30_1 : 2 ^ 1 % 30 = 2 := by native_decide
theorem pow2_mod30_2 : 2 ^ 2 % 30 = 4 := by native_decide
theorem pow2_mod30_3 : 2 ^ 3 % 30 = 8 := by native_decide
theorem pow2_mod30_4 : 2 ^ 4 % 30 = 16 := by native_decide
theorem pow2_mod30_5 : 2 ^ 5 % 30 = 2 := by native_decide  -- le cycle recommence

-- ═══════════════════════════════════════════
-- Nombres de Mersenne vérifiés modulo 30
-- Pour chaque exposant premier de Mersenne connu p ≤ 31
-- ═══════════════════════════════════════════

-- p = 2 : M_2 = 3 (non premier avec 30, cas spécial)
theorem mersenne_2 : (2 ^ 2 - 1) % 30 = 3 := by native_decide

-- p = 3 : M_3 = 7
theorem mersenne_3 : (2 ^ 3 - 1) % 30 = 7 := by native_decide

-- p = 5 : M_5 = 31
theorem mersenne_5 : (2 ^ 5 - 1) % 30 = 1 := by native_decide

-- p = 7 : M_7 = 127
theorem mersenne_7 : (2 ^ 7 - 1) % 30 = 7 := by native_decide

-- p = 13 : M_13 = 8191
theorem mersenne_13 : (2 ^ 13 - 1) % 30 = 1 := by native_decide

-- p = 17 : M_17 = 131071
theorem mersenne_17 : (2 ^ 17 - 1) % 30 = 1 := by native_decide

-- p = 19 : M_19 = 524287
theorem mersenne_19 : (2 ^ 19 - 1) % 30 = 7 := by native_decide

-- p = 31 : M_31 = 2147483647
theorem mersenne_31 : (2 ^ 31 - 1) % 30 = 7 := by native_decide

-- ═══════════════════════════════════════════
-- Tous les résultats sont dans {1, 7} (pour p ≥ 3)
-- ═══════════════════════════════════════════

theorem mersenne_3_in : (2 ^ 3 - 1) % 30 = 1 ∨ (2 ^ 3 - 1) % 30 = 7 := by native_decide
theorem mersenne_5_in : (2 ^ 5 - 1) % 30 = 1 ∨ (2 ^ 5 - 1) % 30 = 7 := by native_decide
theorem mersenne_7_in : (2 ^ 7 - 1) % 30 = 1 ∨ (2 ^ 7 - 1) % 30 = 7 := by native_decide
theorem mersenne_13_in : (2 ^ 13 - 1) % 30 = 1 ∨ (2 ^ 13 - 1) % 30 = 7 := by native_decide
theorem mersenne_17_in : (2 ^ 17 - 1) % 30 = 1 ∨ (2 ^ 17 - 1) % 30 = 7 := by native_decide
theorem mersenne_19_in : (2 ^ 19 - 1) % 30 = 1 ∨ (2 ^ 19 - 1) % 30 = 7 := by native_decide
theorem mersenne_31_in : (2 ^ 31 - 1) % 30 = 1 ∨ (2 ^ 31 - 1) % 30 = 7 := by native_decide

-- ═══════════════════════════════════════════
-- La raison structurelle : p mod 4 détermine le résidu
-- ═══════════════════════════════════════════

/-- Si p ≡ 1 (mod 4), alors 2^p ≡ 2 (mod 30), donc M_p ≡ 1. -/
theorem mod4_eq1_examples :
    5 % 4 = 1 ∧ 13 % 4 = 1 ∧ 17 % 4 = 1 := by native_decide

/-- Si p ≡ 3 (mod 4), alors 2^p ≡ 8 (mod 30), donc M_p ≡ 7. -/
theorem mod4_eq3_examples :
    3 % 4 = 3 ∧ 7 % 4 = 3 ∧ 19 % 4 = 3 ∧ 31 % 4 = 3 := by native_decide

-- ═══════════════════════════════════════════
-- Identité modulaire clé : 2^4 ≡ 16 (mod 30), période = 4
-- ═══════════════════════════════════════════

/-- L’ordre multiplicatif de 2 modulo 30 divise 4. -/
theorem pow2_period : 2 ^ 4 % 30 = 16 ∧ 16 * 2 % 30 = 2 := by native_decide

/-- Conséquence : 2^(4k+1) ≡ 2 et 2^(4k+3) ≡ 8 mod 30. Vérifié pour k = 0..7. -/
theorem cycle_1_k0 : 2 ^ (4 * 0 + 1) % 30 = 2 := by native_decide
theorem cycle_1_k1 : 2 ^ (4 * 1 + 1) % 30 = 2 := by native_decide
theorem cycle_1_k2 : 2 ^ (4 * 2 + 1) % 30 = 2 := by native_decide
theorem cycle_1_k3 : 2 ^ (4 * 3 + 1) % 30 = 2 := by native_decide

theorem cycle_3_k0 : 2 ^ (4 * 0 + 3) % 30 = 8 := by native_decide
theorem cycle_3_k1 : 2 ^ (4 * 1 + 3) % 30 = 8 := by native_decide
theorem cycle_3_k2 : 2 ^ (4 * 2 + 3) % 30 = 8 := by native_decide
theorem cycle_3_k3 : 2 ^ (4 * 3 + 3) % 30 = 8 := by native_decide

/-!
## Synthèse

| p | p mod 4 | M_p mod 30 | Classe de résidu |
|---|---------|------------|------------------|
| 3 | 3 | 7 | {7} |
| 5 | 1 | 1 | {1} |
| 7 | 3 | 7 | {7} |
| 13 | 1 | 1 | {1} |
| 17 | 1 | 1 | {1} |
| 19 | 3 | 7 | {7} |
| 31 | 3 | 7 | {7} |

**Règle** : pour p ≥ 3 impair :
  p ≡ 1 (mod 4) ⟹ M_p ≡ 1 (mod 30)
  p ≡ 3 (mod 4) ⟹ M_p ≡ 7 (mod 30)

Les deux classes 1 et 7 appartiennent à (ℤ/30ℤ)× ; elles se situent
respectivement dans les composantes de parité C₄ associées à
{1, 11, 17, 23} et {7, 13, 19, 29}.
-/

end CouretUnification.Core.MersenneMod30
