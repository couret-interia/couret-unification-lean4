import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

import CouretUnification.Core.U30

namespace CouretUnification.Core.ParsevalL5

/-!
# Masse de Parseval au niveau L5 (q = 2310) et correction E = 2

L’identité de Parseval sur le groupe multiplicatif (ℤ/qℤ)× donne :
  P(q) = φ(q) · |TC ∩ (ℤ/qℤ)×|

Au niveau L5 (q = 2310 = 2·3·5·7·11), l’élément 11 ∈ TC vérifie
11 | 2310, donc 11 ∉ (ℤ/2310ℤ)×. Seuls {1, 29} survivent :
  P(2310) = 480 · 2 = 960,  E = 960/480 = 2.

Cela corrige l’affirmation v17 selon laquelle E = 3 à tous les niveaux.
Le véritable invariant est E/|TC_coprime(q)| = 1 à chaque niveau.

Les indicatrices d’Euler (phi_30, phi_210, phi_2310) sont fournies par Core U30.
-/

-- ═══════════════════════════════════════════
-- Arithmétique des niveaux (entièrement par native_decide)
-- ═══════════════════════════════════════════

/-- q₃ = 30, q₄ = 210, q₅ = 2310. -/
theorem q3_def : 2 * 3 * 5 = (30 : Nat) := by norm_num
theorem q4_def : 2 * 3 * 5 * 7 = (210 : Nat) := by norm_num
theorem q5_def : 2 * 3 * 5 * 7 * 11 = (2310 : Nat) := by norm_num

-- ═══════════════════════════════════════════
-- Éléments de TC : coprimalité à chaque niveau
-- ═══════════════════════════════════════════

/-- Au niveau L3 (q = 30) : les trois éléments sont premiers avec q. -/
theorem gcd_1_30 : Nat.gcd 1 30 = 1 := by native_decide
theorem gcd_11_30 : Nat.gcd 11 30 = 1 := by native_decide
theorem gcd_29_30 : Nat.gcd 29 30 = 1 := by native_decide

/-- Au niveau L4 (q = 210) : les trois éléments sont premiers avec q. -/
theorem gcd_1_210 : Nat.gcd 1 210 = 1 := by native_decide
theorem gcd_11_210 : Nat.gcd 11 210 = 1 := by native_decide
theorem gcd_29_210 : Nat.gcd 29 210 = 1 := by native_decide

/-- Au niveau L5 (q = 2310) : 11 divise 2310, donc 11 ∉ (ℤ/2310ℤ)×. -/
theorem gcd_1_2310 : Nat.gcd 1 2310 = 1 := by native_decide
theorem gcd_11_2310 : Nat.gcd 11 2310 = 11 := by native_decide
theorem gcd_29_2310 : Nat.gcd 29 2310 = 1 := by native_decide

/-- 11 n’est PAS premier avec 2310. C’est pourquoi E chute de 3 à 2. -/
theorem eleven_not_coprime_2310 : Nat.gcd 11 2310 ≠ 1 := by native_decide

-- ═══════════════════════════════════════════
-- Nombre d’éléments de TC premiers avec q à chaque niveau
-- ═══════════════════════════════════════════

/-- Nombre d’éléments de TC premiers avec q. -/
def tcCoprime (q : Nat) : Nat :=
  (if Nat.gcd 1 q = 1 then 1 else 0) +
  (if Nat.gcd 11 q = 1 then 1 else 0) +
  (if Nat.gcd 29 q = 1 then 1 else 0)

theorem tcCoprime_30 : tcCoprime 30 = 3 := by native_decide
theorem tcCoprime_210 : tcCoprime 210 = 3 := by native_decide
theorem tcCoprime_2310 : tcCoprime 2310 = 2 := by native_decide

-- ═══════════════════════════════════════════
-- Masse de Parseval : P(q) = φ(q) · |TC_coprime(q)|
-- ═══════════════════════════════════════════

/-- Formule de la masse de Parseval. -/
def parsevalMass (q : Nat) : Nat := Nat.totient q * tcCoprime q

theorem parseval_30 : parsevalMass 30 = 24 := by native_decide
theorem parseval_210 : parsevalMass 210 = 144 := by native_decide

/-- **Résultat principal** : Parseval(2310) = 960, et non 1440. -/
theorem parseval_2310 : parsevalMass 2310 = 960 := by native_decide

/-- La valeur erronée (issue de v17) : 3 · φ(2310) = 1440 ≠ 960. -/
theorem wrong_parseval_2310 : 3 * Nat.totient 2310 = 1440 := by native_decide
theorem parseval_correction : (960 : Nat) ≠ 1440 := by norm_num

-- ═══════════════════════════════════════════
-- Invariant d’énergie E = P(q)/φ(q)
-- ═══════════════════════════════════════════

/-- Énergie à chaque niveau. -/
noncomputable def energy (q : Nat) : ℚ := (parsevalMass q : ℚ) / (Nat.totient q : ℚ)

theorem energy_30 : energy 30 = 3 := by
  simp [energy, parseval_30, CouretUnification.Core.phi_30]; norm_num

theorem energy_210 : energy 210 = 3 := by
  simp [energy, parseval_210, CouretUnification.Core.phi_210]; norm_num

/-- **E(2310) = 2**, et non 3. -/
theorem energy_2310 : energy 2310 = 2 := by
  simp [energy, parseval_2310, CouretUnification.Core.phi_2310]; norm_num

-- ═══════════════════════════════════════════
-- Le véritable invariant : E/|TC_coprime| = 1 toujours
-- ═══════════════════════════════════════════

noncomputable def normalizedEnergy (q : Nat) : ℚ :=
  energy q / (tcCoprime q : ℚ)

theorem normalized_energy_30 : normalizedEnergy 30 = 1 := by
  simp [normalizedEnergy, energy, parseval_30, CouretUnification.Core.phi_30, tcCoprime_30]; norm_num

theorem normalized_energy_210 : normalizedEnergy 210 = 1 := by
  simp [normalizedEnergy, energy, parseval_210, CouretUnification.Core.phi_210, tcCoprime_210]; norm_num

theorem normalized_energy_2310 : normalizedEnergy 2310 = 1 := by
  simp [normalizedEnergy, energy, parseval_2310, CouretUnification.Core.phi_2310, tcCoprime_2310]; norm_num

/-!
## Synthèse

| Niveau | q | φ(q) | |TC_cop| | Parseval | E | E/|TC_cop| |
|-------|------|------|---------|----------|---|------------|
| L3 | 30 | 8 | 3 | 24 | 3 | 1 |
| L4 | 210 | 48 | 3 | 144 | 3 | 1 |
| L5 | 2310 | 480 | 2 | 960 | 2 | 1 |

Correction v17→v18 : au niveau L5, 11 | 2310 force χ(11) = 0 pour tous
les caractères de Dirichlet modulo 2310. Le nombre d’éléments premiers avec q
chute de 3 à 2, donnant P = 960 (et non 1440) et E = 2 (et non 3).

L’**invariant stable** est E/|TC_coprime(q)| = 1 à chaque niveau.
-/

end CouretUnification.Core.ParsevalL5
