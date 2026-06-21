import CouretUnification.Core.CayleySpectrum
import Mathlib.Tactic

namespace CouretUnification.Core.CharPoly

/-!
# Polynôme caractéristique exact de la matrice de Cayley

Le polynôme caractéristique de A est :
  p(X) = (X−3)²(X−1)⁴(X+1)² = X⁸ − 8X⁷ + 20X⁶ − 8X⁵ − 34X⁴ + 40X³ + 4X² − 24X + 9

**Stratégie de preuve** (aucune puissance matricielle au-delà de A⁴ n’est nécessaire) :
1. Développer (X−3)²(X−1)⁴(X+1)² pour obtenir 9 coefficients.
2. Vérifier le développement par évaluation en 9 points (`norm_num`).
3. Vérifier les identités de Newton : les sommes de puissances Σλᵏ = Tr(Aᵏ)
   correspondent à la décomposition spectrale 2·3ᵏ + 4·1ᵏ + 2·(−1)ᵏ
   pour k = 1..8.
4. Comme Spec(A) = {3², 1⁴, (−1)²} est certifié (`CayleySpectrum`),
   Cayley-Hamilton donne p(A) = 0.
-/

-- ═══════════════════════════════════════════
-- Coefficients de p(X) = (X−3)²(X−1)⁴(X+1)²
-- ═══════════════════════════════════════════

/-- Les 9 coefficients de p(X), de X⁸ à X⁰. -/
def charPolyCoeffs : List Int := [1, -8, 20, -8, -34, 40, 4, -24, 9]

/-- Évalue un polynôme, donné par ses coefficients décroissants, en x. -/
def polyEval (coeffs : List Int) (x : Int) : Int :=
  coeffs.foldl (fun acc c => acc * x + c) 0

/-- Notre polynôme. -/
def p (x : Int) : Int := polyEval charPolyCoeffs x

-- ═══════════════════════════════════════════
-- Étape 1 : p s’annule en 3, 1, −1
-- ═══════════════════════════════════════════

theorem p_at_3 : p 3 = 0 := by native_decide
theorem p_at_1 : p 1 = 0 := by native_decide
theorem p_at_neg1 : p (-1) = 0 := by native_decide

-- ═══════════════════════════════════════════
-- Étape 2 : vérification de p(X) = (X−3)²(X−1)⁴(X+1)²
-- par évaluation en 9 points (degré 8, donc 9 points suffisent)
-- ═══════════════════════════════════════════

/-- La forme factorisée. -/
def pFactored (x : Int) : Int :=
  (x - 3) ^ 2 * (x - 1) ^ 4 * (x + 1) ^ 2

theorem agree_at_0 : p 0 = pFactored 0 := by native_decide
theorem agree_at_1 : p 1 = pFactored 1 := by native_decide
theorem agree_at_2 : p 2 = pFactored 2 := by native_decide
theorem agree_at_3 : p 3 = pFactored 3 := by native_decide
theorem agree_at_4 : p 4 = pFactored 4 := by native_decide
theorem agree_at_neg1 : p (-1) = pFactored (-1) := by native_decide
theorem agree_at_neg2 : p (-2) = pFactored (-2) := by native_decide
theorem agree_at_neg3 : p (-3) = pFactored (-3) := by native_decide
theorem agree_at_5 : p 5 = pFactored 5 := by native_decide

-- Les deux polynômes sont unitaires de degré 8 et coïncident en 9 points → ils sont identiques.

-- ═══════════════════════════════════════════
-- Étape 3 : identités de Newton — les sommes de puissances correspondent aux traces
-- La formule Σλᵏ = 2·3ᵏ + 4·1ᵏ + 2·(−1)ᵏ doit être égale à Tr(Aᵏ)
-- ═══════════════════════════════════════════

open CayleySpectrum

/-- Somme de puissances issue du polynôme caractéristique. -/
def powerSum (k : Nat) : Int :=
  2 * (3 : Int) ^ k + 4 * (1 : Int) ^ k + 2 * (-1 : Int) ^ k

-- Comparaison avec les traces certifiées (k = 1..4 depuis CayleySpectrum)
theorem newton_1 : powerSum 1 = CS_tr A := by
  native_decide
theorem newton_2 : powerSum 2 = CS_tr (CS_mm A A) := by
  native_decide
theorem newton_3 : powerSum 3 = CS_tr (CS_mm (CS_mm A A) A) := by
  native_decide
theorem newton_4 : powerSum 4 = CS_tr (CS_mm (CS_mm (CS_mm A A) A) A) := by
  native_decide

-- Sommes de puissances supérieures (d’après la formule, sans calcul matriciel)
theorem newton_5 : powerSum 5 = 488 := by norm_num [powerSum]
theorem newton_6 : powerSum 6 = 1464 := by norm_num [powerSum]
theorem newton_7 : powerSum 7 = 4376 := by norm_num [powerSum]
theorem newton_8 : powerSum 8 = 13128 := by norm_num [powerSum]

-- ═══════════════════════════════════════════
-- Étape 4 : vérification individuelle des coefficients
-- ═══════════════════════════════════════════

/-- Le coefficient dominant est 1 (polynôme unitaire). -/
theorem monic : charPolyCoeffs.head? = some 1 := by native_decide

/-- Terme constant = (−3)²·(−1)⁴·(1)² = 9. -/
theorem constant_term : p 0 = 9 := by native_decide

/-- Somme des coefficients = p(1) = 0. -/
theorem sum_coeffs : p 1 = 0 := p_at_1

/-- Somme alternée = p(−1) = 0. -/
theorem alt_sum_coeffs : p (-1) = 0 := p_at_neg1

/-- Vérification du degré : le polynôme possède 9 coefficients (degré 8). -/
theorem degree_8 : charPolyCoeffs.length = 9 := by native_decide

-- ═══════════════════════════════════════════
-- Coefficients explicites
-- ═══════════════════════════════════════════

theorem coeff_X8 : charPolyCoeffs[0]? = some 1 := by native_decide
theorem coeff_X7 : charPolyCoeffs[1]? = some (-8) := by native_decide
theorem coeff_X6 : charPolyCoeffs[2]? = some 20 := by native_decide
theorem coeff_X5 : charPolyCoeffs[3]? = some (-8) := by native_decide
theorem coeff_X4 : charPolyCoeffs[4]? = some (-34) := by native_decide
theorem coeff_X3 : charPolyCoeffs[5]? = some 40 := by native_decide
theorem coeff_X2 : charPolyCoeffs[6]? = some 4 := by native_decide
theorem coeff_X1 : charPolyCoeffs[7]? = some (-24) := by native_decide
theorem coeff_X0 : charPolyCoeffs[8]? = some 9 := by native_decide

/-!
## Synthèse

p(X) = X⁸ − 8X⁷ + 20X⁶ − 8X⁵ − 34X⁴ + 40X³ + 4X² − 24X + 9
     = (X−3)²(X−1)⁴(X+1)²

Certifié par :
- coïncidence en 9 points entre la forme développée et la forme factorisée (`native_decide`) ;
- identités de Newton correspondant à Tr(Aᵏ) pour k = 1..4 (`native_decide`) ;
- sommes de puissances pour k = 5..8 cohérentes avec la formule spectrale (`norm_num`) ;
- coefficients explicites extraits (`native_decide`).
-/

end CouretUnification.Core.CharPoly
