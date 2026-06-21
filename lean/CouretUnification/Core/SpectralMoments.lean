import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open Finset

namespace CouretUnification.Core.SpectralMoments

/-!
# Moments spectraux de la matrice de Cayley-Couret

Nous calculons les traces Tr(M^k) des puissances de la matrice d’adjacence
de Cayley pour le triplet de Couret T_C = {1, 11, 29} sur (ℤ/30ℤ)×.

Ces moments encodent la structure spectrale :
  Tr(M^k) = Σ_i λ_i^k

Pour le spectre {3², 1⁴, (-1)²}, les valeurs prédites sont :
  Tr(M¹) = 8,  Tr(M²) = 24,  Tr(M³) = 56,  Tr(M⁴) = 168,  Tr(M⁵) = 488

Le rapport Tr(M^k)/3^k → 2 (= multiplicité de la valeur propre dominante).
Cette convergence est l’*invariant des moments spectraux* du programme Couret.
-/

/-- Les 8 unités de (ℤ/30ℤ)× dans l’ordre naturel. -/
def unitsMod30 : Fin 8 → Nat
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 7 | ⟨2, _⟩ => 11 | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17 | ⟨5, _⟩ => 19 | ⟨6, _⟩ => 23 | ⟨7, _⟩ => 29

/-- Le triplet de Couret. -/
def couretSet : List Nat := [1, 11, 29]

/-- Adjacence de Cayley : M[i,j] = 1 ssi g_j ∈ g_i · T_C. -/
def cayleyAdj (i j : Fin 8) : Bool :=
  couretSet.any fun t => (unitsMod30 i * t) % 30 == unitsMod30 j

/-- Matrice de Cayley entière. -/
def cayleyMatZ (i j : Fin 8) : Int :=
  if cayleyAdj i j then 1 else 0

/-- La matrice est symétrique (car T_C = T_C⁻¹). -/
theorem cayleyMatZ_symm : ∀ i j : Fin 8, cayleyMatZ i j = cayleyMatZ j i := by
  native_decide

/-- Chaque ligne somme à 3 = |T_C|. -/
theorem cayleyMatZ_rowSum :
    ∀ i : Fin 8, (univ : Finset (Fin 8)).sum (cayleyMatZ i) = 3 := by
  native_decide

/-- Multiplication matricielle entière. -/
def matMul (A B : Fin 8 → Fin 8 → Int) (i j : Fin 8) : Int :=
  (univ : Finset (Fin 8)).sum fun k => A i k * B k j

/-- Puissance entière de matrice. -/
def matPow (A : Fin 8 → Fin 8 → Int) : Nat → Fin 8 → Fin 8 → Int
  | 0 => fun i j => if i = j then 1 else 0
  | n + 1 => matMul A (matPow A n)

/-- Trace d’une matrice entière. -/
def matTrace (A : Fin 8 → Fin 8 → Int) : Int :=
  (univ : Finset (Fin 8)).sum fun i => A i i

/-!
### Moments spectraux certifiés

Chaque `Tr(M^k)` est calculée à partir de la matrice réelle et vérifiée par `native_decide`.
-/

/-- Tr(M) = 8. L’identité 1 ∈ T_C contribue 1 à chaque entrée diagonale. -/
theorem trace_M1 : matTrace cayleyMatZ = 8 := by native_decide

/-- Tr(M²) = 24 = 8 × 3 = dim × |T_C| (identité de Parseval). -/
theorem trace_M2 : matTrace (matPow cayleyMatZ 2) = 24 := by native_decide

/-- Tr(M³) = 56. Compte les marches fermées de longueur 3 sur le graphe de Cayley. -/
theorem trace_M3 : matTrace (matPow cayleyMatZ 3) = 56 := by native_decide

/-- Tr(M⁴) = 168. -/
theorem trace_M4 : matTrace (matPow cayleyMatZ 4) = 168 := by native_decide

/-- Tr(M⁵) = 488. -/
theorem trace_M5 : matTrace (matPow cayleyMatZ 5) = 488 := by native_decide

/-!
### Cohérence avec la formule des valeurs propres

Les valeurs propres {3², 1⁴, (-1)²} prédisent :
  Tr(M^k) = 2·3^k + 4·1^k + 2·(-1)^k

Nous vérifions cette identité algébrique pour k = 1,...,5.
-/

/-- Trace prédite à partir des multiplicités des valeurs propres. -/
def predictedTrace (k : Nat) : Int :=
  2 * (3 : Int) ^ k + 4 * (1 : Int) ^ k + 2 * ((-1 : Int) ^ k)

theorem predicted_trace_M1 : predictedTrace 1 = 8 := by native_decide
theorem predicted_trace_M2 : predictedTrace 2 = 24 := by native_decide
theorem predicted_trace_M3 : predictedTrace 3 = 56 := by native_decide
theorem predicted_trace_M4 : predictedTrace 4 = 168 := by native_decide
theorem predicted_trace_M5 : predictedTrace 5 = 488 := by native_decide

/-- Les traces effectives correspondent aux prédictions par valeurs propres pour k = 1,...,5. -/
theorem traces_match_eigenvalue_formula :
    matTrace cayleyMatZ = predictedTrace 1 ∧
    matTrace (matPow cayleyMatZ 2) = predictedTrace 2 ∧
    matTrace (matPow cayleyMatZ 3) = predictedTrace 3 ∧
    matTrace (matPow cayleyMatZ 4) = predictedTrace 4 ∧
    matTrace (matPow cayleyMatZ 5) = predictedTrace 5 := by
  native_decide

end CouretUnification.Core.SpectralMoments
