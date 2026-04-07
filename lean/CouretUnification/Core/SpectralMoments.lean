import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open Finset

namespace CouretUnification.Core

/-!
# Spectral moments of the Couret-Cayley matrix

We compute the traces Tr(M^k) of powers of the Cayley adjacency matrix
for the Couret triplet T_C = {1, 11, 29} on (ℤ/30ℤ)×.

These moments encode the spectral structure:
  Tr(M^k) = Σ_i λ_i^k

For the spectrum {3², 1⁴, (-1)²}, the predicted values are:
  Tr(M¹) = 8,  Tr(M²) = 24,  Tr(M³) = 56,  Tr(M⁴) = 168,  Tr(M⁵) = 488

The ratio Tr(M^k)/3^k → 2 (= multiplicity of the dominant eigenvalue).
This convergence is the *spectral moment invariant* of the Couret programme.
-/

namespace SpectralMoments

/-- The 8 units of (ℤ/30ℤ)× in natural order. -/
def unitsMod30 : Fin 8 → Nat
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 7 | ⟨2, _⟩ => 11 | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17 | ⟨5, _⟩ => 19 | ⟨6, _⟩ => 23 | ⟨7, _⟩ => 29

/-- The Couret triplet. -/
def couretSet : List Nat := [1, 11, 29]

/-- Cayley adjacency: M[i,j] = 1 iff g_j ∈ g_i · T_C. -/
def cayleyAdj (i j : Fin 8) : Bool :=
  couretSet.any fun t => (unitsMod30 i * t) % 30 == unitsMod30 j

/-- Integer Cayley matrix. -/
def cayleyMatZ (i j : Fin 8) : Int :=
  if cayleyAdj i j then 1 else 0

/-- The matrix is symmetric (since T_C = T_C⁻¹). -/
theorem cayleyMatZ_symm : ∀ i j : Fin 8, cayleyMatZ i j = cayleyMatZ j i := by
  native_decide

/-- Every row sums to 3 = |T_C|. -/
theorem cayleyMatZ_rowSum :
    ∀ i : Fin 8, (univ : Finset (Fin 8)).sum (cayleyMatZ i) = 3 := by
  native_decide

/-- Integer matrix multiplication. -/
def matMul (A B : Fin 8 → Fin 8 → Int) (i j : Fin 8) : Int :=
  (univ : Finset (Fin 8)).sum fun k => A i k * B k j

/-- Integer matrix power. -/
def matPow (A : Fin 8 → Fin 8 → Int) : Nat → Fin 8 → Fin 8 → Int
  | 0 => fun i j => if i = j then 1 else 0
  | n + 1 => matMul A (matPow A n)

/-- Trace of an integer matrix. -/
def matTrace (A : Fin 8 → Fin 8 → Int) : Int :=
  (univ : Finset (Fin 8)).sum fun i => A i i

/-!
### Certified spectral moments

Each `Tr(M^k)` is computed from the actual matrix and verified by `native_decide`.
-/

/-- Tr(M) = 8. The identity 1 ∈ T_C contributes 1 to each diagonal entry. -/
theorem trace_M1 : matTrace cayleyMatZ = 8 := by native_decide

/-- Tr(M²) = 24 = 8 × 3 = dim × |T_C| (Parseval identity). -/
theorem trace_M2 : matTrace (matPow cayleyMatZ 2) = 24 := by native_decide

/-- Tr(M³) = 56. Counts closed walks of length 3 on the Cayley graph. -/
theorem trace_M3 : matTrace (matPow cayleyMatZ 3) = 56 := by native_decide

/-- Tr(M⁴) = 168. -/
theorem trace_M4 : matTrace (matPow cayleyMatZ 4) = 168 := by native_decide

/-- Tr(M⁵) = 488. -/
theorem trace_M5 : matTrace (matPow cayleyMatZ 5) = 488 := by native_decide

/-!
### Consistency with eigenvalue formula

The eigenvalues {3², 1⁴, (-1)²} predict:
  Tr(M^k) = 2·3^k + 4·1^k + 2·(-1)^k

We verify this algebraic identity for k = 1,...,5.
-/

/-- Predicted trace from eigenvalue multiplicities. -/
def predictedTrace (k : Nat) : Int :=
  2 * (3 : Int) ^ k + 4 * (1 : Int) ^ k + 2 * ((-1 : Int) ^ k)

theorem predicted_trace_M1 : predictedTrace 1 = 8 := by native_decide
theorem predicted_trace_M2 : predictedTrace 2 = 24 := by native_decide
theorem predicted_trace_M3 : predictedTrace 3 = 56 := by native_decide
theorem predicted_trace_M4 : predictedTrace 4 = 168 := by native_decide
theorem predicted_trace_M5 : predictedTrace 5 = 488 := by native_decide

/-- The actual traces match the eigenvalue predictions for k = 1,...,5. -/
theorem traces_match_eigenvalue_formula :
    matTrace cayleyMatZ = predictedTrace 1 ∧
    matTrace (matPow cayleyMatZ 2) = predictedTrace 2 ∧
    matTrace (matPow cayleyMatZ 3) = predictedTrace 3 ∧
    matTrace (matPow cayleyMatZ 4) = predictedTrace 4 ∧
    matTrace (matPow cayleyMatZ 5) = predictedTrace 5 := by
  native_decide

end SpectralMoments

end CouretUnification.Core
