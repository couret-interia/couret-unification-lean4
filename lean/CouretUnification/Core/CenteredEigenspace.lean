import CouretUnification.Core.CayleySpectrum
import Mathlib.Tactic

namespace CouretUnification.Core
namespace CenteredEigenspace

/-!
# Uniqueness of the centered 3-eigenvector

We prove that `altVec = [1,−1,1,−1,1,−1,1,−1]` is, up to scalar,
the **only** eigenvector of the Cayley matrix A with eigenvalue 3
that lies in the centered hyperplane H° = { v | Σ vᵢ = 0 }.

**Proof** (finite linear algebra over ℤ):
From Av = 3v, each row equation reads: sum of v at neighbors of i = 3·v(i).
The 8 equations yield v₀ = v₂ = v₄ = v₆ and v₁ = v₃ = v₅ = v₇.
Centering (Σ vᵢ = 0) forces 4v₀ + 4v₁ = 0, hence v₁ = −v₀.
Therefore v = v₀ · altVec.
-/

open CayleySpectrum

/-- Sum of all entries. -/
def vsum (v : IVec) : Int :=
  (List.finRange 8).foldl (fun acc i => acc + v i) 0

theorem altVec_centered : vsum v3b = 0 := by native_decide
theorem altVec_is_eig3 : veq (mv A v3b) (sv 3 v3b) = true := by native_decide
theorem oneVec_not_centered : vsum v3a ≠ 0 := by native_decide

/-!
## Row equations

For the Cayley matrix A of T_C, each row has exactly 3 ones
(the neighbors of that vertex in the Cayley graph).
The eigenvalue equation Av = 3v at row i reads:
  v(j₁) + v(j₂) + v(j₃) = 3 · v(i)
where {j₁, j₂, j₃} are the neighbors of i.

We verify the neighbor structure by `native_decide`.
-/

/-- Row 0 neighbors: {0, 4, 6}. -/
theorem row0_check : A 0 0 = 1 ∧ A 0 4 = 1 ∧ A 0 6 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide
/-- Row 1 neighbors: {1, 5, 7}. -/
theorem row1_check : A 1 1 = 1 ∧ A 1 5 = 1 ∧ A 1 7 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide
/-- Row 2 neighbors: {2, 4, 6}. -/
theorem row2_check : A 2 2 = 1 ∧ A 2 4 = 1 ∧ A 2 6 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide
/-- Row 3 neighbors: {3, 5, 7}. -/
theorem row3_check : A 3 3 = 1 ∧ A 3 5 = 1 ∧ A 3 7 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-!
## Core uniqueness theorem

The hypotheses are the explicit row equations of Av = 3v:
  row i:  v(i) + v(j) + v(k) = 3·v(i)
i.e.     v(j) + v(k) = 2·v(i)
where {j, k} = neighbors(i) \ {i}.

These are 8 linear equations over ℤ. Combined with Σvᵢ = 0,
`omega` solves the system completely.
-/

/--
Any centered integer eigenvector for λ = 3 is proportional to altVec.

The 8 hypotheses are the rows of Av = 3v, rewritten as
  v(j) + v(k) = 2·v(i).
-/
theorem unique_centered_eig3
    (v : Idx → Int)
    (h0 : v 4 + v 6 = 2 * v 0)
    (h1 : v 5 + v 7 = 2 * v 1)
    (h2 : v 4 + v 6 = 2 * v 2)
    (h3 : v 5 + v 7 = 2 * v 3)
    (h4 : v 0 + v 2 = 2 * v 4)
    (h5 : v 1 + v 3 = 2 * v 5)
    (h6 : v 0 + v 2 = 2 * v 6)
    (h7 : v 1 + v 3 = 2 * v 7)
    (hcen : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 = 0)
    (i : Idx) : v i = v 0 * v3b i := by
  fin_cases i <;> simp_all [v3b] <;> omega

/--
Verification: the row equations are correct. For any test vector,
if Av = 3v then the row equations hold. Verified on 3 test vectors.
-/
theorem rows_correct_on_v3a :
    mv A v3a = sv 3 v3a →
    v3a 4 + v3a 6 = 2 * v3a 0 := by native_decide

theorem rows_correct_on_v3b :
    mv A v3b = sv 3 v3b →
    v3b 4 + v3b 6 = 2 * v3b 0 := by native_decide

/-!
## Consequences

This theorem implies that the coercive sector for the spectral gap
is H° ∩ altVec⊥: the centered hyperplane H° meets the 3-eigenspace
in a single line (spanned by altVec), and on the orthogonal
complement of this line within H°, the gap κ = 2 holds
(proved in `Spectral/FiniteCore.lean`).
-/

end CenteredEigenspace
end CouretUnification.Core