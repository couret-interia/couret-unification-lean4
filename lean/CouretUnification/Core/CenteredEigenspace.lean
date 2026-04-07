import CouretUnification.Core.CayleySpectrum
import Mathlib.Tactic

namespace CouretUnification.Core
namespace CenteredEigenspace

/-!
# Uniqueness of the centered 3-eigenvector

We prove that `altVec = [1,−1,1,−1,1,−1,1,−1]` is, up to scalar,
the **only** eigenvector of the Cayley matrix A with eigenvalue 3
that lies in the centered hyperplane H° = { v | Σ vᵢ = 0 }.

**Proof sketch** (finite linear algebra over ℤ):
From (A − 3I)v = 0, the 8 row equations yield:
  v₀ = v₂ = v₄ = v₆   and   v₁ = v₃ = v₅ = v₇.
The centering condition Σ vᵢ = 0 then forces v₁ = −v₀.
Therefore v = v₀ · altVec.
-/

open CayleySpectrum

/-- Sum of all entries. -/
def vsum (v : IVec) : Int :=
  (List.finRange 8).foldl (fun acc i => acc + v i) 0

/-- altVec is centered: Σ altVec_i = 0. -/
theorem altVec_centered : vsum v3b = 0 := by native_decide

/-- altVec is a 3-eigenvector. -/
theorem altVec_is_eig3 : veq (mv A v3b) (sv 3 v3b) = true := by native_decide

/-- The constant vector is NOT centered. -/
theorem oneVec_not_centered : vsum v3a ≠ 0 := by native_decide

/-!
## Core uniqueness theorem

The hypotheses are the 8 explicit row equations of (A − 3I)v = 0
plus the centering condition. These are pure linear constraints
over ℤ, and `omega` closes each sub-goal.
-/

/--
Any centered integer eigenvector for λ = 3 is proportional to altVec.

Hypotheses h₀..h₇ are the rows of (A − 3I)v = 0, unrolled:
  row i: Σⱼ (A[i,j] − 3·δ_{ij}) · v[j] = 0.
-/
theorem centered_eig3_proportional (v : Idx → Int)
    (h0 : v 4 + v 6 = 2 * v 0)
    (h1 : v 5 + v 7 = 2 * v 1)
    (h2 : v 4 + v 6 = 2 * v 2)
    (h3 : v 5 + v 7 = 2 * v 3)
    (h4 : v 0 + v 2 = 2 * v 4)
    (h5 : v 1 + v 3 = 2 * v 5)
    (h6 : v 0 + v 2 = 2 * v 6)
    (h7 : v 1 + v 3 = 2 * v 7)
    (hcen : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 = 0) :
    v 1 = -(v 0) ∧
    v 2 = v 0 ∧
    v 3 = -(v 0) ∧
    v 4 = v 0 ∧
    v 5 = -(v 0) ∧
    v 6 = v 0 ∧
    v 7 = -(v 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/--
Corollary: the centered 3-eigenspace is exactly ℤ · altVec.
For each coordinate i, v(i) = v(0) · altVec(i).
-/
theorem centered_eig3_eq_scalar_altVec (v : Idx → Int)
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
  have ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    centered_eig3_proportional v h0 h1 h2 h3 h4 h5 h6 h7 hcen
  fin_cases i <;> simp_all [v3b] <;> omega

/-!
## Bridge: matrix equation → row equations

We verify that (A − 3I)v = 0, stated as `mv A v = sv 3 v`,
implies each of the 8 row equations used above.
This is stated as a structure for clean extraction.
-/

/-- The 8 row equations extracted from (A-3I)v = 0. -/
structure RowEquations (v : IVec) : Prop where
  eq0 : v 4 + v 6 = 2 * v 0
  eq1 : v 5 + v 7 = 2 * v 1
  eq2 : v 4 + v 6 = 2 * v 2
  eq3 : v 5 + v 7 = 2 * v 3
  eq4 : v 0 + v 2 = 2 * v 4
  eq5 : v 1 + v 3 = 2 * v 5
  eq6 : v 0 + v 2 = 2 * v 6
  eq7 : v 1 + v 3 = 2 * v 7

/--
If Av = 3v (stated pointwise), then the explicit row equations hold.
Each is proved by expanding the matrix-vector product at one row.
-/
theorem matrix_eig3_implies_rows (v : IVec)
    (h : ∀ i : Idx, mv A v i = sv 3 v i) : RowEquations v := by
  constructor
  all_goals (simp only [mv, sv, A, List.finRange, List.foldl, List.map] at h; omega)

/--
**Main theorem (packaged):**
If v is an integer vector with Av = 3v and Σvᵢ = 0,
then v = v₀ · altVec.
-/
theorem unique_centered_eig3 (v : IVec)
    (hEig : ∀ i : Idx, mv A v i = sv 3 v i)
    (hCen : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 = 0)
    (i : Idx) : v i = v 0 * v3b i := by
  have rows := matrix_eig3_implies_rows v hEig
  exact centered_eig3_eq_scalar_altVec v
    rows.eq0 rows.eq1 rows.eq2 rows.eq3
    rows.eq4 rows.eq5 rows.eq6 rows.eq7
    hCen i

/-!
## Consequences for the coercive gap

This theorem justifies why the coercive sector must be H° ∩ altVec⊥:
the centered hyperplane H° contains exactly one direction in the
3-eigenspace (namely altVec), and the coercive gap κ = 2 holds
on the orthogonal complement of this direction within H°.
-/

end CenteredEigenspace
end CouretUnification.Core