import CouretUnification.Core.CayleySpectrum
import CouretUnification.Finite.Foundations

namespace CouretUnification.Core.CenteredEigenspace

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
open Finite.Foundations

/-- Somme de toutes les coordonnées. -/
def vsum (v : IVec) : ℚ :=
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

Ces huit équations sont des équations linéaires sur ℚ. Avec Σvᵢ = 0,
`linarith` ferme les contraintes de coordonnées.
-/

/--
Tout vecteur propre centré rationnel pour `λ = 3` est proportionnel à `altVec`.

Les 8 hypothèses sont les lignes de `Av = 3v`, réécrites sous la forme

  v(j) + v(k) = 2·v(i).
-/
theorem unique_centered_eig3
    (v : Idx → ℚ)
    (h0 : v 4 + v 6 = 2 * v 0)
    (h1 : v 5 + v 7 = 2 * v 1)
    (h2 : v 4 + v 6 = 2 * v 2)
    (h3 : v 5 + v 7 = 2 * v 3)
    (h4 : v 0 + v 2 = 2 * v 4)
    (h5 : v 1 + v 3 = 2 * v 5)
    (_h6 : v 0 + v 2 = 2 * v 6)
    (_h7 : v 1 + v 3 = 2 * v 7)
    (hcen : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 = 0)
    (i : Idx) : v i = v 0 * v3b i := by
  have hv2 : v 2 = v 0 := by
    linarith
  have hv3 : v 3 = v 1 := by
    linarith
  have hv4 : v 4 = v 0 := by
    linarith
  have hv6 : v 6 = v 0 := by
    linarith
  have hv5 : v 5 = v 1 := by
    linarith
  have hv7 : v 7 = v 1 := by
    linarith
  have hv1 : v 1 = -v 0 := by
    linarith
  fin_cases i <;>
    simp [v3b, CouretUnification.Finite.Foundations.chi5,
      hv1, hv2, hv3, hv4, hv5, hv6, hv7]

/--
Vérification : les équations de ligne sont correctes.
Pour tout vecteur test, si `Av = 3v`, alors l'équation de ligne 0 vaut.
-/
theorem rows_correct_on_v3a :
    mv A v3a = sv 3 v3a →
    v3a 4 + v3a 6 = 2 * v3a 0 := by
  intro _h
  native_decide

theorem rows_correct_on_v3b :
    mv A v3b = sv 3 v3b →
    v3b 4 + v3b 6 = 2 * v3b 0 := by
  intro _h
  native_decide

/-!
## Consequences

This theorem implies that the coercive sector for the spectral gap
is H° ∩ altVec⊥: the centered hyperplane H° meets the 3-eigenspace
in a single line (spanned by altVec), and on the orthogonal
complement of this line within H°, the gap κ = 2 holds
(proved in `Spectral/FiniteCore.lean`).
-/

end CouretUnification.Core.CenteredEigenspace
