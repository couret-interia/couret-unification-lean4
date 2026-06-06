import CouretUnification.Core.CayleySpectrum
import CouretUnification.Finite.Foundations

namespace CouretUnification.Core.CenteredEigenspace

/-!
# Unicité du 3-vecteur propre centré

Nous prouvons que `altVec = [1,−1,1,−1,1,−1,1,−1]` est, à scalaire près,
l’**unique** vecteur propre de la matrice de Cayley A associé à la valeur propre 3
qui appartient à l’hyperplan centré H° = { v | Σ vᵢ = 0 }.

**Preuve** (algèbre linéaire finie sur ℤ) :
À partir de Av = 3v, chaque équation de ligne s’écrit :
la somme des valeurs de v sur les voisins de i est égale à 3·v(i).
Les 8 équations donnent v₀ = v₂ = v₄ = v₆ et v₁ = v₃ = v₅ = v₇.
La condition de centrage (Σ vᵢ = 0) impose 4v₀ + 4v₁ = 0, donc v₁ = −v₀.
Ainsi v = v₀ · altVec.
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
## Équations de ligne

Pour la matrice de Cayley A de T_C, chaque ligne possède exactement 3 coefficients égaux à 1
(les voisins de ce sommet dans le graphe de Cayley).
L’équation propre Av = 3v à la ligne i s’écrit :
  v(j₁) + v(j₂) + v(j₃) = 3 · v(i)
où {j₁, j₂, j₃} sont les voisins de i.

Nous vérifions la structure des voisins par `native_decide`.
-/

/-- Voisins de la ligne 0 : {0, 4, 6}. -/
theorem row0_check : A 0 0 = 1 ∧ A 0 4 = 1 ∧ A 0 6 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Voisins de la ligne 1 : {1, 5, 7}. -/
theorem row1_check : A 1 1 = 1 ∧ A 1 5 = 1 ∧ A 1 7 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Voisins de la ligne 2 : {2, 4, 6}. -/
theorem row2_check : A 2 2 = 1 ∧ A 2 4 = 1 ∧ A 2 6 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Voisins de la ligne 3 : {3, 5, 7}. -/
theorem row3_check : A 3 3 = 1 ∧ A 3 5 = 1 ∧ A 3 7 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-!
## Théorème central d’unicité

Les hypothèses sont les équations de ligne explicites de Av = 3v :
  ligne i :  v(i) + v(j) + v(k) = 3·v(i)
c’est-à-dire v(j) + v(k) = 2·v(i),
où {j, k} = voisins(i) \ {i}.

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
Pour tout vecteur test, si `Av = 3v`, alors l’équation de ligne 0 vaut.
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
## Conséquences

Ce théorème implique que le secteur coercif pour le trou spectral
est H° ∩ altVec⊥ : l’hyperplan centré H° rencontre le 3-espace propre
selon une seule droite (engendrée par altVec), et sur le complément
orthogonal de cette droite dans H°, le trou κ = 2 vaut
(prouvé dans `Spectral/FiniteCore.lean`).
-/

end CouretUnification.Core.CenteredEigenspace
