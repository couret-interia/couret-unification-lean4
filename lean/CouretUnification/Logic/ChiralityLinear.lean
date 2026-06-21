/-
Copyright (c) 2026 Couret-Unification Programme.

# Logic/ChiralityLinear.lean — Couche B / Réalisation matricielle de Ω₇

## Statut

Couche     : Logic / Diamond.
Sorry      : 0 sur les faits matriciels (antisymétrie, polynôme minimal,
             traces, vecteurs du noyau) ; 0 sorry sur la dérivation
             spectrale qui est présentée comme corollaire externe
             (à formaliser dans un fichier ChiralitySpectrum.lean séparé
             avec Mathlib.LinearAlgebra.Matrix.Charpoly).
Axiomes    : 0 additionnels.
RHClaimed  : false.

## Contexte

Ce fichier réalise explicitement, comme matrices 8×8 à coefficients
entiers, les objets abstraits de ChiralityFinite.lean :

  * P₇ comme matrice de permutation sur ℤ⁸
  * P₇⁻¹ = P₇ᵀ (pour une permutation)
  * Ω₇ = P₇ − P₇⁻¹ : opérateur chiral

Indexation de E par Fin 8 dans l'ordre croissant des résidus :

    index 0 → résidu  1       index 4 → résidu 17
    index 1 → résidu  7       index 5 → résidu 19
    index 2 → résidu 11       index 6 → résidu 23
    index 3 → résidu 13       index 7 → résidu 29

Sous cette indexation :

  * Orbite A (sous P₇) = indices {0, 1, 3, 5}, cycle 0→1→5→3→0
    = résidus {1, 7, 13, 19}
  * Orbite B (sous P₇) = indices {2, 4, 6, 7}, cycle 2→4→7→6→2
    = résidus {11, 17, 23, 29}

Tous les énoncés sont vérifiés par `native_decide` sur des matrices
entières de taille 8×8, sans aucune dépendance analytique.

  Note de nomenclature v38.4.20 :
    `ChiralityFinite.Omega7Fun` désigne l'opérateur fonctionnel abstrait
    sur les fonctions `ZMod 30 → ℂ`.

    `ChiralityLinear.Omega7` désigne sa réalisation matricielle 8×8 dans
    l'indexation explicite de E.

    Les deux objets ne sont pas synonymes Lean : l'un est fonctionnel,
    l'autre matriciel. Le fichier présent formalise seulement la couche B.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

namespace CouretUnification.ChiralityLinear

open Matrix

/-! ## Section 1 — Matrices P₇ et P₇⁻¹ -/

/-- Matrice de permutation P₇ agissant sur ℤ⁸.
    Convention : (P₇)[i][j] = 1 ⟺ σ(j) = i, où σ est la permutation
    multiplicative induite par la multiplication par 7 mod 30.

    Permutation σ : 0↦1, 1↦5, 2↦4, 3↦0, 4↦7, 5↦3, 6↦2, 7↦6. -/
def P7 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0]

/-- L'inverse d'une matrice de permutation est sa transposée. -/
def P7inv : Matrix (Fin 8) (Fin 8) ℤ := P7.transpose

/-- P₇ · P₇⁻¹ = I. -/
theorem P7_mul_P7inv : P7 * P7inv = 1 := by native_decide

/-- P₇⁻¹ · P₇ = I. -/
theorem P7inv_mul_P7 : P7inv * P7 = 1 := by native_decide

/-- P₇⁴ = I (ordre 4 dans le groupe des permutations). -/
theorem P7_order_four : P7 * P7 * P7 * P7 = 1 := by native_decide

/-! ## Section 2 — Opérateur chiral Ω₇ -/

/-- L'opérateur chiral canonique : Ω₇ = P₇ − P₇⁻¹.
    Mesure l'écart entre transport direct et transport inverse. -/
def Omega7 : Matrix (Fin 8) (Fin 8) ℤ := P7 - P7inv

/-- **Forme explicite de Ω₇** (matrice entière à 16 coefficients non nuls,
    chacun valant ±1, répartis en 2 par ligne et 2 par colonne). -/
theorem Omega7_eq :
    Omega7 =
      !![ 0, -1,  0,  1,  0,  0,  0,  0;
          1,  0,  0,  0,  0, -1,  0,  0;
          0,  0,  0,  0, -1,  0,  1,  0;
         -1,  0,  0,  0,  0,  1,  0,  0;
          0,  0,  1,  0,  0,  0,  0, -1;
          0,  1,  0, -1,  0,  0,  0,  0;
          0,  0, -1,  0,  0,  0,  0,  1;
          0,  0,  0,  0,  1,  0, -1,  0] := by
  native_decide

/-- **Antisymétrie** : Ω₇ᵀ = −Ω₇. -/
theorem Omega7_antisymmetric : Omega7.transpose = -Omega7 := by native_decide

/-- Trace nulle (conséquence immédiate de l'antisymétrie). -/
theorem trace_Omega7 : Omega7.trace = 0 := by native_decide

/-! ## Section 3 — Polynôme minimal : Ω₇³ = −4·Ω₇ -/

/-- **Identité fondamentale** (polynôme minimal) :

      Ω₇³ + 4·Ω₇ = 0.

    Autrement dit, Ω₇ annule le polynôme p(x) = x³ + 4x = x(x² + 4).
    Sur ℂ, p(x) = x(x − 2i)(x + 2i), qui a trois racines simples.
    Ω₇ est donc diagonalisable et son spectre est inclus dans {0, +2i, −2i}. -/
theorem Omega7_cubed_plus_four :
    Omega7 * Omega7 * Omega7 + (4 : ℤ) • Omega7 = 0 := by
  native_decide

/-- Reformulation factorisée : Ω₇ · (Ω₇² + 4·I) = 0. -/
theorem Omega7_factored :
    Omega7 * (Omega7 * Omega7 + (4 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ)) = 0 := by
  native_decide

/-- **Trace de Ω₇²** : compte les multiplicités via
    trace(Ω₇²) = m₊·(2i)² + m₋·(−2i)² = −4(m₊ + m₋). -/
theorem trace_Omega7_squared : (Omega7 * Omega7).trace = -16 := by
  native_decide

/-! ## Section 4 — Noyau de Ω₇ : quatre vecteurs symétriques indépendants

Les deux orbites, chacune munie de sa somme (eigenvalue +1 de P₇|_orb)
et de son vecteur alterné (eigenvalue −1 de P₇|_orb), fournissent
quatre vecteurs réels annulés par Ω₇.
-/

/-- Vecteur indicateur de l'orbite A : {1, 7, 13, 19} = indices {0, 1, 3, 5}.
    Eigenvalue +1 de P₇ restreint à orbite A. -/
def vA_plus : Fin 8 → ℤ := ![1, 1, 0, 1, 0, 1, 0, 0]

/-- Vecteur alterné sur l'orbite A : cycle 0→1→5→3 avec signes (+,−,+,−).
    Eigenvalue −1 de P₇ restreint à orbite A. -/
def vA_minus : Fin 8 → ℤ := ![1, -1, 0, -1, 0, 1, 0, 0]

/-- Vecteur indicateur de l'orbite B : {11, 17, 23, 29} = indices {2, 4, 6, 7}.
    Eigenvalue +1 de P₇ restreint à orbite B. -/
def vB_plus : Fin 8 → ℤ := ![0, 0, 1, 0, 1, 0, 1, 1]

/-- Vecteur alterné sur l'orbite B : cycle 2→4→7→6 avec signes (+,−,+,−).
    Eigenvalue −1 de P₇ restreint à orbite B. -/
def vB_minus : Fin 8 → ℤ := ![0, 0, 1, 0, -1, 0, -1, 1]

/-- vA_plus ∈ ker(Ω₇). -/
theorem Omega7_kills_vA_plus : Omega7.mulVec vA_plus = 0 := by native_decide

/-- vA_minus ∈ ker(Ω₇). -/
theorem Omega7_kills_vA_minus : Omega7.mulVec vA_minus = 0 := by native_decide

/-- vB_plus ∈ ker(Ω₇). -/
theorem Omega7_kills_vB_plus : Omega7.mulVec vB_plus = 0 := by native_decide

/-- vB_minus ∈ ker(Ω₇). -/
theorem Omega7_kills_vB_minus : Omega7.mulVec vB_minus = 0 := by native_decide

/-! ## Section 5 — Action sur les vecteurs non symétriques (image)

Témoin que Ω₇ n'est pas identiquement nul : il agit non trivialement
sur les vecteurs « transverses » aux orbites symétriques.
-/

/-- Vecteur test : premier vecteur de base e₀. -/
def e0 : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0]

/-- Ω₇ · e₀ ≠ 0 : on a Ω₇·e₀ = e₁ − e₃ (conforme à la lecture :
    le transport direct envoie 1 sur 7, l'inverse sur 13). -/
theorem Omega7_e0 : Omega7.mulVec e0 = ![0, 1, 0, -1, 0, 0, 0, 0] := by
  native_decide

/-! ## Section 6 — Synthèse spectrale (corollaire externe)

On rassemble les faits **prouvés** ci-dessus :

  (L1) Ω₇ᵀ = −Ω₇                                  [Omega7_antisymmetric]
  (L2) Ω₇³ + 4·Ω₇ = 0                              [Omega7_cubed_plus_four]
  (L3) trace(Ω₇) = 0                               [trace_Omega7]
  (L4) trace(Ω₇²) = −16                            [trace_Omega7_squared]
  (L5) 4 vecteurs réels indép. dans ker(Ω₇)        [Omega7_kills_v{A,B}_{plus,minus}]

### Dérivation du spectre

Par (L2), le polynôme minimal de Ω₇ sur ℂ divise
  p(x) = x(x² + 4) = x(x − 2i)(x + 2i).
Les trois racines 0, +2i, −2i sont simples, donc **Ω₇ est diagonalisable**
et ses valeurs propres appartiennent à {0, +2i, −2i}.

Soient m₀, m₊, m₋ les multiplicités des trois valeurs propres.

  * Par (L1), Ω₇ est antisymétrique réelle : ses valeurs propres non
    nulles sont imaginaires pures et apparaissent en paires conjuguées.
    Donc **m₊ = m₋**.
  * Par (L5), il existe 4 vecteurs réels linéairement indépendants dans
    ker(Ω₇). Donc **m₀ ≥ 4**.
  * Par (L4) :
      −16 = trace(Ω₇²) = m₀·0² + m₊·(2i)² + m₋·(−2i)² = −4(m₊ + m₋).
    Donc **m₊ + m₋ = 4**, d'où **m₊ = m₋ = 2**.
  * m₀ + m₊ + m₋ = 8 donne **m₀ = 4**.

### Conclusion

    Spec(Ω₇) = { 0, 0, 0, 0, +2i, +2i, −2i, −2i }.

    rang(Ω₇) = 4.
    ker(Ω₇)  = Vect_ℝ ⟨ vA_plus, vA_minus, vB_plus, vB_minus ⟩.
    Im(Ω₇)   = sous-espace antisymétrique de dimension 4,
               porteur de la **composante chirale orientée**.

L'opérateur Ω₇ ne voit pas la composante « symétrique » du simplexe ;
il isole exactement les modes qui distinguent le transport direct
du transport inverse le long des deux 4-cycles.

La formalisation complète de l'implication « (L1)–(L5) ⟹ spectre »
appartient à un fichier successeur ChiralitySpectrum.lean s'appuyant
sur `Mathlib.LinearAlgebra.Matrix.Charpoly` et sur le théorème de
diagonalisation des matrices antisymétriques réelles.

## Section 7 — Devise

  La chiralité transporte la cohérence ;
  la métastabilité verrouille le défaut qui la rend visible.

-/

/-! ## Section 8 — Invariant doctrinal -/

/-- Invariant constitutionnel : ce fichier ne prétend rien sur RH. -/
def RHClaimed : Bool := false

example : RHClaimed = false := rfl

end CouretUnification.ChiralityLinear

