/-
# Empirical/SophieGermainTransitions.lean — Interprétation statistique (v35.7)

## Statut épistémique

  - Couche : Empirical
  - Statut : [C] empirical — les chiffres χ², résidus standardisés et
             p-values sont des **données mesurées**, non des théorèmes.
  - sorryCount : 0
  - RHClaimed = false
  - **Ce fichier n'est jamais importé par Logic/.**

## Doctrine

Ce fichier encode comme données Lean les résultats du calcul χ² mené hors
de Lean (sympy, Python) sur les transitions entre nombres premiers de
Sophie Germain modulo 30, pour p ≤ 10⁷.

Les valeurs encodées ne sont **pas** prouvées par Lean. Elles sont importées
comme constantes flottantes (encodées en ℝ) pour permettre :

  - leur consultation depuis le programme,
  - leur comparaison avec des seuils décisionnels,
  - leur traçabilité au sein du dépôt Lean.

La matrice combinatoire elle-même est traitée à part dans
`Logic/SophieGermainMatrix.lean` (niveau A, prouvée par `decide`).

## Lecture correcte

  Les données rejettent **très fortement** les modèles nuls testés :
    - modèle uniforme (équiprobabilité 1/3 par cellule) : χ² ≈ 242
    - modèle d'indépendance Hardy-Littlewood conditionnelle : χ² ≈ 242
  sur 4 degrés de liberté, p < 10⁻⁴⁹.

  Cette régularité empirique forte suggère une mémoire de transition non
  triviale entre classes de résidus, mais **ne constitue pas** une
  démonstration de loi déterministe globale.
-/

import CouretUnification.Meta.Layer
import Mathlib.Data.Real.Basic

namespace CouretUnification
namespace Empirical
namespace SophieGermainTransitions

open CouretUnification.Meta

/-! ## Section 1 — Métadonnées de la mesure -/

/-- Borne supérieure des nombres premiers considérés dans le recensement. -/
def measurement_upper_bound : ℕ := 10_000_000

/-- Nombre total de transitions Sophie Germain observées. -/
def total_transitions_observed : ℕ := 30_653

/-! ## Section 2 — Statistiques χ² -/

/-- Rapport χ² complet pour les transitions Sophie Germain mod 30. -/
structure ChiSquareReport where
  /-- χ² contre le modèle d'uniformité simple (équiprobabilité). -/
  chi2_uniform : ℝ
  /-- χ² contre le modèle d'indépendance Hardy-Littlewood. -/
  chi2_HL : ℝ
  /-- Degrés de liberté. -/
  degrees_of_freedom : ℕ
  /-- Borne supérieure de la p-value associée à χ²_HL. -/
  p_value_upper_bound : ℝ

/-- Rapport effectivement mesuré sur le crible p ≤ 10⁷. -/
def transition_report : ChiSquareReport := {
  chi2_uniform := 242.45
  chi2_HL := 241.68
  degrees_of_freedom := 4
  p_value_upper_bound := 1e-49
}

/-! ## Section 3 — Résidus diagonaux standardisés -/

/-- Résidus standardisés sur la diagonale (déficit observé / σ attendu).

    Tous négatifs et de magnitude > 6, ce qui est la signature de la
    « répulsion diagonale » : les transitions intra-classe sont
    significativement moins fréquentes que ne le prédit le modèle nul. -/
structure DiagonalResidualsReport where
  /-- Résidu standardisé pour la transition 11 → 11. -/
  resid_11_to_11 : ℝ
  /-- Résidu standardisé pour la transition 23 → 23. -/
  resid_23_to_23 : ℝ
  /-- Résidu standardisé pour la transition 29 → 29. -/
  resid_29_to_29 : ℝ
  /-- Fraction de χ²_HL provenant de la diagonale. -/
  diagonal_chi2_fraction : ℝ

def diagonal_residuals : DiagonalResidualsReport := {
  resid_11_to_11 := -6.11
  resid_23_to_23 := -6.51
  resid_29_to_29 := -7.29
  diagonal_chi2_fraction := 0.55
}

/-! ## Section 4 — Verdict empirique -/

/-- Verdict d'un test de rejet de modèle nul. -/
inductive RejectionVerdict where
  | not_rejected
  | weakly_rejected
  | strongly_rejected
  | very_strongly_rejected
  deriving DecidableEq, Repr

/-- Verdict du test contre Hardy-Littlewood : rejet très fort, p < 10⁻⁴⁹. -/
def hl_verdict : RejectionVerdict := .very_strongly_rejected

/-- Verdict du test contre l'uniformité : rejet très fort. -/
def uniform_verdict : RejectionVerdict := .very_strongly_rejected

/-! ## Section 5 — Énoncé descriptif (Statement empirique) -/

def empirical_statement : Statement := {
  title := "Transitions Sophie Germain mod 30 — rejet HL"
  layer := .C
  status := .empirical
  content :=
    "χ²_HL = 241.68 sur 4 ddl, p < 10⁻⁴⁹. Résidus diagonaux entre " ++
    "-6 σ et -7 σ. Lecture : régularité empirique forte (mémoire de " ++
    "transition), non démonstration formelle d'une loi globale."
}

/-! ## Section 6 — Identité doctrinale -/

def fileIdentity : FileIdentity := {
  filename := "Empirical/SophieGermainTransitions.lean"
  layer := .C
  status := .empirical
  sorryCount := 0
  rhClaimed := false
}

example : fileIdentity.rhClaimed = false := rfl
example : fileIdentity.layer = .C := rfl

/-! ## Notes

1. La matrice combinatoire elle-même (avec sommes lignes/colonnes/total et
   théorème de déficit diagonal prouvés par `decide`) est dans
   `Logic/SophieGermainMatrix.lean`. Cette séparation est délibérée :

     - matrice + invariants combinatoires    → niveau A
     - interprétation statistique χ²/p-value → niveau C

2. Aucun fichier de `Logic/` n'importe ce fichier. La couche empirique
   peut consulter Meta, mais la couche démonstrative ne dépend jamais
   d'une donnée numérique externe.

3. Indépendance de RH : aucun élément de ce fichier ne dépend ni
   ne contraint RH.
-/

end SophieGermainTransitions
end Empirical
end CouretUnification
