/-
# Logic/Doctrine.lean — Invariants doctrinaux du programme (v35.7)

## Statut

Niveau A. Aucun sorry. Aucune affirmation sur la zêta.

## Rôle

Ce fichier centralise :

  1. L'invariant `RHClaimed = false`, vérifié statiquement par `rfl`.
  2. Le journal des frottements d'API rencontrés au cours de la formalisation.
  3. Les conventions de marquage `[A]/[B]/[C]/[D]` utilisées par le programme.

Importé par tous les fichiers du noyau démonstratif (`Logic/`).

## Garantie

Le programme Couret-Unification, à toute version, satisfait :
  example : RHClaimed = false := rfl
Cette ligne ne ment pas. Elle dit simplement que ce paquet Lean ne revendique
nulle part la résolution de l'Hypothèse de Riemann.
-/

import CouretUnification.Meta.Layer

namespace CouretUnification.Logic

open CouretUnification.Meta

/-! ## Section 1 — Invariant RHClaimed -/

/-- Invariant doctrinal absolu : le programme ne revendique pas RH. -/
def RHClaimed : Bool := false

/-- Vérification statique de l'invariant. Cette ligne compile par `rfl` ou pas. -/
theorem rh_claimed_false : RHClaimed = false := rfl

/-! ## Section 2 — Journal des frottements d'API observés -/

/-- Typologie des frottements d'API rencontrés lors de la formalisation. -/
inductive ApiFriction where
  /-- Lean exige un témoin explicite de `Disjoint` pour `Finset.sum_union`. -/
  | disjointness_required
  /-- Le produit sur `insert p s` reste syntaxiquement muet ; il faut
      `Finset.prod_insert` pour exposer la multiplication algébrique. -/
  | silent_product
  /-- Le nommage des lemmes Mathlib évolue ; certains identifiants
      anciens (`Finset.insert_inj_of_not_mem`) ont disparu. -/
  | taxonomy_drift
  /-- `sum_powerset_insert` peut produire deux sommes séparées (cas a)
      ou une seule somme avec intégrande additive (cas b). -/
  | sum_powerset_insert_shape
  /-- `rw [Finset.sum_congr rfl ...]` peut buter sur l'unification ;
      la route robuste est un `have` intermédiaire avec `refine`. -/
  | sum_congr_unification
  deriving DecidableEq, Repr

/-- Description textuelle d'un frottement. -/
def ApiFriction.describe : ApiFriction → String
  | .disjointness_required =>
      "La décomposition d'une somme exige un témoin explicite de Disjoint."
  | .silent_product =>
      "Le produit sur `insert p s` doit être exposé via Finset.prod_insert."
  | .taxonomy_drift =>
      "Le nommage des lemmes Mathlib évolue avec l'API."
  | .sum_powerset_insert_shape =>
      "sum_powerset_insert peut produire deux sommes séparées ou une somme additive."
  | .sum_congr_unification =>
      "rw [sum_congr rfl ...] peut échouer ; passer par un `have` intermédiaire."

/-- Journal des frottements rencontrés dans `SquarefreeSupport.lean`. -/
def squarefree_support_friction_log : List ApiFriction :=
  [ .disjointness_required
  , .silent_product
  , .taxonomy_drift
  , .sum_powerset_insert_shape
  , .sum_congr_unification ]

/-! ## Section 3 — Conventions de marquage A/B/C/D -/

/-- Pour un fichier donné, sa couche dominante. Les éléments d'une autre
    couche dans le fichier doivent être explicitement étiquetés en commentaire. -/
def layer_marker : Layer → String
  | .A => "[A] formel prouvé"
  | .B => "[B] analytique conditionnel"
  | .C => "[C] empirique fort"
  | .D => "[D] spéculatif"

/-- Identité doctrinale de ce fichier. -/
def fileIdentity : FileIdentity := {
  filename := "Logic/Doctrine.lean"
  layer := .A
  status := .proved
  sorryCount := 0
  rhClaimed := false
}

example : fileIdentity.rhClaimed = false := rfl
example : RHClaimed = false := rh_claimed_false

end CouretUnification.Logic
