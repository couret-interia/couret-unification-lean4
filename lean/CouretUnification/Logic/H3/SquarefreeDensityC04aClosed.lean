/-
Couret-Unification — v38.5.12
# CouretUnification/Logic/H3/SquarefreeDensityC04aClosed.lean

## Rôle

Façade de promotion de C-04a.

Ce fichier importe le laboratoire `SquarefreeDensityHalf.lean`
et transforme le bridge effectif public de `SquarefreeDensity.lean`
en résultat prouvé.

## Statut

- Couche       : Logic / H3
- Front        : C-04a — minoration effective squarefree
- C-04b        : déjà fermé via SquarefreeDensityC04bClosed
- RHClaimed    : false
- Sorry count  : 0

## Doctrine

Ce fichier ne prouve aucune assertion RH / Hilbert–Pólya.
Il promeut seulement la minoration effective classique :

  pour N ≥ 176, squarefreeCount N ≥ N / 2.
-/

import CouretUnification.Logic.H3.SquarefreeDensityHalf

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- Fermeture prouvée du bridge public C-04a de `SquarefreeDensity.lean`.

    Le bridge `SquarefreeCountGeHalfBridge` était conditionnel
    dans l'interface stable ; il est maintenant fourni par la fermeture
    effective du laboratoire `SquarefreeDensityHalf`. -/
theorem squarefreeCountGeHalfBridge_promoted :
    SquarefreeCountGeHalfBridge :=
  squarefreeCountGeHalfBridge_proved

/-- Version inconditionnelle du théorème public C-04a.

    Elle spécialise l'ancien consommateur conditionnel
    `squarefreeCount_ge_half` avec le bridge désormais prouvé. -/
theorem squarefreeCount_ge_half_unconditional
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half
    squarefreeCountGeHalfBridge_promoted
    hN

/-- Alias de promotion : C-04a fermé dans la façade stable, RHClaimed = false. -/
theorem C04a_squarefree_half_promoted
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_unconditional hN

/-- Dossier de fermeture C-04a. -/
def SquarefreeDensityC04aClosure : Prop :=
  SquarefreeCountGeHalfBridge

/-- Fermeture du dossier C-04a. -/
theorem squarefreeDensityC04aClosure_proved :
    SquarefreeDensityC04aClosure :=
  squarefreeCountGeHalfBridge_promoted

end CouretUnification.Logic.H3
