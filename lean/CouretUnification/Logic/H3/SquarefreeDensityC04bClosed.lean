/-
Couret-Unification — v38.5.11
# CouretUnification/Logic/H3/SquarefreeDensityC04bClosed.lean

## Rôle

Façade de promotion de C-04b.

Ce fichier importe la fermeture lab
`SquarefreeDensityAsymptotic.lean` et transforme le bridge conditionnel
public de `SquarefreeDensity.lean` en résultat prouvé.

## Statut

- Couche       : Logic / H3
- Front        : C-04b — densité squarefree
- RHClaimed    : false
- Sorry count  : 0

## Doctrine

Ce fichier ne prouve aucune assertion RH / Hilbert–Pólya.
Il promeut seulement la densité asymptotique classique des entiers
squarefree :
  squarefreeCount N / N → 6 / π².
-/

import CouretUnification.Logic.H3.SquarefreeDensityAsymptotic

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- Fermeture prouvée du bridge public C-04b de `SquarefreeDensity.lean`.

    Le bridge `SquarefreeAsymptoticDensityBridge` était conditionnel
    dans l'interface stable ; il est maintenant fourni par la fermeture
    lab `squarefree_asymptotic_density_six_over_pi_squared`. -/
theorem squarefreeAsymptoticDensityBridge_proved :
    SquarefreeAsymptoticDensityBridge := by
  unfold SquarefreeAsymptoticDensityBridge

  exact squarefree_asymptotic_density_six_over_pi_squared

/-- Version inconditionnelle du théorème public C-04b.

    Elle spécialise l'ancien consommateur conditionnel
    `squarefree_asymptotic_density` avec le bridge désormais prouvé. -/
theorem squarefree_asymptotic_density_unconditional :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density
    squarefreeAsymptoticDensityBridge_proved

/-- Alias de promotion : C-04b fermé dans la façade stable, RHClaimed = false. -/
theorem C04b_squarefree_density_promoted :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_unconditional

/-- Dossier partiel de fermeture : composante C-04b prouvée.

    C-04a reste séparée : la minoration effective `squarefreeCount_ge_half`
    n'est pas fermée ici. -/
def SquarefreeDensityC04bClosure : Prop :=
  SquarefreeAsymptoticDensityBridge

/-- Fermeture du dossier partiel C-04b. -/
theorem squarefreeDensityC04bClosure_proved :
    SquarefreeDensityC04bClosure :=
  squarefreeAsymptoticDensityBridge_proved

end CouretUnification.Logic.H3
