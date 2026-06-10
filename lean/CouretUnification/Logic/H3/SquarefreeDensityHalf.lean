/-
Couret-Unification — v38.5.12-lab
# CouretUnification/Logic/H3/SquarefreeDensityHalf.lean

## Rôle

Laboratoire de fermeture de C-04a :
  pour N ≥ 176, squarefreeCount N ≥ N / 2.

Ce premier fichier ne ferme pas encore la borne effective.
Il réduit C-04a à une majoration équivalente du nombre d'entiers
non-squarefree.

## Statut

- Couche      : Logic / H3
- Front       : C-04a — minoration effective squarefree
- C-04b       : déjà fermé via SquarefreeDensityC04bClosed
- RHClaimed   : false
- Sorry count : 0
-/

import CouretUnification.Logic.H3.SquarefreeDensityC04bClosed

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- Nombre d'entiers non-squarefree dans `[1, N]`. -/
def nonSquarefreeCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => ¬ Squarefree n)).card

/-- Décomposition exacte de `[1, N]` en squarefree et non-squarefree. -/
theorem squarefreeCount_add_nonSquarefreeCount
    (N : ℕ) :
    squarefreeCount N + nonSquarefreeCount N = N := by
  unfold squarefreeCount
  unfold nonSquarefreeCount

  calc
    ((Finset.Icc 1 N).filter Squarefree).card
        + ((Finset.Icc 1 N).filter (fun n => ¬ Squarefree n)).card
        =
      (Finset.Icc 1 N).card := by
        exact Finset.card_filter_add_card_filter_not
          (s := Finset.Icc 1 N)
          (p := Squarefree)
    _ = N := by
        rw [Nat.card_Icc]
        omega

/-- Bridge effectif équivalent à C-04a :
    au-delà de `176`, au plus la moitié des entiers `≤ N`
    sont non-squarefree. -/
def NonSquarefreeCountLeHalfBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      (nonSquarefreeCount N : ℚ) ≤ (N : ℚ) / 2

/-- Si les non-squarefree sont au plus `N/2`, alors les squarefree
    sont au moins `N/2`. -/
theorem squarefreeCountGeHalfBridge_of_nonSquarefree_le_half
    (H : NonSquarefreeCountLeHalfBridge) :
    SquarefreeCountGeHalfBridge := by
  unfold SquarefreeCountGeHalfBridge
  unfold NonSquarefreeCountLeHalfBridge at H

  intro N hN

  have h_non : (nonSquarefreeCount N : ℚ) ≤ (N : ℚ) / 2 :=
    H hN

  have hsplit_nat :
      squarefreeCount N + nonSquarefreeCount N = N :=
    squarefreeCount_add_nonSquarefreeCount N

  have hsplit_rat :
      (squarefreeCount N : ℚ) + (nonSquarefreeCount N : ℚ)
        =
      (N : ℚ) := by
    norm_num [← Nat.cast_add, hsplit_nat]

  linarith

/-- Version consommable de C-04a sous la seule borne effective
    sur les non-squarefree. -/
theorem squarefreeCount_ge_half_of_nonSquarefree_le_half
    (H : NonSquarefreeCountLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half
    (squarefreeCountGeHalfBridge_of_nonSquarefree_le_half H)
    hN

end CouretUnification.Logic.H3
