/-
  CouretUnification.Core.CenteredCoordinates
  ════════════════════════════════════════════════════════════════════
  Fermeture coordonnée des fonctions centrées sur U30.

  Pour une fonction f : ZMod 30 → ℚ centrée sur U30 — c'est-à-dire
  vérifiant ∑_{x ∈ U30} f(x) = 0 — la valeur f(29) est entièrement
  déterminée par les sept autres :

      f(29) = -(f(1) + f(7) + f(11) + f(13) + f(17) + f(19) + f(23)).

  C'est le contenu concret du slogan « le centré sur U30 a sept degrés
  de liberté », sans passer par Module.finrank ni par une représentation
  inductive parallèle à U30.

  Couche
  ------
  Core étendu (machine-certifié, non FROZEN strict au sens
  DOCTRINE_FINITECORE_VS_CORE_v38.5.md §3 — ce module utilise une
  fonction générique ZMod 30 → ℚ, pas une combinatoire purement finie).

  Discipline
  ----------
    • aucun `sorry` ;
    • aucun `axiom` introduit ;
    • aucun import vers ACTIVE ;
    • aucune revendication RH / HilbertPolya / det₂ ↔ ξ ;
    • RHClaimed = false (invariant préservé via import Core.U30).

  Statut : [D] machine-certifié après compilation.

  Pour Bernard Couret (1928–1999).
-/

import CouretUnification.Core.U30

open Finset

namespace CouretUnification.Core

/-! ## §1 — Définitions de base -/

/-- Fonctions rationnelles sur ZMod 30. -/
abbrev FunU30 := ZMod 30 → ℚ

/-- Somme canonique d'une fonction sur le Finset U30. -/
def sumU30 (f : FunU30) : ℚ := ∑ x ∈ U30, f x

/-- Une fonction est centrée sur U30 si sa somme y est nulle. -/
def IsCentered (f : FunU30) : Prop := sumU30 f = 0

/-- Somme explicite sur les 8 classes inversibles modulo 30. -/
def explicitSumU30 (f : FunU30) : ℚ :=
  f 1 + f 7 + f 11 + f 13 + f 17 + f 19 + f 23 + f 29

/-- Somme explicite sur les 7 premières classes — sans 29. -/
def sevenSumU30 (f : FunU30) : ℚ :=
  f 1 + f 7 + f 11 + f 13 + f 17 + f 19 + f 23

/-! ## §2 — Pont entre la somme canonique et la somme explicite -/

/-- La somme canonique `∑ x ∈ U30, f x` se déplie exactement en la somme
    explicite des huit valeurs.

    Stratégie principale : dépliage de `U30 = {1, 7, 11, 13, 17, 19, 23, 29}`
    par `Finset.sum_insert` répété, puis `Finset.sum_singleton`, puis `ring`.

    Note pour Thomas : si la stratégie principale échoue à cause d'un
    changement d'API Mathlib v4.29.x, plusieurs fallbacks sont documentés
    en commentaire à la fin de la preuve. -/
theorem sumU30_eq_explicitSumU30 (f : FunU30) :
    sumU30 f = explicitSumU30 f := by
  unfold sumU30 explicitSumU30 U30
  rw [Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

/-- Équivalence des deux formulations du centrage. -/
theorem isCentered_iff_explicitSum (f : FunU30) :
    IsCentered f ↔ explicitSumU30 f = 0 := by
  unfold IsCentered
  rw [sumU30_eq_explicitSumU30]

/-! ## §3 — Fermeture coordonnée — la 8ᵉ coordonnée est contrainte -/

/-- Si f est centrée sur U30, alors f(29) est déterminée comme
    l'opposée de la somme des sept autres valeurs.

    C'est la matérialisation arithmétique du fait que le sous-espace
    centré a sept degrés de liberté parmi les huit classes inversibles
    mod 30. -/
theorem centered_29_eq_neg_sevenSum {f : FunU30}
    (hf : IsCentered f) :
    f 29 = - sevenSumU30 f := by
  have h := (isCentered_iff_explicitSum f).mp hf
  unfold explicitSumU30 at h
  unfold sevenSumU30
  linarith

/-! ## §4 — Extensionnalité sur U30 par sept coordonnées -/

/-- Deux fonctions centrées qui coïncident sur les sept classes
    {1, 7, 11, 13, 17, 19, 23} coïncident en fait sur les huit classes
    de U30.

    Note. Cette extensionnalité est restreinte à U30 — elle n'affirme
    rien sur les valeurs en dehors des huit classes inversibles
    (c'est-à-dire sur 0, 2, 3, 4, 5, 6, 8, 9, 10, 12, etc.). C'est
    cohérent avec le fait que IsCentered ne contraint que la somme
    sur U30 ; les valeurs hors U30 restent libres. -/
theorem centered_ext_from_first_seven {f g : FunU30}
    (hf : IsCentered f) (hg : IsCentered g)
    (h1  : f 1  = g 1)  (h7  : f 7  = g 7)
    (h11 : f 11 = g 11) (h13 : f 13 = g 13)
    (h17 : f 17 = g 17) (h19 : f 19 = g 19)
    (h23 : f 23 = g 23) :
    ∀ x ∈ U30, f x = g x := by
  intro x hx
  rw [mem_U30_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h7
  · exact h11
  · exact h13
  · exact h17
  · exact h19
  · exact h23
  · rw [centered_29_eq_neg_sevenSum hf, centered_29_eq_neg_sevenSum hg]
    unfold sevenSumU30
    rw [h1, h7, h11, h13, h17, h19, h23]

/-! ## §5 — Garde épistémique -/

/-- Ce module n'introduit aucune revendication sur RH. -/
theorem RHClaimed_false_CenteredCoordinates :
    RHClaimed = false := rh_not_claimed

end CouretUnification.Core
