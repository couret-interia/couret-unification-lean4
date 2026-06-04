import CouretUnification.Core.PointDefectLemma
import CouretUnification.Core.G30Classification  -- oracle de régression
import Mathlib.Tactic

/-!

# Spécialisation à G₃₀ — statut [D-local]

Couret–Unification — couche finie G₃₀.

Ce fichier relie le mécanisme abstrait du défaut ponctuel à la classification
finie des triplets de `G₃₀`.

## Statut

D-formal localement, dépend de l'oracle D-computational typeQ_iff_quadratic_fiber]
Compilé avec Lean 4 / Mathlib v4.29.1,
sans `sorry` dans ce fichier, sans nouvel axiome.

La certification effective de la réciproque repose sur l'oracle fini
`G30Classification.typeQ_iff_quadratic_fiber`, prouvé par énumération exhaustive
des 56 triplets canoniques via `native_decide`.

## Contenu

* Sens direct : fourni par `PointDefectLemma`, mécanisme abstrait du défaut
  ponctuel sur une fibre quadratique.
* Réciproque spécifique à `G₃₀` : un triplet canonique de type Q est contenu
  dans une fibre quadratique.
* Ajout du verrou booléen `isTypeQTriplet`, qui encode explicitement :

  1. `T ∈ G30Classification.triplets` ;
  2. `G30Classification.isTypeQ T = true`.

## Note logique

`G30Classification.isTypeQ` seul est un test spectral brut sur une liste
arbitraire. Il ne garantit pas que la liste soit l'un des 56 triplets canoniques.

Le prédicat `isTypeQTriplet` ferme ce trou logique : l'énoncé sans hypothèse
séparée devient correct parce que l'appartenance canonique est intégrée dans
le prédicat d'entrée.

## Périmètre

Périmètre strictement fini : classification locale de `G₃₀`.

Aucun transport vers les nombres premiers réels.
Aucune conséquence analytique globale.
Ne lève pas les quarantaines liées au transport spectral.

Invariants préservés :
`RHClaimed = false`.
`ScopeExpansionClaimed = false`.
-/


namespace CouretUnification.Core.G30ClassificationFromPointDefect

/-- `T` est l'un des 56 triplets canoniques énumérés dans `G30Classification.triplets`. -/
def isCanonicalTriplet (T : List (Fin 8)) : Bool :=
  decide (T ∈ G30Classification.triplets)

/-- Type Q statutaire : triplet canonique + spectre de type Q.

Ce prédicat évite l'ambiguïté de `G30Classification.isTypeQ`, qui est seulement
un test spectral brut sur une liste quelconque. -/
def isTypeQTriplet (T : List (Fin 8)) : Bool :=
  isCanonicalTriplet T && G30Classification.isTypeQ T

/-- Extraction de l'appartenance canonique depuis `isTypeQTriplet`. -/
theorem mem_triplets_of_isTypeQTriplet (T : List (Fin 8)) :
    isTypeQTriplet T = true → T ∈ G30Classification.triplets := by
  intro h
  unfold isTypeQTriplet isCanonicalTriplet at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- Extraction du type Q spectral depuis `isTypeQTriplet`. -/
theorem typeQ_of_isTypeQTriplet (T : List (Fin 8)) :
    isTypeQTriplet T = true → G30Classification.isTypeQ T = true := by
  intro h
  unfold isTypeQTriplet at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- Version avec hypothèse explicite d'appartenance aux 56 triplets canoniques.

C'est le pont direct vers l'oracle énumératif
`G30Classification.typeQ_iff_quadratic_fiber`. -/
theorem typeQ_implies_quadratic_fiber_of_mem (T : List (Fin 8))
    (hT : T ∈ G30Classification.triplets) :
    G30Classification.isTypeQ T = true →
    G30Classification.inSomeQuadFiber T = true := by
  intro hQ
  have hEq :
      (G30Classification.isTypeQ T == G30Classification.inSomeQuadFiber T) = true := by
    have hAll :
        ∀ U ∈ G30Classification.triplets,
          (G30Classification.isTypeQ U == G30Classification.inSomeQuadFiber U) = true := by
      simpa [List.all_eq_true] using G30Classification.typeQ_iff_quadratic_fiber
    exact hAll T hT
  simpa [hQ] using hEq

/-- RÉCIPROQUE verrouillée, sans hypothèse séparée :
    `isTypeQTriplet T = true` suffit à porter à la fois l'information
    “T est un triplet canonique” et “T est de type Q”.

C'est la version recommandée pour éviter les faux positifs sur des listes arbitraires. -/
theorem typeQTriplet_implies_quadratic_fiber (T : List (Fin 8)) :
    isTypeQTriplet T = true →
    G30Classification.inSomeQuadFiber T = true := by
  intro h
  exact typeQ_implies_quadratic_fiber_of_mem T
    (mem_triplets_of_isTypeQTriplet T h)
    (typeQ_of_isTypeQTriplet T h)

/-- Alias court : même contenu que `typeQTriplet_implies_quadratic_fiber`.

Le nom historique est conservé, mais le prédicat d'entrée est maintenant le bon :
`isTypeQTriplet`, pas `G30Classification.isTypeQ` seul. -/
theorem typeQ_implies_quadratic_fiber (T : List (Fin 8)) :
    isTypeQTriplet T = true →
    G30Classification.inSomeQuadFiber T = true := by
  exact typeQTriplet_implies_quadratic_fiber T

end CouretUnification.Core.G30ClassificationFromPointDefect
