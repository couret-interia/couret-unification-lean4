import CouretUnification.Core.ExceptionalDecisionCompatibilityOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
API canonique publique des décisions exceptionnelles sur la famille finie
des 21 triplets centrés sur l’identité.

Ce fichier est volontairement compact :
- il fixe les noms stables à utiliser dans la suite ;
- il s’appuie uniquement sur la couche de compatibilité ;
- il évite que les futurs fichiers dépendent directement de la tour
  `Final`, `FinalView`, `FinalViewFinal`, etc.

Convention :
les développements futurs doivent préférer les noms introduits ici,
et non les anciens noms historiques lorsqu’un simple accès à la couche
canonique suffit.
-/

/--
Type canonique public pour la couche terminale des décisions exceptionnelles
sur la famille identité.
-/
abbrev ExceptionalDecisionCanonicalAPI :=
  IdentityCenteredExceptionalDecisionCanonical

/--
Valeur canonique publique pour la couche terminale des décisions exceptionnelles
sur la famille identité.
-/
abbrev exceptionalDecisionCanonicalAPI :
    ExceptionalDecisionCanonicalAPI :=
  identityCenteredExceptionalDecisionCanonical

/--
Sortie documentaire canonique publique :
liste des couples `(triplet, valeur de décision)` portée par l’API stable.
-/
abbrev exceptionalDecisionCanonicalRowsOnIdentityTriplets :
    List (Triplet × ExceptionalDecisionValue) :=
  identityCenteredExceptionalDecisionCanonicalRows

/--
Entrée canonique publique du cas Couret dans l’API stable.
-/
abbrev couretExceptionalDecisionCanonicalEntryOnIdentityTriplets :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionCanonicalEntry

/-- L’API canonique publique a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalAPI_length :
    exceptionalDecisionCanonicalRowsOnIdentityTriplets.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonical_length

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem exceptionalDecisionCanonicalAPI_triplet :
    exceptionalDecisionCanonicalRowsOnIdentityTriplets.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonical_triplet

/--
Toute ligne de l’API canonique publique porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionCanonicalAPI_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonical_mem_family hp

/--
Le cas Couret recolle bien à l’entrée canonique publique stable.
-/
theorem couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_triplet :
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionCanonicalEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique publique
prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_cases :
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionCanonicalEntry_cases

/--
Compatibilité publique : la couche historique `Final` se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinal :
    identityCenteredExceptionalDecisionFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinal_compat

/--
Compatibilité publique : la couche historique `FinalSummary` se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalSummary :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalSummary_compat

/--
Compatibilité publique : la couche historique `FinalView` se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalView :
    identityCenteredExceptionalDecisionFinalView.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalView_compat

/--
Compatibilité publique : la couche historique `FinalViewFinal` se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalViewFinal :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinal_compat

/--
Compatibilité publique : la couche historique `FinalViewFinalFinal`
se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalViewFinalFinal :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal_compat

/--
Compatibilité publique : la table décidable `Final`, oubliée vers
`(triplet, valeur)`, se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalDecidableTable :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalDecidableTable_compat

/--
Compatibilité publique : la table booléenne `Final`, oubliée vers
`(triplet, valeur)`, se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalBooleanTable :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalBooleanTable_compat

/--
Compatibilité publique : la table décidable `FinalView`, oubliée vers
`(triplet, valeur)`, se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalViewDecidableTable :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewDecidableTable_compat

/--
Compatibilité publique : la table booléenne `FinalView`, oubliée vers
`(triplet, valeur)`, se réécrit vers l’API canonique.
-/
theorem exceptionalDecisionCanonicalAPI_fromFinalViewBooleanTable :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewBooleanTable_compat

/--
Validation groupée minimale de l’API canonique publique :
- la sortie canonique est bien calibrée ;
- les principales couches historiques se réécrivent vers elle ;
- le cas Couret recolle bien à l’entrée publique stable.
-/
theorem exceptionalDecisionCanonicalAPIOnIdentityTriplets_valid :
    exceptionalDecisionCanonicalRowsOnIdentityTriplets.length = 21
      ∧ exceptionalDecisionCanonicalRowsOnIdentityTriplets.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ (∀ p, p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    exceptionalDecisionCanonicalAPI_length,
    exceptionalDecisionCanonicalAPI_triplet,
    exceptionalDecisionCanonicalAPI_fromFinal,
    exceptionalDecisionCanonicalAPI_fromFinalSummary,
    exceptionalDecisionCanonicalAPI_fromFinalView,
    exceptionalDecisionCanonicalAPI_fromFinalViewFinal,
    exceptionalDecisionCanonicalAPI_fromFinalViewFinalFinal,
    ?_,
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_triplet,
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_cases
  ⟩
  intro p hp
  exact exceptionalDecisionCanonicalAPI_mem_family hp

end

end CouretUnification.Core