import CouretUnification.Core.ExceptionalLocalCriterionPreviewBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue d’export documentaire purement locale, sur la famille finie des 21 triplets
centrés sur l’identité, des couples déjà stabilisés `(triplet, bool)` :

- une liste de couples `(triplet, bool)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la projection documentaire de la table booléenne déjà empaquetée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewExport where
  rows : List (Triplet × Bool)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromBooleanTable :
    rows =
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value))

/--
Export canonique purement local :
on prend simplement la projection documentaire `(triplet, bool)`
de la table booléenne déjà empaquetée.
-/
def identityCenteredExceptionalLocalCriterionPreviewExport :
    IdentityCenteredExceptionalLocalCriterionPreviewExport where
  rows :=
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
      (fun E => (E.triplet, E.value))
  rows_len := by
    simpa using
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_len
  rows_fst := by
    rw [List.map_map]
    have hfun :
        (Prod.fst ∘
          fun E : IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry =>
            (E.triplet, E.value)) =
          (fun E : IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry =>
            E.triplet) := by
      funext E
      rfl
    rw [hfun]
    exact
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_triplet
  rows_fromBooleanTable := rfl

/-- La vue d’export canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExport_length :
    identityCenteredExceptionalLocalCriterionPreviewExport.rows.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewExport.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExport_triplet :
    identityCenteredExceptionalLocalCriterionPreviewExport.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalLocalCriterionPreviewExport.rows_fst

/--
La vue d’export canonique coïncide bien avec la projection documentaire
`(triplet, bool)` de la table booléenne déjà empaquetée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewExport_coherence :
    identityCenteredExceptionalLocalCriterionPreviewExport.rows =
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalLocalCriterionPreviewExport.rows_fromBooleanTable

/--
Couple documentaire canonique du cas Couret dans la vue d’export locale.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair :
    Triplet × Bool :=
  ( couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.triplet
  , couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue )

/--
Dans le cas Couret, le couple documentaire canonique d’export
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair_eq :
    couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair =
      (couretTriplet, true) := by
  simp [couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_boolValue]

/--
Validation groupée minimale de la vue d’export documentaire purement locale
sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewExportOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewExport.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewExport.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExport.rows =
          identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewExport_length,
    identityCenteredExceptionalLocalCriterionPreviewExport_triplet,
    identityCenteredExceptionalLocalCriterionPreviewExport_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair_eq
  ⟩

end

end CouretUnification.Core