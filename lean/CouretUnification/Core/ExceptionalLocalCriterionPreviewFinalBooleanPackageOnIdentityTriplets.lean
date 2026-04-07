import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table décidable documentaire finale ;
- la table booléenne documentaire explicite finale associée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_forgetsToPreviewPairs :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique purement local :
on regroupe simplement la table décidable finale déjà construite
et la table booléenne explicite qui en est extraite.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage where
  decidableTable := identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable
  decidableTable_len := identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_triplet

  booleanTable := identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable
  booleanTable_len := identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_triplet
  booleanTable_forgetsToPreviewPairs :=
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_forgetsToPreviewPairs

/-- La table décidable du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_decidableTable_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable_len

/-- Les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne finale oublie bien vers la projection documentaire
`(triplet, bool)` de la table décidable finale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable_forgetsToPreviewPairs

/--
Cas Couret : la ligne booléenne finale canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_triplet

/--
Cas Couret : le prédicat local empaqueté dans la ligne booléenne finale canonique
est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.predicate := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_predicate

/--
Cas Couret : la présentation booléenne explicite finale associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_boolValue :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.boolValue = true := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_boolValue_true

/--
Validation groupée minimale du paquet canonique purement local
au niveau décidable / booléen final sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.boolValue = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_decidableTable_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_forgetful_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_predicate,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage_boolValue
  ⟩

end

end CouretUnification.Core