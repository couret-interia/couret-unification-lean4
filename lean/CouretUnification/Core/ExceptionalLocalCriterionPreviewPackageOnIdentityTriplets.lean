import CouretUnification.Core.ExceptionalLocalCriterionPreviewOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table booléenne documentaire du critère local synthétique ;
- la table de prévisualisation documentaire purement locale extraite de celle-ci.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewPackage where
  booleanTable : List IdentityCenteredExceptionalLocalCriterionBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets

  previewTable : List IdentityCenteredExceptionalLocalCriterionPreviewEntry
  previewTable_len : previewTable.length = 21
  previewTable_triplet :
    previewTable.map (fun E => E.triplet) = identityCenteredTriplets
  previewTable_forgetsToBooleanPairs :
    previewTable.map (fun E => (E.triplet, E.value)) =
      booleanTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique purement local :
on regroupe simplement la table booléenne déjà construite
et la table de prévisualisation qui en est extraite.
-/
def identityCenteredExceptionalLocalCriterionPreviewPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewPackage where
  booleanTable := identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable
  booleanTable_len := identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_len
  booleanTable_triplet :=
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_triplet

  previewTable := identityCenteredExceptionalLocalCriterionPreviewTable
  previewTable_len := identityCenteredExceptionalLocalCriterionPreviewTable_length
  previewTable_triplet := identityCenteredExceptionalLocalCriterionPreviewTable_triplet
  previewTable_forgetsToBooleanPairs :=
    identityCenteredExceptionalLocalCriterionPreviewTable_forgetsToBooleanPairs

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable_len

/-- La table de prévisualisation du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewPackage_previewTable_length :
    identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_len

/-- Les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
          (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_triplet
  ⟩

/--
La table de prévisualisation oublie bien vers la projection documentaire
`(triplet, bool)` de la table booléenne.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_forgetsToBooleanPairs

/--
Cas Couret : l’entrée de prévisualisation canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewPackage_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_triplet

/--
Cas Couret : la valeur booléenne documentaire de prévisualisation
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewPackage_value :
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.value = true := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_value

/--
Validation groupée minimale du paquet canonique purement local
au niveau booléen / prévisualisation sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.triplet = couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.value = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewPackage_previewTable_length,
    identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewPackage_forgetful_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewPackage_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewPackage_value
  ⟩

end

end CouretUnification.Core