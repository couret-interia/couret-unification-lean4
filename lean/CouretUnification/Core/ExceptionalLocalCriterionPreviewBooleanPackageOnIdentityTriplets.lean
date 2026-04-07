import CouretUnification.Core.ExceptionalLocalCriterionPreviewBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table décidable documentaire de prévisualisation ;
- la table booléenne documentaire explicite associée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_forgetsToPreviewPairs :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique purement local :
on regroupe simplement la table décidable déjà construite
et la table booléenne qui en est extraite.
-/
def identityCenteredExceptionalLocalCriterionPreviewBooleanPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage where
  decidableTable := identityCenteredExceptionalLocalCriterionPreviewDecidableTable
  decidableTable_len := identityCenteredExceptionalLocalCriterionPreviewDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable_triplet

  booleanTable := identityCenteredExceptionalLocalCriterionPreviewBooleanTable
  booleanTable_len := identityCenteredExceptionalLocalCriterionPreviewBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable_triplet
  booleanTable_forgetsToPreviewPairs :=
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable_forgetsToPreviewPairs

/-- La table décidable du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_decidableTable_length :
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_len

/-- Les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne oublie bien vers la projection documentaire `(triplet, bool)`
de la table décidable de prévisualisation.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_forgetsToPreviewPairs

/--
Cas Couret : la ligne booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.triplet = couretTriplet := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry,
    couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_triplet

/--
Cas Couret : le prédicat local empaqueté dans la ligne booléenne canonique
est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.predicate := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_predicate

/--
Cas Couret : la présentation booléenne explicite associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_boolValue :
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue = true := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_boolValue_true

/--
Validation groupée minimale du paquet canonique purement local
au niveau décidable / booléen de prévisualisation sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_decidableTable_length,
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewBooleanPackage_forgetful_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_predicate,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage_boolValue
  ⟩

end

end CouretUnification.Core