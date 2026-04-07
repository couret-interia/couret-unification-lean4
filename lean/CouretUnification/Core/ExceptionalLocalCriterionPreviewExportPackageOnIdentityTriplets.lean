import CouretUnification.Core.ExceptionalLocalCriterionPreviewExportOnIdentityTriplets
import CouretUnification.Core.ExceptionalLocalCriterionPreviewPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table booléenne documentaire ;
- la table de prévisualisation documentaire ;
- la vue d’export documentaire purement locale des couples `(triplet, bool)`.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewExportPackage where
  booleanPackage : IdentityCenteredExceptionalLocalCriterionPreviewBooleanPackage
  previewPackage : IdentityCenteredExceptionalLocalCriterionPreviewPackage
  exportView : IdentityCenteredExceptionalLocalCriterionPreviewExport

  booleanToExport :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      exportView.rows

  previewToExport :
    previewPackage.previewTable.map (fun E => (E.triplet, E.value)) =
      exportView.rows

/--
Paquet canonique purement local :
on regroupe simplement le paquet booléen, le paquet de prévisualisation,
et la vue d’export déjà construits, avec leurs cohérences documentaires minimales.
-/
def identityCenteredExceptionalLocalCriterionPreviewExportPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewExportPackage where
  booleanPackage := identityCenteredExceptionalLocalCriterionPreviewBooleanPackage
  previewPackage := identityCenteredExceptionalLocalCriterionPreviewPackage
  exportView := identityCenteredExceptionalLocalCriterionPreviewExport

  booleanToExport := by
    simp [identityCenteredExceptionalLocalCriterionPreviewExport,
      identityCenteredExceptionalLocalCriterionPreviewBooleanPackage]

  previewToExport := by
    calc
      identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalLocalCriterionPreviewPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) := by
            exact
              identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_forgetsToBooleanPairs
      _ = identityCenteredExceptionalLocalCriterionPreviewExport.rows := by
            simpa [identityCenteredExceptionalLocalCriterionPreviewPackage,
              identityCenteredExceptionalLocalCriterionPreviewBooleanPackage]
              using identityCenteredExceptionalLocalCriterionPreviewExport_coherence.symm

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExportPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable_len

/-- La table de prévisualisation du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExportPackage_previewTable_length :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable_len

/-- La vue d’export canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExportPackage_export_length :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewExportPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows.map Prod.fst =
          identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows_fst
  ⟩

/--
Les couches booléenne et prévisualisation oublient bien vers la même
vue d’export documentaire `(triplet, bool)`.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewExportPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
          identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanToExport,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewToExport
  ⟩

/--
Cas Couret : le couple documentaire canonique d’export
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewExportPackage_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair_eq

/--
Validation groupée minimale du paquet canonique purement local
au niveau booléen / prévisualisation / export sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewExportPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows
      ∧ identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewExportPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage_previewTable_length,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage_export_length,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewPackage.previewTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.exportView.rows_fst,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.booleanToExport,
    identityCenteredExceptionalLocalCriterionPreviewExportPackage.previewToExport,
    couretIdentityCenteredExceptionalLocalCriterionPreviewExportPackage_pair
  ⟩

end

end CouretUnification.Core