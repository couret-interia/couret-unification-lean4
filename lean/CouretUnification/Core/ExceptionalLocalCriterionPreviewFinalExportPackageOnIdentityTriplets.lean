import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalBooleanPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalExportOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- le paquet booléen documentaire final déjà stabilisé ;
- la vue d’export documentaire finale purement locale des couples `(triplet, bool)`.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalExportPackage where
  booleanPackage : IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage
  exportView : IdentityCenteredExceptionalLocalCriterionPreviewFinalExport

  booleanToExport :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      exportView.rows

/--
Paquet canonique purement local :
on regroupe simplement le paquet booléen final déjà construit
et la vue d’export finale qui en est extraite.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalExportPackage where
  booleanPackage := identityCenteredExceptionalLocalCriterionPreviewFinalBooleanPackage
  exportView := identityCenteredExceptionalLocalCriterionPreviewFinalExport
  booleanToExport := by
    exact identityCenteredExceptionalLocalCriterionPreviewFinalExport_coherence.symm

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable_len

/-- La vue d’export finale du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_export_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows_len

/-- Les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows.map Prod.fst =
          identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows_fst
  ⟩

/--
Le paquet canonique identifie bien la table booléenne finale
à la vue d’export documentaire purement locale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_coherence :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanToExport

/--
La vue d’export du paquet canonique coïncide aussi avec la projection
documentaire `(triplet, bool)` de la table décidable finale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_fromDecidableTable :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows := by
  calc
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact
          identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable_forgetsToPreviewPairs.symm
    _ =
      identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows := by
        exact
          identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanToExport

/--
Cas Couret : le couple documentaire canonique d’export final
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair_eq

/--
Validation groupée minimale du paquet canonique purement local
au niveau booléen final / export sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalExportPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_export_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage.exportView.rows_fst,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_coherence,
    identityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_fromDecidableTable,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPackage_pair
  ⟩

end

end CouretUnification.Core