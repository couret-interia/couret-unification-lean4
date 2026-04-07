import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalViewOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant simplement :

- la vue documentaire finale purement locale déjà stabilisée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalPackage where
  finalView : IdentityCenteredExceptionalLocalCriterionPreviewFinalView

/--
Paquet canonique purement local :
on reprend simplement la vue finale déjà stabilisée.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalPackage :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalPackage where
  finalView := identityCenteredExceptionalLocalCriterionPreviewFinalView

/-- La vue finale du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalPackage_final_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows.length = 21 := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalPackage_triplet_projection :
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows_fst

/--
Le paquet canonique recolle bien avec la vue d’export déjà stabilisée
en amont de la chaîne finale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalPackage_fromExport :
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows =
      identityCenteredExceptionalLocalCriterionPreviewExport.rows := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalView_coherence

/--
Cas Couret : le couple documentaire canonique final
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalPackage_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair_eq

/--
Validation groupée minimale du paquet canonique purement local
au niveau de la vue finale sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows =
          identityCenteredExceptionalLocalCriterionPreviewExport.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage_final_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage_triplet_projection,
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage_fromExport,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalPackage_pair
  ⟩

end

end CouretUnification.Core