import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalViewOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue d’export documentaire purement locale, sur la famille finie des 21 triplets
centrés sur l’identité, des couples finaux déjà stabilisés `(triplet, bool)` :

- une liste de couples `(triplet, bool)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale déjà stabilisée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalExport where
  rows : List (Triplet × Bool)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalView :
    rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalView.rows

/--
Export canonique purement local :
on reprend simplement la vue finale déjà stabilisée.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalExport :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalExport where
  rows := identityCenteredExceptionalLocalCriterionPreviewFinalView.rows
  rows_len := identityCenteredExceptionalLocalCriterionPreviewFinalView.rows_len
  rows_fst := identityCenteredExceptionalLocalCriterionPreviewFinalView.rows_fst
  rows_fromFinalView := rfl

/-- La vue d’export canonique finale a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExport_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExport_triplet :
    identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows_fst

/--
La vue d’export canonique finale coïncide bien avec la vue finale
déjà stabilisée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExport_coherence :
    identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalView.rows := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows_fromFinalView

/--
La vue d’export canonique finale est bien obtenue à partir de la vue finale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalExport_fromFinalView :
    identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalView.rows := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalExport_coherence

/--
Couple documentaire canonique du cas Couret dans la vue d’export finale locale.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair :
    Triplet × Bool :=
  couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair

/--
Dans le cas Couret, le couple documentaire canonique d’export final
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair_eq :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair_eq

/--
Validation groupée minimale de la vue d’export documentaire finale purement locale
sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalExportOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows =
          identityCenteredExceptionalLocalCriterionPreviewFinalView.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalExport_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalExport_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalExport_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair_eq
  ⟩

end

end CouretUnification.Core