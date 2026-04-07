import CouretUnification.Core.ExceptionalLocalCriterionPreviewExportOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue documentaire finale purement locale, sur la famille finie des 21 triplets
centrés sur l’identité, des couples déjà stabilisés `(triplet, bool)` :

- une liste finale de couples `(triplet, bool)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue d’export déjà stabilisée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalView where
  rows : List (Triplet × Bool)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromExport :
    rows =
      identityCenteredExceptionalLocalCriterionPreviewExport.rows

/--
Vue finale canonique purement locale :
on reprend simplement la vue d’export déjà stabilisée.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalView :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalView where
  rows := identityCenteredExceptionalLocalCriterionPreviewExport.rows
  rows_len := identityCenteredExceptionalLocalCriterionPreviewExport.rows_len
  rows_fst := identityCenteredExceptionalLocalCriterionPreviewExport.rows_fst
  rows_fromExport := rfl

/-- La vue finale canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalView_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalView.rows.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalView.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalView_triplet :
    identityCenteredExceptionalLocalCriterionPreviewFinalView.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalView.rows_fst

/--
La vue finale canonique coïncide bien avec la vue d’export
déjà stabilisée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalView_coherence :
    identityCenteredExceptionalLocalCriterionPreviewFinalView.rows =
      identityCenteredExceptionalLocalCriterionPreviewExport.rows := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalView.rows_fromExport

/--
Couple documentaire canonique du cas Couret dans la vue finale locale.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair :
    Triplet × Bool :=
  couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair

/--
Dans le cas Couret, le couple documentaire canonique final
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair_eq :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewExportPair_eq

/--
Validation groupée minimale de la vue documentaire finale purement locale
sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalViewOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalView.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalView.rows =
          identityCenteredExceptionalLocalCriterionPreviewExport.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalView_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalView_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalView_coherence,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair_eq
  ⟩

end

end CouretUnification.Core