import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire final purement local, sur la famille finie des 21 triplets
centrés sur l’identité, condensant la vue finale déjà stabilisée :

- une liste finale de couples `(triplet, bool)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale déjà empaquetée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalSummary where
  rows : List (Triplet × Bool)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalPackage :
    rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows

/--
Résumé final canonique purement local :
on reprend simplement la vue finale déjà stabilisée dans le paquet final.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalSummary :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalSummary where
  rows := identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows
  rows_len :=
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows_len
  rows_fst :=
    identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows_fst
  rows_fromFinalPackage := rfl

/-- Le résumé final canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalSummary_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalSummary_triplet :
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows_fst

/--
Le résumé final canonique coïncide bien avec la vue finale
déjà stabilisée dans le paquet documentaire local final.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalSummary_coherence :
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows_fromFinalPackage

/--
Le résumé final canonique coïncide aussi avec la vue d’export
déjà stabilisée en amont de la chaîne finale.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalSummary_fromExport :
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows =
      identityCenteredExceptionalLocalCriterionPreviewExport.rows := by
  calc
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows =
      identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalLocalCriterionPreviewFinalSummary_coherence
    _ =
      identityCenteredExceptionalLocalCriterionPreviewExport.rows := by
        exact identityCenteredExceptionalLocalCriterionPreviewFinalPackage_fromExport

/--
Couple documentaire canonique du cas Couret dans le résumé final local.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair :
    Triplet × Bool :=
  couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair

/--
Dans le cas Couret, le couple documentaire canonique final
est bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair_eq :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalViewPair_eq

/--
Validation groupée minimale du résumé documentaire final purement local
sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows =
          identityCenteredExceptionalLocalCriterionPreviewFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows =
          identityCenteredExceptionalLocalCriterionPreviewExport.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary_coherence,
    identityCenteredExceptionalLocalCriterionPreviewFinalSummary_fromExport,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair_eq
  ⟩

end

end CouretUnification.Core