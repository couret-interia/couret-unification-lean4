import CouretUnification.Core.ExceptionalLocalCriterionPreviewPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, condensant le noyau minimal déjà empaqueté :

- un triplet de la famille ;
- la valeur booléenne documentaire associée au critère local synthétique.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewSummary where
  triplet : Triplet
  value : Bool

/--
Constructeur canonique :
à partir d’une entrée de prévisualisation déjà construite,
on en extrait le résumé minimal correspondant.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary
    (E : IdentityCenteredExceptionalLocalCriterionPreviewEntry) :
    IdentityCenteredExceptionalLocalCriterionPreviewSummary where
  triplet := E.triplet
  value := E.value

/--
Table documentaire purement locale des résumés minimaux associés
à la prévisualisation du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionPreviewSummaryTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewSummary :=
  identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary

/-- La table documentaire locale des résumés a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewSummaryTable_length :
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewSummaryTable]
    using identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewSummaryTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewSummaryTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable_triplet

/--
En oubliant la structure de résumé, on retrouve exactement la projection
documentaire `(triplet, bool)` de la table de prévisualisation déjà empaquetée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewSummaryTable_forgetsToPreviewPairs :
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
        (fun E => (E.triplet, E.value)) := by
  unfold identityCenteredExceptionalLocalCriterionPreviewSummaryTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]

/--
Cas Couret : résumé documentaire local canonique extrait
de l’entrée de prévisualisation déjà stabilisée.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewSummary :
    IdentityCenteredExceptionalLocalCriterionPreviewSummary :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry

/--
Dans le cas Couret, le résumé documentaire local canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewSummary,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_triplet

/--
Dans le cas Couret, la valeur booléenne documentaire du résumé local
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_value :
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.value = true := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewSummary,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewSummary]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_value

/--
Validation groupée minimale du cas Couret au niveau du résumé documentaire
purement local de prévisualisation sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewSummaryTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewSummaryTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewPackage.previewTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.value = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable_length,
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewSummaryTable_forgetsToPreviewPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_value
  ⟩

end

end CouretUnification.Core