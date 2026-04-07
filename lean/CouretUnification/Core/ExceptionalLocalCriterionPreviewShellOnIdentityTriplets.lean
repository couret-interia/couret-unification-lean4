import CouretUnification.Core.ExceptionalLocalCriterionPreviewSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du résumé documentaire
de prévisualisation sur la famille finie des 21 triplets centrés
sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` admet une entrée
dans la table des résumés de prévisualisation.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewShell where
  summaryTable : List IdentityCenteredExceptionalLocalCriterionPreviewSummary
  summaryTable_len : summaryTable.length = 21
  summaryTable_triplet :
    summaryTable.map (fun E => E.triplet) = identityCenteredTriplets

  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ E : IdentityCenteredExceptionalLocalCriterionPreviewSummary,
            E.triplet = T
  decidablePredicate : Decidable predicate

/--
Shell canonique :
on prend exactement la table documentaire des résumés de prévisualisation
déjà construite, munie d’un prédicat local minimal de couverture documentaire.
-/
def identityCenteredExceptionalLocalCriterionPreviewShell :
    IdentityCenteredExceptionalLocalCriterionPreviewShell where
  summaryTable := identityCenteredExceptionalLocalCriterionPreviewSummaryTable
  summaryTable_len := identityCenteredExceptionalLocalCriterionPreviewSummaryTable_length
  summaryTable_triplet := identityCenteredExceptionalLocalCriterionPreviewSummaryTable_triplet

  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ E : IdentityCenteredExceptionalLocalCriterionPreviewSummary,
          E.triplet = T
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionPreviewShell.predicate_spec
    (S : IdentityCenteredExceptionalLocalCriterionPreviewShell) :
    S.predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ E : IdentityCenteredExceptionalLocalCriterionPreviewSummary,
            E.triplet = T := by
  exact S.predicate_eq

/--
Le prédicat documentaire local porté par le shell canonique est bien vérifié :
tout triplet de la famille identité apparaît bien dans la table des résumés
de prévisualisation.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewShell_true :
    identityCenteredExceptionalLocalCriterionPreviewShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.map
        (fun E => E.triplet) := by
    rw [identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable_triplet]
    exact hmem
  rcases List.mem_map.1 hmem' with ⟨E, _hE, hEq⟩
  exact ⟨E, hEq⟩

/--
Version calculatoire : décidabilité locale purement documentaire
du prédicat empaqueté par le shell canonique.
-/
def identityCenteredExceptionalLocalCriterionPreviewShellDecidable :
    Decidable identityCenteredExceptionalLocalCriterionPreviewShell.predicate :=
  identityCenteredExceptionalLocalCriterionPreviewShell.decidablePredicate

/--
Cas Couret : le shell local sur la famille identité fournit bien
une entrée de résumé documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewShell_entry :
    ∃ E : IdentityCenteredExceptionalLocalCriterionPreviewSummary,
      E.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée canonique de résumé documentaire porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewShell_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.triplet =
      couretTriplet := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_triplet

/--
Cas Couret : la valeur booléenne documentaire du résumé canonique
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewShell_value :
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.value = true := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_value

/--
Validation groupée minimale du shell purement local
sur la famille identité :
- la table documentaire des résumés a bien longueur 21 ;
- sa projection sur les triplets redonne bien la famille identité ;
- le prédicat empaqueté est vrai ;
- le cas Couret admet bien une entrée documentaire ;
- cette entrée canonique vaut bien `true`.
-/
theorem exceptionalLocalCriterionPreviewShellOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewShell.predicate
      ∧ (∃ E : IdentityCenteredExceptionalLocalCriterionPreviewSummary,
            E.triplet = couretTriplet)
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewSummary.value = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable_len,
    identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewShell_true,
    couretIdentityCenteredExceptionalLocalCriterionPreviewShell_entry,
    couretIdentityCenteredExceptionalLocalCriterionPreviewShell_value
  ⟩

end

end CouretUnification.Core