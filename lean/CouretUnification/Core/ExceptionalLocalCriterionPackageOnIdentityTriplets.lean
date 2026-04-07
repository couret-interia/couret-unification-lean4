import CouretUnification.Core.ExceptionalLocalCriterionSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table du critère local synthétique ;
- la table des témoins explicites associés ;
- la table des vues minimales ;
- la table des résumés minimaux.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPackage where
  criterionTable : List (Triplet × Prop)
  criterionTable_len : criterionTable.length = 21
  criterionTable_triplet :
    criterionTable.map Prod.fst = identityCenteredTriplets

  witnessTable : List IdentityCenteredExceptionalLocalCriterionWitnessEntry
  witnessTable_len : witnessTable.length = 21
  witnessTable_triplet :
    witnessTable.map (fun E => E.triplet) = identityCenteredTriplets
  witnessTable_forgetsToCriterionTable :
    witnessTable.map (fun E => (E.triplet, E.criterion)) = criterionTable

  coreViewTable : List IdentityCenteredExceptionalLocalCriterionCoreView
  coreViewTable_len : coreViewTable.length = 21
  coreViewTable_triplet :
    coreViewTable.map (fun E => E.triplet) = identityCenteredTriplets
  coreViewTable_forgetsToCriterionTable :
    coreViewTable.map (fun E => (E.triplet, E.criterion)) = criterionTable

  summaryTable : List IdentityCenteredExceptionalLocalCriterionSummary
  summaryTable_len : summaryTable.length = 21
  summaryTable_triplet :
    summaryTable.map (fun E => E.triplet) = identityCenteredTriplets
  summaryTable_forgetsToCriterionTable :
    summaryTable.map (fun E => (E.triplet, E.criterion)) = criterionTable

/--
Paquet canonique purement local sur la famille identité :
on regroupe simplement les quatre tables déjà construites et leurs
cohérences documentaires minimales.
-/
def identityCenteredExceptionalLocalCriterionPackage :
    IdentityCenteredExceptionalLocalCriterionPackage where
  criterionTable := identityCenteredExceptionalLocalCriterionTable
  criterionTable_len := identityCenteredExceptionalLocalCriterionTable_length
  criterionTable_triplet := identityCenteredExceptionalLocalCriterionTable_fst

  witnessTable := identityCenteredExceptionalLocalCriterionWitnessTable
  witnessTable_len := identityCenteredExceptionalLocalCriterionWitnessTable_length
  witnessTable_triplet := identityCenteredExceptionalLocalCriterionWitnessTable_triplet
  witnessTable_forgetsToCriterionTable :=
    identityCenteredExceptionalLocalCriterionWitnessTable_forgetsToCriterionTable

  coreViewTable := identityCenteredExceptionalLocalCriterionCoreViewTable
  coreViewTable_len := identityCenteredExceptionalLocalCriterionCoreViewTable_length
  coreViewTable_triplet := identityCenteredExceptionalLocalCriterionCoreViewTable_triplet
  coreViewTable_forgetsToCriterionTable :=
    identityCenteredExceptionalLocalCriterionCoreViewTable_forgetsToCriterionTable

  summaryTable := identityCenteredExceptionalLocalCriterionSummaryTable
  summaryTable_len := identityCenteredExceptionalLocalCriterionSummaryTable_length
  summaryTable_triplet := identityCenteredExceptionalLocalCriterionSummaryTable_triplet
  summaryTable_forgetsToCriterionTable :=
    identityCenteredExceptionalLocalCriterionSummaryTable_forgetsToCriterionTable

/-- La table du critère local synthétique du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPackage_criterionTable_length :
    identityCenteredExceptionalLocalCriterionPackage.criterionTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPackage.criterionTable_len

/-- La table des témoins explicites du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPackage_witnessTable_length :
    identityCenteredExceptionalLocalCriterionPackage.witnessTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPackage.witnessTable_len

/-- La table des vues minimales du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPackage_coreViewTable_length :
    identityCenteredExceptionalLocalCriterionPackage.coreViewTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPackage.coreViewTable_len

/-- La table des résumés minimaux du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPackage_summaryTable_length :
    identityCenteredExceptionalLocalCriterionPackage.summaryTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionPackage.summaryTable_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionPackage.criterionTable.map Prod.fst =
        identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.witnessTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.coreViewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.summaryTable.map
          (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPackage.criterionTable_triplet,
    identityCenteredExceptionalLocalCriterionPackage.witnessTable_triplet,
    identityCenteredExceptionalLocalCriterionPackage.coreViewTable_triplet,
    identityCenteredExceptionalLocalCriterionPackage.summaryTable_triplet
  ⟩

/--
Les trois tables enrichies oublient bien vers la même table documentaire
du critère local synthétique.
-/
theorem identityCenteredExceptionalLocalCriterionPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionPackage.witnessTable.map
        (fun E => (E.triplet, E.criterion)) =
          identityCenteredExceptionalLocalCriterionPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionPackage.coreViewTable.map
          (fun E => (E.triplet, E.criterion)) =
            identityCenteredExceptionalLocalCriterionPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionPackage.summaryTable.map
          (fun E => (E.triplet, E.criterion)) =
            identityCenteredExceptionalLocalCriterionPackage.criterionTable := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPackage.witnessTable_forgetsToCriterionTable,
    identityCenteredExceptionalLocalCriterionPackage.coreViewTable_forgetsToCriterionTable,
    identityCenteredExceptionalLocalCriterionPackage.summaryTable_forgetsToCriterionTable
  ⟩

/--
Cas Couret : le critère local synthétique empaqueté dans le résumé canonique
est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPackage_summaryCriterion :
    couretIdentityCenteredExceptionalLocalCriterionSummary.criterion := by
  exact couretIdentityCenteredExceptionalLocalCriterionSummary_criterion

/--
Cas Couret : le témoin explicite canonique du résumé local empaqueté
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPackage_summaryWitness :
    couretIdentityCenteredExceptionalLocalCriterionSummaryWitness.candidate.triplet =
      couretTriplet := by
  exact couretIdentityCenteredExceptionalLocalCriterionSummaryWitness_triplet

/--
Validation groupée minimale du paquet canonique purement local
sur la famille identité.
-/
theorem exceptionalLocalCriterionPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPackage.criterionTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPackage.witnessTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPackage.coreViewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPackage.summaryTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPackage.criterionTable.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.witnessTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.coreViewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.summaryTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPackage.witnessTable.map
          (fun E => (E.triplet, E.criterion)) =
            identityCenteredExceptionalLocalCriterionPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionPackage.coreViewTable.map
          (fun E => (E.triplet, E.criterion)) =
            identityCenteredExceptionalLocalCriterionPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionPackage.summaryTable.map
          (fun E => (E.triplet, E.criterion)) =
            identityCenteredExceptionalLocalCriterionPackage.criterionTable
      ∧ couretIdentityCenteredExceptionalLocalCriterionSummary.criterion
      ∧ couretIdentityCenteredExceptionalLocalCriterionSummaryWitness.candidate.triplet =
          couretTriplet := by
  refine ⟨
    identityCenteredExceptionalLocalCriterionPackage_criterionTable_length,
    identityCenteredExceptionalLocalCriterionPackage_witnessTable_length,
    identityCenteredExceptionalLocalCriterionPackage_coreViewTable_length,
    identityCenteredExceptionalLocalCriterionPackage_summaryTable_length,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    couretIdentityCenteredExceptionalLocalCriterionPackage_summaryCriterion,
    couretIdentityCenteredExceptionalLocalCriterionPackage_summaryWitness
  ⟩
  · exact identityCenteredExceptionalLocalCriterionPackage.criterionTable_triplet
  · exact identityCenteredExceptionalLocalCriterionPackage.witnessTable_triplet
  · exact identityCenteredExceptionalLocalCriterionPackage.coreViewTable_triplet
  · exact identityCenteredExceptionalLocalCriterionPackage.summaryTable_triplet
  · exact identityCenteredExceptionalLocalCriterionPackage.witnessTable_forgetsToCriterionTable
  · exact identityCenteredExceptionalLocalCriterionPackage.coreViewTable_forgetsToCriterionTable
  · exact identityCenteredExceptionalLocalCriterionPackage.summaryTable_forgetsToCriterionTable

end

end CouretUnification.Core