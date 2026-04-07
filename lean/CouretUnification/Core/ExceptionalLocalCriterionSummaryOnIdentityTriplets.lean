import CouretUnification.Core.ExceptionalLocalCriterionCoreViewOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, condensant le noyau minimal déjà extrait :

- un triplet ;
- le critère local synthétique associé ;
- l’extracteur explicite de témoin lorsque ce critère est satisfait.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionSummary where
  triplet : Triplet
  criterion : Prop
  criterion_eq :
    criterion = satisfiesExceptionalLocalPredicateOnIdentityTriplets triplet
  witnessOfCriterion :
    criterion → IdentityCenteredExceptionalWitness
  witness_spec :
    ∀ h : criterion, (witnessOfCriterion h).candidate.triplet = triplet

/--
Constructeur canonique :
à partir d’une vue documentaire locale déjà construite,
on en extrait le résumé minimal correspondant.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionSummary
    (E : IdentityCenteredExceptionalLocalCriterionCoreView) :
    IdentityCenteredExceptionalLocalCriterionSummary where
  triplet := E.triplet
  criterion := E.criterion
  criterion_eq := E.criterion_eq
  witnessOfCriterion := E.witnessOfCriterion
  witness_spec := E.witness_spec

/--
Table documentaire purement locale des résumés minimaux associés
au critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionSummaryTable :
    List IdentityCenteredExceptionalLocalCriterionSummary :=
  identityCenteredExceptionalLocalCriterionCoreViewTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionSummary

/-- La table documentaire locale des résumés a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionSummaryTable_length :
    identityCenteredExceptionalLocalCriterionSummaryTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionSummaryTable,
    identityCenteredExceptionalLocalCriterionCoreViewTable_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionSummaryTable_triplet :
    identityCenteredExceptionalLocalCriterionSummaryTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionSummaryTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionSummary) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionCoreViewTable_triplet

/--
En oubliant l’extracteur de témoin, on retrouve exactement la table
documentaire du critère local synthétique déjà isolée.
-/
theorem identityCenteredExceptionalLocalCriterionSummaryTable_forgetsToCriterionTable :
    identityCenteredExceptionalLocalCriterionSummaryTable.map
        (fun E => (E.triplet, E.criterion)) =
      identityCenteredExceptionalLocalCriterionTable := by
  unfold identityCenteredExceptionalLocalCriterionSummaryTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.criterion)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionSummary) =
        (fun E => (E.triplet, E.criterion)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionCoreViewTable_forgetsToCriterionTable

/-- Dépliage exact du critère empaqueté dans un résumé documentaire local. -/
theorem IdentityCenteredExceptionalLocalCriterionSummary.criterion_iff
    (E : IdentityCenteredExceptionalLocalCriterionSummary) :
    E.criterion ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
  simp [E.criterion_eq]

/--
Tout résumé documentaire local fournit, sous hypothèse de son critère,
un témoin explicite sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionSummary.hasExplicitWitness
    (E : IdentityCenteredExceptionalLocalCriterionSummary)
    (h : E.criterion) :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = E.triplet := by
  exact ⟨E.witnessOfCriterion h, E.witness_spec h⟩

/--
Sous hypothèse du critère empaqueté, le résumé documentaire local
implique bien l’appartenance à la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionSummary.inFamily
    (E : IdentityCenteredExceptionalLocalCriterionSummary)
    (h : E.criterion) :
    E.triplet ∈ identityCenteredTriplets := by
  have hcrit : satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
    simpa [E.criterion_eq] using h
  exact satisfiesExceptionalLocalPredicateOnIdentityTriplets_mem hcrit

/--
Sous hypothèse du critère empaqueté, le résumé documentaire local
implique bien le prédicat local exceptionnel.
-/
theorem IdentityCenteredExceptionalLocalCriterionSummary.localExceptional
    (E : IdentityCenteredExceptionalLocalCriterionSummary)
    (h : E.criterion) :
    isLocalExceptionalCandidate E.triplet := by
  have hcrit : satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
    simpa [E.criterion_eq] using h
  exact satisfiesExceptionalLocalPredicateOnIdentityTriplets_local hcrit

/--
Cas Couret : résumé documentaire local canonique dans la table locale
associée au critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionSummary :
    IdentityCenteredExceptionalLocalCriterionSummary :=
  canonicalIdentityCenteredExceptionalLocalCriterionSummary
    couretIdentityCenteredExceptionalLocalCriterionCoreView

/--
Dans le cas Couret, le critère local synthétique empaqueté
dans le résumé canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionSummary_criterion :
    couretIdentityCenteredExceptionalLocalCriterionSummary.criterion := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionSummary,
    canonicalIdentityCenteredExceptionalLocalCriterionSummary]
    using couretIdentityCenteredExceptionalLocalCriterionCoreView_criterion

/-- Témoin explicite canonique extrait du résumé local de Couret. -/
def couretIdentityCenteredExceptionalLocalCriterionSummaryWitness :
    IdentityCenteredExceptionalWitness :=
  couretIdentityCenteredExceptionalLocalCriterionSummary.witnessOfCriterion
    couretIdentityCenteredExceptionalLocalCriterionSummary_criterion

/--
Le témoin explicite canonique extrait du résumé local de Couret
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionSummaryWitness_triplet :
    couretIdentityCenteredExceptionalLocalCriterionSummaryWitness.candidate.triplet =
      couretTriplet := by
  exact
    couretIdentityCenteredExceptionalLocalCriterionSummary.witness_spec
      couretIdentityCenteredExceptionalLocalCriterionSummary_criterion

/--
Validation groupée minimale du cas Couret au niveau du résumé documentaire
local du critère local synthétique sur la famille identité.
-/
theorem couretExceptionalLocalCriterionSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionSummaryTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionSummaryTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ couretIdentityCenteredExceptionalLocalCriterionSummary.criterion
      ∧ couretIdentityCenteredExceptionalLocalCriterionSummaryWitness.candidate.triplet =
          couretTriplet := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionSummaryTable_length,
    identityCenteredExceptionalLocalCriterionSummaryTable_triplet,
    couretIdentityCenteredExceptionalLocalCriterionSummary_criterion,
    couretIdentityCenteredExceptionalLocalCriterionSummaryWitness_triplet
  ⟩

end

end CouretUnification.Core