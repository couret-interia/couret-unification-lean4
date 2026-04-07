import CouretUnification.Core.ExceptionalLocalCriterionWitnessTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue documentaire minimale, sur la famille finie des 21 triplets centrés
sur l’identité, réunissant :

- un triplet de la famille ;
- le critère local synthétique déjà isolé ;
- le témoin explicite associé lorsque ce critère est satisfait.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionCoreView where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  criterion : Prop
  criterion_eq :
    criterion = satisfiesExceptionalLocalPredicateOnIdentityTriplets triplet
  witnessOfCriterion :
    criterion → IdentityCenteredExceptionalWitness
  witness_spec :
    ∀ h : criterion, (witnessOfCriterion h).candidate.triplet = triplet

/--
Constructeur canonique :
à partir d’une ligne documentaire locale déjà construite dans la table
des témoins, on extrait la vue minimale correspondante.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionCoreView
    (E : IdentityCenteredExceptionalLocalCriterionWitnessEntry) :
    IdentityCenteredExceptionalLocalCriterionCoreView where
  triplet := E.triplet
  inFamily := E.inFamily
  criterion := E.criterion
  criterion_eq := E.criterion_eq
  witnessOfCriterion := E.witnessOfCriterion
  witness_spec := E.witness_spec

/--
Table documentaire purement locale des vues minimales associées
au critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionCoreViewTable :
    List IdentityCenteredExceptionalLocalCriterionCoreView :=
  identityCenteredExceptionalLocalCriterionWitnessTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionCoreView

/-- La table documentaire locale des vues minimales a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionCoreViewTable_length :
    identityCenteredExceptionalLocalCriterionCoreViewTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionCoreViewTable,
    identityCenteredExceptionalLocalCriterionWitnessTable_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionCoreViewTable_triplet :
    identityCenteredExceptionalLocalCriterionCoreViewTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionCoreViewTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘ canonicalIdentityCenteredExceptionalLocalCriterionCoreView) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionWitnessTable_triplet

/--
En oubliant l’extracteur de témoin, on retrouve exactement la table
documentaire du critère local synthétique déjà isolée.
-/
theorem identityCenteredExceptionalLocalCriterionCoreViewTable_forgetsToCriterionTable :
    identityCenteredExceptionalLocalCriterionCoreViewTable.map
        (fun E => (E.triplet, E.criterion)) =
      identityCenteredExceptionalLocalCriterionTable := by
  unfold identityCenteredExceptionalLocalCriterionCoreViewTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.criterion)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionCoreView) =
        (fun E => (E.triplet, E.criterion)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionWitnessTable_forgetsToCriterionTable

/-- Dépliage exact du critère empaqueté dans une vue documentaire locale. -/
theorem IdentityCenteredExceptionalLocalCriterionCoreView.criterion_iff
    (E : IdentityCenteredExceptionalLocalCriterionCoreView) :
    E.criterion ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
  simp [E.criterion_eq]

/--
Toute vue documentaire locale fournit, sous hypothèse de son critère,
un témoin explicite sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionCoreView.hasExplicitWitness
    (E : IdentityCenteredExceptionalLocalCriterionCoreView)
    (h : E.criterion) :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = E.triplet := by
  exact ⟨E.witnessOfCriterion h, E.witness_spec h⟩

/--
Sous hypothèse du critère empaqueté, le témoin explicite extrait
reste bien dans la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionCoreView.witness_inFamily
    (E : IdentityCenteredExceptionalLocalCriterionCoreView)
    (h : E.criterion) :
    (E.witnessOfCriterion h).candidate.triplet ∈ identityCenteredTriplets := by
  simpa [E.witness_spec h] using (E.witnessOfCriterion h).inFamily

/--
Sous hypothèse du critère empaqueté, le témoin explicite extrait
satisfait bien le prédicat local exceptionnel.
-/
theorem IdentityCenteredExceptionalLocalCriterionCoreView.witness_localExceptional
    (E : IdentityCenteredExceptionalLocalCriterionCoreView)
    (h : E.criterion) :
    isLocalExceptionalCandidate E.triplet := by
  simpa [E.witness_spec h] using (E.witnessOfCriterion h).localExceptional

/--
Cas Couret : vue documentaire minimale canonique dans la table locale
associée au critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionCoreView :
    IdentityCenteredExceptionalLocalCriterionCoreView :=
  canonicalIdentityCenteredExceptionalLocalCriterionCoreView
    couretIdentityCenteredExceptionalLocalCriterionWitnessEntry

/--
Dans le cas Couret, le critère local synthétique empaqueté
dans la vue canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionCoreView_criterion :
    couretIdentityCenteredExceptionalLocalCriterionCoreView.criterion := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionCoreView,
    canonicalIdentityCenteredExceptionalLocalCriterionCoreView]
    using couretIdentityCenteredExceptionalLocalCriterionWitnessEntry_criterion

/-- Témoin explicite canonique extrait de la vue locale de Couret. -/
def couretIdentityCenteredExceptionalLocalCriterionCoreWitness :
    IdentityCenteredExceptionalWitness :=
  couretIdentityCenteredExceptionalLocalCriterionCoreView.witnessOfCriterion
    couretIdentityCenteredExceptionalLocalCriterionCoreView_criterion

/--
Le témoin explicite canonique extrait de la vue locale de Couret
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionCoreWitness_triplet :
    couretIdentityCenteredExceptionalLocalCriterionCoreWitness.candidate.triplet =
      couretTriplet := by
  exact
    couretIdentityCenteredExceptionalLocalCriterionCoreView.witness_spec
      couretIdentityCenteredExceptionalLocalCriterionCoreView_criterion

/--
Validation groupée minimale du cas Couret au niveau de la vue documentaire
locale du critère local synthétique sur la famille identité.
-/
theorem couretExceptionalLocalCriterionCoreViewOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionCoreViewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionCoreViewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ couretIdentityCenteredExceptionalLocalCriterionCoreView.criterion
      ∧ couretIdentityCenteredExceptionalLocalCriterionCoreWitness.candidate.triplet =
          couretTriplet := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionCoreViewTable_length,
    identityCenteredExceptionalLocalCriterionCoreViewTable_triplet,
    couretIdentityCenteredExceptionalLocalCriterionCoreView_criterion,
    couretIdentityCenteredExceptionalLocalCriterionCoreWitness_triplet
  ⟩

end

end CouretUnification.Core