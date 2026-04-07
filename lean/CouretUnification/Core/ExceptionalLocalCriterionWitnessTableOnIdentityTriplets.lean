import CouretUnification.Core.ExceptionalLocalCriterionTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalCandidateWitnessesOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire purement locale, sur la famille finie des 21 triplets
centrés sur l’identité :

- un triplet de la famille ;
- le critère local synthétique déjà isolé sur cette famille ;
- une extraction explicite de témoin lorsque ce critère est satisfait.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionWitnessEntry where
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
Constructeur canonique d’une ligne documentaire locale :
on part d’un triplet déjà dans la famille identité, on lui associe
le critère local synthétique correspondant, et l’extraction explicite
de témoin lorsqu’une preuve de ce critère est fournie.
-/
def mkIdentityCenteredExceptionalLocalCriterionWitnessEntry
    (T : Triplet) (hmem : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalLocalCriterionWitnessEntry where
  triplet := T
  inFamily := hmem
  criterion := satisfiesExceptionalLocalPredicateOnIdentityTriplets T
  criterion_eq := rfl
  witnessOfCriterion := fun h => Classical.choose h
  witness_spec := by
    intro h
    exact Classical.choose_spec h

/--
Table documentaire purement locale des témoins explicites associés
au critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionWitnessTable :
    List IdentityCenteredExceptionalLocalCriterionWitnessEntry :=
  identityCenteredTriplets.attach.map
    (fun T =>
      mkIdentityCenteredExceptionalLocalCriterionWitnessEntry
        T.1
        T.2)

/-- La table documentaire locale des témoins a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionWitnessTable_length :
    identityCenteredExceptionalLocalCriterionWitnessTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionWitnessTable, identityCenteredTriplets_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionWitnessTable_triplet :
    identityCenteredExceptionalLocalCriterionWitnessTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionWitnessTable
  simp [mkIdentityCenteredExceptionalLocalCriterionWitnessEntry]

/--
En oubliant les extracteurs de témoins, on retrouve exactement
la table documentaire du critère local synthétique déjà isolée.
-/
theorem identityCenteredExceptionalLocalCriterionWitnessTable_forgetsToCriterionTable :
    identityCenteredExceptionalLocalCriterionWitnessTable.map
        (fun E => (E.triplet, E.criterion)) =
      identityCenteredExceptionalLocalCriterionTable := by
  unfold identityCenteredExceptionalLocalCriterionWitnessTable
  unfold identityCenteredExceptionalLocalCriterionTable
  simp [mkIdentityCenteredExceptionalLocalCriterionWitnessEntry]

/-- Dépliage exact du critère empaqueté dans une ligne documentaire. -/
theorem IdentityCenteredExceptionalLocalCriterionWitnessEntry.criterion_iff
    (E : IdentityCenteredExceptionalLocalCriterionWitnessEntry) :
    E.criterion ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
  simp [E.criterion_eq]

/--
Toute ligne documentaire locale fournit, sous hypothèse de son critère,
un témoin explicite sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionWitnessEntry.hasExplicitWitness
    (E : IdentityCenteredExceptionalLocalCriterionWitnessEntry)
    (h : E.criterion) :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = E.triplet := by
  exact ⟨E.witnessOfCriterion h, E.witness_spec h⟩

/--
Sous hypothèse du critère empaqueté, le témoin explicite extrait
reste bien dans la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionWitnessEntry.witness_inFamily
    (E : IdentityCenteredExceptionalLocalCriterionWitnessEntry)
    (h : E.criterion) :
    (E.witnessOfCriterion h).candidate.triplet ∈ identityCenteredTriplets := by
  simpa [E.witness_spec h] using (E.witnessOfCriterion h).inFamily

/--
Sous hypothèse du critère empaqueté, le témoin explicite extrait
satisfait bien le prédicat local exceptionnel.
-/
theorem IdentityCenteredExceptionalLocalCriterionWitnessEntry.witness_localExceptional
    (E : IdentityCenteredExceptionalLocalCriterionWitnessEntry)
    (h : E.criterion) :
    isLocalExceptionalCandidate E.triplet := by
  simpa [E.witness_spec h] using (E.witnessOfCriterion h).localExceptional

/--
Cas Couret : ligne documentaire canonique dans la table locale
des témoins associés au critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionWitnessEntry :
    IdentityCenteredExceptionalLocalCriterionWitnessEntry :=
  mkIdentityCenteredExceptionalLocalCriterionWitnessEntry
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, le critère local synthétique empaqueté
dans la ligne canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionWitnessEntry_criterion :
    couretIdentityCenteredExceptionalLocalCriterionWitnessEntry.criterion := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionWitnessEntry,
    mkIdentityCenteredExceptionalLocalCriterionWitnessEntry]
    using couretExceptionalLocalPredicateOnIdentityTriplets_true

/-- Témoin explicite canonique extrait de la ligne locale de Couret. -/
def couretIdentityCenteredExceptionalLocalCriterionWitness :
    IdentityCenteredExceptionalWitness :=
  couretIdentityCenteredExceptionalLocalCriterionWitnessEntry.witnessOfCriterion
    couretIdentityCenteredExceptionalLocalCriterionWitnessEntry_criterion

/--
Le témoin explicite canonique extrait de la ligne locale de Couret
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionWitness_triplet :
    couretIdentityCenteredExceptionalLocalCriterionWitness.candidate.triplet =
      couretTriplet := by
  exact
    couretIdentityCenteredExceptionalLocalCriterionWitnessEntry.witness_spec
      couretIdentityCenteredExceptionalLocalCriterionWitnessEntry_criterion

/--
Validation groupée minimale du cas Couret au niveau de la table documentaire
locale des témoins associés au critère local synthétique.
-/
theorem couretExceptionalLocalCriterionWitnessTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionWitnessTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionWitnessTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ couretIdentityCenteredExceptionalLocalCriterionWitnessEntry.criterion
      ∧ couretIdentityCenteredExceptionalLocalCriterionWitness.candidate.triplet =
          couretTriplet := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionWitnessTable_length,
    identityCenteredExceptionalLocalCriterionWitnessTable_triplet,
    couretIdentityCenteredExceptionalLocalCriterionWitnessEntry_criterion,
    couretIdentityCenteredExceptionalLocalCriterionWitness_triplet
  ⟩

end

end CouretUnification.Core