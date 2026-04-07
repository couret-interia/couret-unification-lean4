import CouretUnification.Core.ExceptionalLocalCriterionDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- le critère local synthétique déjà isolé ;
- une décidabilité purement locale de ce critère ;
- une présentation booléenne documentaire correspondante.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionBooleanEntry where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  predicate : Prop
  predicate_eq :
    predicate = satisfiesExceptionalLocalPredicateOnIdentityTriplets triplet
  decidablePredicate : Decidable predicate
  value : Bool
  value_spec :
    value = @decide predicate decidablePredicate

/--
Constructeur canonique :
à partir d’une ligne documentaire décidable déjà construite,
on en extrait la présentation booléenne documentaire correspondante.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry
    (E : IdentityCenteredExceptionalLocalCriterionDecidableEntry) :
    IdentityCenteredExceptionalLocalCriterionBooleanEntry where
  triplet := E.triplet
  inFamily := E.inFamily
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  value := @decide E.predicate E.decidablePredicate
  value_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne
du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionBooleanTable :
    List IdentityCenteredExceptionalLocalCriterionBooleanEntry :=
  identityCenteredExceptionalLocalCriterionDecidableTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry

/-- La table documentaire locale booléenne a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionBooleanTable_length :
    identityCenteredExceptionalLocalCriterionBooleanTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionBooleanTable,
    identityCenteredExceptionalLocalCriterionDecidableTable_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionBooleanTable_triplet :
    identityCenteredExceptionalLocalCriterionBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionDecidableTable_triplet

/--
En oubliant la couche booléenne/documentaire et la décidabilité,
on retrouve exactement la table documentaire du critère local synthétique
déjà isolée.
-/
theorem identityCenteredExceptionalLocalCriterionBooleanTable_forgetsToCriterionTable :
    identityCenteredExceptionalLocalCriterionBooleanTable.map
        (fun E => (E.triplet, E.predicate)) =
      identityCenteredExceptionalLocalCriterionTable := by
  unfold identityCenteredExceptionalLocalCriterionBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.predicate)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry) =
        (fun E => (E.triplet, E.predicate)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionDecidableTable_forgetsToCriterionTable

/-- Dépliage exact du critère empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalLocalCriterionBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionBooleanEntry) :
    E.predicate ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire booléenne fournit bien
la décidabilité du critère local synthétique sous-jacent.
-/
def IdentityCenteredExceptionalLocalCriterionBooleanEntry.decidable
    (E : IdentityCenteredExceptionalLocalCriterionBooleanEntry) :
    Decidable (satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet) := by
  classical
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée au critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionBooleanEntry :
    IdentityCenteredExceptionalLocalCriterionBooleanEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry
    couretIdentityCenteredExceptionalLocalCriterionDecidableEntry

/--
Dans le cas Couret, le critère local synthétique empaqueté
dans la ligne booléenne canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_predicate :
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionBooleanEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry]
    using couretIdentityCenteredExceptionalLocalCriterionDecidableEntry_true

/--
Dans le cas Couret, la présentation booléenne documentaire associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_value_true :
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.value = true := by
  have hpred :
      couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.predicate := by
    exact couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_predicate
  unfold couretIdentityCenteredExceptionalLocalCriterionBooleanEntry
  simp [canonicalIdentityCenteredExceptionalLocalCriterionBooleanEntry,
    couretIdentityCenteredExceptionalLocalCriterionDecidableEntry_true]

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire booléenne du critère local synthétique sur la famille identité.
-/
theorem exceptionalLocalCriterionBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionBooleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanTable.map
          (fun E => (E.triplet, E.predicate)) =
            identityCenteredExceptionalLocalCriterionTable
      ∧ couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.value = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionBooleanTable_length,
    identityCenteredExceptionalLocalCriterionBooleanTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanTable_forgetsToCriterionTable,
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_predicate,
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_value_true
  ⟩

end

end CouretUnification.Core