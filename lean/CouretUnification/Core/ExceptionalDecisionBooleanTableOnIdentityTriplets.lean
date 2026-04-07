import CouretUnification.Core.ExceptionalDecisionDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire de décision déjà stabilisée ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la décision canonique.
-/
structure IdentityCenteredExceptionalDecisionBooleanEntry where
  triplet : Triplet
  value : ExceptionalDecisionValue
  predicate : Prop
  predicate_eq :
    predicate = (value = ExceptionalDecisionValue.exceptional)
  decidablePredicate : Decidable predicate
  boolValue : Bool
  boolValue_spec :
    boolValue = @decide predicate decidablePredicate

/--
Constructeur canonique :
à partir d’une ligne documentaire décidable déjà construite,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalDecisionBooleanEntry
    (E : IdentityCenteredExceptionalDecisionDecidableEntry) :
    IdentityCenteredExceptionalDecisionBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la décision canonique sur la famille identité.
-/
def identityCenteredExceptionalDecisionBooleanTable :
    List IdentityCenteredExceptionalDecisionBooleanEntry :=
  identityCenteredExceptionalDecisionDecidableTable.map
    canonicalIdentityCenteredExceptionalDecisionBooleanEntry

/-- La table documentaire locale booléenne a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionBooleanTable_length :
    identityCenteredExceptionalDecisionBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionBooleanTable]
    using identityCenteredExceptionalDecisionDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionBooleanTable_triplet :
    identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue documentaire `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionBooleanTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalDecisionBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionBooleanEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalDecisionBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalDecisionBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la décision canonique.
-/
def couretIdentityCenteredExceptionalDecisionBooleanEntry :
    IdentityCenteredExceptionalDecisionBooleanEntry :=
  canonicalIdentityCenteredExceptionalDecisionBooleanEntry
    couretIdentityCenteredExceptionalDecisionDecidableEntry

/--
Dans le cas Couret, la ligne documentaire booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanEntry_triplet :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionDecidableEntry_triplet

/--
Dans le cas Couret, la ligne documentaire booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanEntry_cases :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionDecidableEntry_cases

/--
Dans le cas Couret, la présentation booléenne explicite prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanEntry_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = false := by
  cases h :
      couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue with
  | false =>
      right
      simp
  | true =>
      left
      simp

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire booléenne explicite des décisions sur la famille identité.
-/
theorem exceptionalDecisionBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionBooleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = false) := by
  exact ⟨
    identityCenteredExceptionalDecisionBooleanTable_length,
    identityCenteredExceptionalDecisionBooleanTable_triplet,
    identityCenteredExceptionalDecisionBooleanTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionBooleanEntry_triplet,
    couretIdentityCenteredExceptionalDecisionBooleanEntry_cases,
    couretIdentityCenteredExceptionalDecisionBooleanEntry_boolValue_cases
  ⟩

end

end CouretUnification.Core