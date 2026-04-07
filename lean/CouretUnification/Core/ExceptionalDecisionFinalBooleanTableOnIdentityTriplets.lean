import CouretUnification.Core.ExceptionalDecisionFinalDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale de décision déjà stabilisée ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale des décisions.
-/
structure IdentityCenteredExceptionalDecisionFinalBooleanEntry where
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
à partir d’une ligne documentaire décidable finale déjà construite,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry
    (E : IdentityCenteredExceptionalDecisionFinalDecidableEntry) :
    IdentityCenteredExceptionalDecisionFinalBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la décision finale sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalBooleanTable :
    List IdentityCenteredExceptionalDecisionFinalBooleanEntry :=
  identityCenteredExceptionalDecisionFinalDecidableTable.map
    canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry

/-- La table documentaire locale booléenne finale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_length :
    identityCenteredExceptionalDecisionFinalBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalBooleanTable]
    using identityCenteredExceptionalDecisionFinalDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_triplet :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue documentaire finale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalDecisionFinalBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalBooleanEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalDecisionFinalBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la décision finale.
-/
def couretIdentityCenteredExceptionalDecisionFinalBooleanEntry :
    IdentityCenteredExceptionalDecisionFinalBooleanEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry
    couretIdentityCenteredExceptionalDecisionFinalDecidableEntry

/--
Dans le cas Couret, la ligne documentaire booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_triplet

/--
Dans le cas Couret, la ligne documentaire booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_cases

/--
Dans le cas Couret, la présentation booléenne explicite prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = false := by
  cases h : couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue with
  | false =>
      right
      simp
  | true =>
      left
      simp

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire booléenne explicite finale des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalBooleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = false) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalBooleanTable_length,
    identityCenteredExceptionalDecisionFinalBooleanTable_triplet,
    identityCenteredExceptionalDecisionFinalBooleanTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_cases,
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_boolValue_cases
  ⟩

end

end CouretUnification.Core