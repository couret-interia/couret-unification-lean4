import CouretUnification.Core.ExceptionalDecisionFinalViewFinalDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale terminale de décision déjà stabilisée ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale terminale de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry where
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
à partir d’une ligne documentaire décidable finale terminale déjà construite,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry) :
    IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la décision finale terminale de vue sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewFinalBooleanTable :
    List IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry :=
  identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry

/-- La table documentaire locale booléenne finale terminale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewFinalBooleanTable]
    using identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue documentaire finale terminale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_forgetsToDecisionPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la décision finale terminale de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry :
    IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry
    couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry

/--
Dans le cas Couret, la ligne documentaire booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_triplet

/--
Dans le cas Couret, la ligne documentaire booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_cases

/--
Dans le cas Couret, la présentation booléenne explicite prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = false := by
  cases h : couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue with
  | false =>
      right
      simp
  | true =>
      left
      simp

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire booléenne explicite finale terminale de vue des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = false) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_boolValue_cases
  ⟩

end

end CouretUnification.Core