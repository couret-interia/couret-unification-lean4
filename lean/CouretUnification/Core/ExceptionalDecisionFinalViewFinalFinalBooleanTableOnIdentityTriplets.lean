import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale terminale ultime de décision déjà stabilisée ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale terminale ultime de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry where
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
à partir d’une ligne documentaire décidable finale terminale ultime déjà construite,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry) :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la décision finale terminale ultime de vue sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable :
    List IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry :=
  identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry

/-- La table documentaire locale booléenne finale terminale ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable]
    using identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue documentaire finale terminale ultime `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_forgetsToDecisionPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la décision finale terminale ultime de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry

/--
Dans le cas Couret, la ligne documentaire booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_triplet

/--
Dans le cas Couret, la ligne documentaire booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_cases

/--
Dans le cas Couret, la présentation booléenne explicite prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = false := by
  cases h : couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue with
  | false =>
      right
      simp
  | true =>
      left
      simp

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire booléenne explicite finale terminale ultime de vue des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = false) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_boolValue_cases
  ⟩

end

end CouretUnification.Core