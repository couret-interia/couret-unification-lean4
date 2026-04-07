import CouretUnification.Core.ExceptionalDecisionFinalViewDecidableTableOnIdentityTriplets
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
- aucune dépendance logique nouvelle au-delà de la couche finale de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewBooleanEntry where
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
def canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry
    (E : IdentityCenteredExceptionalDecisionFinalViewDecidableEntry) :
    IdentityCenteredExceptionalDecisionFinalViewBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la décision finale de vue sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewBooleanTable :
    List IdentityCenteredExceptionalDecisionFinalViewBooleanEntry :=
  identityCenteredExceptionalDecisionFinalViewDecidableTable.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry

/-- La table documentaire locale booléenne finale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_length :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewBooleanTable]
    using identityCenteredExceptionalDecisionFinalViewDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_triplet :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue documentaire finale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewDecidableTable_forgetsToDecisionPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalDecisionFinalViewBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewBooleanEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalDecisionFinalViewBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la décision finale de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry :
    IdentityCenteredExceptionalDecisionFinalViewBooleanEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry
    couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry

/--
Dans le cas Couret, la ligne documentaire booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_triplet

/--
Dans le cas Couret, la ligne documentaire booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewBooleanEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_cases

/--
Dans le cas Couret, la présentation booléenne explicite prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = false := by
  cases h : couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue <;> simp

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire booléenne explicite finale de vue des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = false) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewBooleanTable_length,
    identityCenteredExceptionalDecisionFinalViewBooleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewBooleanTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_boolValue_cases
  ⟩

end

end CouretUnification.Core