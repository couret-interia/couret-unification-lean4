import CouretUnification.Core.ExceptionalLocalCriterionPreviewDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur booléenne documentaire de prévisualisation ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry where
  triplet : Triplet
  value : Bool
  predicate : Prop
  predicate_eq :
    predicate = (value = true)
  decidablePredicate : Decidable predicate
  boolValue : Bool
  boolValue_spec :
    boolValue = @decide predicate decidablePredicate

/--
Constructeur canonique :
à partir d’une ligne documentaire décidable de prévisualisation,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry
    (E : IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry) :
    IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne
de la prévisualisation du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionPreviewBooleanTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry :=
  identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry

/-- La table documentaire locale booléenne a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewBooleanTable]
    using identityCenteredExceptionalLocalCriterionPreviewDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la projection documentaire `(triplet, bool)` de la table décidable
de prévisualisation.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewBooleanTable_forgetsToPreviewPairs :
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
  unfold identityCenteredExceptionalLocalCriterionPreviewBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry) :
    E.predicate ↔ E.value = true := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la prévisualisation du critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry :
    IdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry
    couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry

/--
Dans le cas Couret, le prédicat local empaqueté
dans la ligne booléenne canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry_predicate

/--
Dans le cas Couret, la présentation booléenne explicite associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_boolValue_true :
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue = true := by
  unfold couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry
  simp [canonicalIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry,
    couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry_predicate]

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire booléenne explicite de prévisualisation sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry.boolValue = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewBooleanTable_forgetsToPreviewPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_predicate,
    couretIdentityCenteredExceptionalLocalCriterionPreviewBooleanEntry_boolValue_true
  ⟩

end

end CouretUnification.Core