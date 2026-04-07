import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalDecidableTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire booléenne purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur booléenne documentaire finale déjà stabilisée ;
- le prédicat propositionnel local associé ;
- sa décidabilité ;
- une présentation booléenne explicite de ce prédicat.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry where
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
à partir d’une ligne documentaire décidable finale déjà construite,
on en extrait la présentation booléenne documentaire explicite.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry
    (E : IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry) :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry where
  triplet := E.triplet
  value := E.value
  predicate := E.predicate
  predicate_eq := E.predicate_eq
  decidablePredicate := E.decidablePredicate
  boolValue := @decide E.predicate E.decidablePredicate
  boolValue_spec := rfl

/--
Table documentaire purement locale de la présentation booléenne explicite
de la vue finale du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry :=
  identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry

/-- La table documentaire locale booléenne finale a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable]
    using identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_length

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_triplet

/--
En oubliant la couche booléenne explicite, on retrouve exactement
la vue finale documentaire `(triplet, bool)` déjà stabilisée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_forgetsToPreviewPairs :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows := by
  unfold identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_forgetsToPreviewPairs

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire booléenne. -/
theorem IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry) :
    E.predicate ↔ E.value = true := by
  simp [E.predicate_eq]

/--
Dans une ligne documentaire booléenne, la présentation booléenne explicite
coïncide bien avec `decide` appliqué au prédicat local empaqueté.
-/
theorem IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.boolValue_eq_decide
    (E : IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry) :
    E.boolValue = @decide E.predicate E.decidablePredicate := by
  exact E.boolValue_spec

/--
Cas Couret : ligne documentaire booléenne canonique dans la table locale
associée à la vue finale du critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry

/--
Dans le cas Couret, le prédicat local empaqueté
dans la ligne booléenne canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_predicate

/--
Dans le cas Couret, la présentation booléenne explicite associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_boolValue_true :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.boolValue = true := by
  unfold couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry
  simp [canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_predicate]

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire booléenne explicite finale sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalBooleanTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry.boolValue = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalBooleanTable_forgetsToPreviewPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_predicate,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalBooleanEntry_boolValue_true
  ⟩

end

end CouretUnification.Core