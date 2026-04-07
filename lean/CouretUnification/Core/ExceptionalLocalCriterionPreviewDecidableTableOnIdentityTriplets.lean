import CouretUnification.Core.ExceptionalLocalCriterionPreviewShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur booléenne documentaire déjà extraite ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry where
  triplet : Triplet
  value : Bool
  predicate : Prop
  predicate_eq :
    predicate = (value = true)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un résumé documentaire de prévisualisation déjà construit,
on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry
    (E : IdentityCenteredExceptionalLocalCriterionPreviewSummary) :
    IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry where
  triplet := E.triplet
  value := E.value
  predicate := (E.value = true)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la prévisualisation du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionPreviewDecidableTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry :=
  identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry

/-- La table documentaire locale décidable a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewDecidableTable_length :
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewDecidableTable]
    using identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewDecidableTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable_triplet

/--
En oubliant la couche de décidabilité, on retrouve exactement
la projection documentaire `(triplet, bool)` de la table de résumés
de prévisualisation déjà empaquetée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewDecidableTable_forgetsToPreviewPairs :
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.map
        (fun E => (E.triplet, E.value)) := by
  unfold identityCenteredExceptionalLocalCriterionPreviewDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry) :
    E.predicate ↔ E.value = true := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat booléen sous-jacent.
-/
def IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry.decidable
    (E : IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry) :
    Decidable (E.value = true) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la prévisualisation du critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry :
    IdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry
    couretIdentityCenteredExceptionalLocalCriterionPreviewSummary

/--
Dans le cas Couret, le prédicat local empaqueté
dans la ligne décidable canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry]
    using couretIdentityCenteredExceptionalLocalCriterionPreviewSummary_value

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire décidable de prévisualisation sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewShell.summaryTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry.predicate := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable_length,
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewDecidableTable_forgetsToPreviewPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewDecidableEntry_predicate
  ⟩

end

end CouretUnification.Core