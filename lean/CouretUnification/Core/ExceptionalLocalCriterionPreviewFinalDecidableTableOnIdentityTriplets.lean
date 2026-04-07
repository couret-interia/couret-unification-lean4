import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur booléenne documentaire finale déjà stabilisée ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry where
  triplet : Triplet
  value : Bool
  predicate : Prop
  predicate_eq :
    predicate = (value = true)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un couple documentaire final déjà stabilisé `(triplet, bool)`,
on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry
    (p : Triplet × Bool) :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = true)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la vue finale du critère local synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry :=
  identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry

/-- La table documentaire locale décidable finale a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_length :
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable]
    using identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue finale documentaire `(triplet, bool)` déjà stabilisée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_forgetsToPreviewPairs :
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows := by
  unfold identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry) :
    E.predicate ↔ E.value = true := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat booléen sous-jacent.
-/
def IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.decidable
    (E : IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry) :
    Decidable (E.value = true) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la vue finale du critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry]
    using congrArg Prod.fst
      couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair_eq

/--
Dans le cas Couret, le prédicat local empaqueté
dans la ligne décidable canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_predicate :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry]
    using congrArg Prod.snd
      couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair_eq

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat final empaqueté.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidable :
    Decidable couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire décidable finale sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewFinalDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry.predicate := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_length,
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewFinalDecidableTable_forgetsToPreviewPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalDecidableEntry_predicate
  ⟩

end

end CouretUnification.Core