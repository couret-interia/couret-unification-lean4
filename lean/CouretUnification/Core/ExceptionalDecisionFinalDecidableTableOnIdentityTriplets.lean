import CouretUnification.Core.ExceptionalDecisionFinalShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale de décision déjà stabilisée ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale des décisions.
-/
structure IdentityCenteredExceptionalDecisionFinalDecidableEntry where
  triplet : Triplet
  value : ExceptionalDecisionValue
  predicate : Prop
  predicate_eq :
    predicate = (value = ExceptionalDecisionValue.exceptional)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un couple documentaire final déjà stabilisé `(triplet, valeur)`,
on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry
    (p : Triplet × ExceptionalDecisionValue) :
    IdentityCenteredExceptionalDecisionFinalDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = ExceptionalDecisionValue.exceptional)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la couche finale des décisions sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalDecidableTable :
    List IdentityCenteredExceptionalDecisionFinalDecidableEntry :=
  identityCenteredExceptionalDecisionFinalShell.summary.rows.map
    canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry

/-- La table documentaire locale décidable finale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_length :
    identityCenteredExceptionalDecisionFinalDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalDecidableTable]
    using identityCenteredExceptionalDecisionFinalShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_triplet :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue documentaire finale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalDecisionFinalDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalDecidableEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat de décision exceptionnelle sous-jacent.
-/
def IdentityCenteredExceptionalDecisionFinalDecidableEntry.decidable
    (E : IdentityCenteredExceptionalDecisionFinalDecidableEntry) :
    Decidable (E.value = ExceptionalDecisionValue.exceptional) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la décision finale.
-/
def couretIdentityCenteredExceptionalDecisionFinalDecidableEntry :
    IdentityCenteredExceptionalDecisionFinalDecidableEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_triplet

/--
Dans le cas Couret, la ligne documentaire décidable canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_cases

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat final de décision exceptionnelle.
-/
def couretIdentityCenteredExceptionalDecisionFinalDecidable :
    Decidable couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire décidable finale des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalDecidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalDecidableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalDecidableTable_length,
    identityCenteredExceptionalDecisionFinalDecidableTable_triplet,
    identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalDecidableEntry_cases
  ⟩

end

end CouretUnification.Core