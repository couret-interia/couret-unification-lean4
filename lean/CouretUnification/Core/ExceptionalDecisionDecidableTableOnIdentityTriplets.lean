import CouretUnification.Core.ExceptionalDecisionShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire de décision déjà stabilisée ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la décision canonique.
-/
structure IdentityCenteredExceptionalDecisionDecidableEntry where
  triplet : Triplet
  value : ExceptionalDecisionValue
  predicate : Prop
  predicate_eq :
    predicate = (value = ExceptionalDecisionValue.exceptional)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un couple documentaire déjà stabilisé `(triplet, valeur)`,
on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalDecisionDecidableEntry
    (p : Triplet × ExceptionalDecisionValue) :
    IdentityCenteredExceptionalDecisionDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = ExceptionalDecisionValue.exceptional)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la couche de décision canonique sur la famille identité.
-/
def identityCenteredExceptionalDecisionDecidableTable :
    List IdentityCenteredExceptionalDecisionDecidableEntry :=
  identityCenteredExceptionalDecisionShell.summary.rows.map
    canonicalIdentityCenteredExceptionalDecisionDecidableEntry

/-- La table documentaire locale décidable a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionDecidableTable_length :
    identityCenteredExceptionalDecisionDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionDecidableTable]
    using identityCenteredExceptionalDecisionShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionDecidableTable_triplet :
    identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue documentaire `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalDecisionDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionDecidableEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat de décision exceptionnel sous-jacent.
-/
def IdentityCenteredExceptionalDecisionDecidableEntry.decidable
    (E : IdentityCenteredExceptionalDecisionDecidableEntry) :
    Decidable (E.value = ExceptionalDecisionValue.exceptional) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la décision canonique.
-/
def couretIdentityCenteredExceptionalDecisionDecidableEntry :
    IdentityCenteredExceptionalDecisionDecidableEntry :=
  canonicalIdentityCenteredExceptionalDecisionDecidableEntry
    couretIdentityCenteredExceptionalDecisionSummaryEntry

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionDecidableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionSummaryEntry_triplet

/--
Dans le cas Couret, la ligne documentaire décidable canonique prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionDecidableEntry_cases :
    couretIdentityCenteredExceptionalDecisionDecidableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionDecidableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionSummaryEntry_cases

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat de décision exceptionnel.
-/
def couretIdentityCenteredExceptionalDecisionDecidable :
    Decidable couretIdentityCenteredExceptionalDecisionDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalDecisionDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire décidable des décisions sur la famille identité.
-/
theorem exceptionalDecisionDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionDecidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionDecidableEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionDecidableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionDecidableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    identityCenteredExceptionalDecisionDecidableTable_length,
    identityCenteredExceptionalDecisionDecidableTable_triplet,
    identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionDecidableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionDecidableEntry_cases
  ⟩

end

end CouretUnification.Core