import CouretUnification.Core.ExceptionalDecisionFinalViewFinalShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale terminale de décision déjà stabilisée ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale terminale de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry where
  triplet : Triplet
  value : ExceptionalDecisionValue
  predicate : Prop
  predicate_eq :
    predicate = (value = ExceptionalDecisionValue.exceptional)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un couple documentaire final terminal déjà stabilisé
`(triplet, valeur)`, on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry
    (p : Triplet × ExceptionalDecisionValue) :
    IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = ExceptionalDecisionValue.exceptional)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la couche finale terminale de vue des décisions sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewFinalDecidableTable :
    List IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry :=
  identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry

/-- La table documentaire locale décidable finale terminale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewFinalDecidableTable]
    using identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue documentaire finale terminale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat de décision exceptionnelle sous-jacent.
-/
def IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.decidable
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry) :
    Decidable (E.value = ExceptionalDecisionValue.exceptional) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la décision finale terminale de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry :
    IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_triplet

/--
Dans le cas Couret, la ligne documentaire décidable canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_cases

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat final terminal de décision exceptionnelle.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidable :
    Decidable couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire décidable finale terminale de vue des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry_cases
  ⟩

end

end CouretUnification.Core