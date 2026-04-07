import CouretUnification.Core.ExceptionalDecisionFinalViewShellOnIdentityTriplets
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
- aucune dépendance logique nouvelle au-delà de la couche finale de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewDecidableEntry where
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
def canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry
    (p : Triplet × ExceptionalDecisionValue) :
    IdentityCenteredExceptionalDecisionFinalViewDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = ExceptionalDecisionValue.exceptional)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la couche finale de vue des décisions sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewDecidableTable :
    List IdentityCenteredExceptionalDecisionFinalViewDecidableEntry :=
  identityCenteredExceptionalDecisionFinalViewShell.summary.rows.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry

/-- La table documentaire locale décidable finale a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_length :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewDecidableTable]
    using identityCenteredExceptionalDecisionFinalViewShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_triplet :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue documentaire finale `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalDecisionFinalViewDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewDecidableEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat de décision exceptionnelle sous-jacent.
-/
def IdentityCenteredExceptionalDecisionFinalViewDecidableEntry.decidable
    (E : IdentityCenteredExceptionalDecisionFinalViewDecidableEntry) :
    Decidable (E.value = ExceptionalDecisionValue.exceptional) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la décision finale de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry :
    IdentityCenteredExceptionalDecisionFinalViewDecidableEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_triplet

/--
Dans le cas Couret, la ligne documentaire décidable canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_cases

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat final de décision exceptionnelle.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewDecidable :
    Decidable couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire décidable finale de vue des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewDecidableTable_length,
    identityCenteredExceptionalDecisionFinalViewDecidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewDecidableTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewDecidableEntry_cases
  ⟩

end

end CouretUnification.Core