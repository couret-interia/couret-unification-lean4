import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- la valeur documentaire finale terminale ultime de décision déjà stabilisée ;
- un prédicat propositionnel purement local correspondant ;
- sa décidabilité documentaire.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà de la couche finale terminale ultime de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry where
  triplet : Triplet
  value : ExceptionalDecisionValue
  predicate : Prop
  predicate_eq :
    predicate = (value = ExceptionalDecisionValue.exceptional)
  decidablePredicate : Decidable predicate

/--
Constructeur canonique :
à partir d’un couple documentaire final terminal ultime déjà stabilisé
`(triplet, valeur)`, on en extrait la version décidable purement locale.
-/
def canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry
    (p : Triplet × ExceptionalDecisionValue) :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry where
  triplet := p.1
  value := p.2
  predicate := (p.2 = ExceptionalDecisionValue.exceptional)
  predicate_eq := rfl
  decidablePredicate := by
    infer_instance

/--
Table documentaire purement locale de la décidabilité associée
à la couche finale terminale ultime de vue des décisions sur la famille identité.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable :
    List IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry :=
  identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows.map
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry

/-- La table documentaire locale décidable finale terminale ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.length = 21 := by
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable]
    using identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry) =
        Prod.fst := by
    funext p
    cases p
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows_fst

/--
En oubliant la couche de décidabilité, on retrouve exactement
la vue documentaire finale terminale ultime `(triplet, valeur)` déjà stabilisée.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_forgetsToDecisionPairs :
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows := by
  unfold identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry) =
        (fun p => p) := by
    funext p
    cases p
    rfl
  rw [hfun]
  rfl

/-- Dépliage exact du prédicat empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry) :
    E.predicate ↔ E.value = ExceptionalDecisionValue.exceptional := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien
la décidabilité du prédicat de décision exceptionnelle sous-jacent.
-/
def IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.decidable
    (E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry) :
    Decidable (E.value = ExceptionalDecisionValue.exceptional) := by
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée à la décision finale terminale ultime de vue.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry :=
  canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry

/--
Dans le cas Couret, la ligne documentaire décidable canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_triplet

/--
Dans le cas Couret, la ligne documentaire décidable canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry,
    canonicalIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry]
    using couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_cases

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du prédicat final terminal ultime de décision exceptionnelle.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidable :
    Decidable
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas canonique au niveau de la table
documentaire décidable finale terminale ultime de vue des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_forgetsToDecisionPairs,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry_cases
  ⟩

end

end CouretUnification.Core