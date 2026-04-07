import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement documentaire autour du résumé canonique
de la vue finale terminale ultime des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste
des couples `(triplet, valeur de décision)` déjà stabilisés.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà du résumé terminal ultime de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalShell where
  summary : IdentityCenteredExceptionalDecisionFinalViewFinalFinalSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell canonique purement documentaire :
on prend exactement le résumé terminal ultime de vue déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalShell :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalShell where
  summary := identityCenteredExceptionalDecisionFinalViewFinalFinalSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ v : ExceptionalDecisionValue,
          (T, v) ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalFinalShell.predicate_spec
    (S : IdentityCenteredExceptionalDecisionFinalViewFinalFinalShell) :
    S.predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ S.summary.rows := by
  exact S.predicate_eq

/--
Le prédicat documentaire local porté par le shell canonique est bien vérifié :
tout triplet de la famille identité apparaît bien dans la liste
des couples `(triplet, valeur de décision)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalShell_true :
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈
        identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows.map
          Prod.fst := by
    rw [identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows_fst]
    exact hmem
  rcases List.mem_map.1 hmem' with ⟨p, hp, hpT⟩
  cases p with
  | mk t v =>
      simp at hpT
      cases hpT
      exact ⟨v, by simpa using hp⟩

/--
Version calculatoire : décidabilité purement documentaire
du prédicat empaqueté par le shell canonique.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalShellDecidable :
    Decidable identityCenteredExceptionalDecisionFinalViewFinalFinalShell.predicate :=
  identityCenteredExceptionalDecisionFinalViewFinalFinalShell.decidablePredicate

/--
Cas Couret : le shell sur la famille identité fournit bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalShell_entry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈
        identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée documentaire canonique du résumé terminal ultime de vue
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalShell_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.1 =
      couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_triplet

/--
Cas Couret : la valeur documentaire canonique du résumé terminal ultime de vue
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalShell_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_cases

/--
Validation groupée minimale du shell canonique de la vue finale terminale ultime
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalShellOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalShell.predicate
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈
                identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.1 =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows_len,
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows_fst,
    identityCenteredExceptionalDecisionFinalViewFinalFinalShell_true,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalShell_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalShell_cases
  ⟩
  intro T hT
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalShell_true T hT

end

end CouretUnification.Core