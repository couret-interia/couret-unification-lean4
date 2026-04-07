import CouretUnification.Core.ExceptionalDecisionFinalViewFinalSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement documentaire autour du résumé canonique
de la vue finale terminale des décisions sur la famille finie des 21 triplets
centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste
des couples `(triplet, valeur de décision)` déjà stabilisés.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà du résumé terminal de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalShell where
  summary : IdentityCenteredExceptionalDecisionFinalViewFinalSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell canonique purement documentaire :
on prend exactement le résumé terminal de vue déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionFinalViewFinalShell :
    IdentityCenteredExceptionalDecisionFinalViewFinalShell where
  summary := identityCenteredExceptionalDecisionFinalViewFinalSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ v : ExceptionalDecisionValue,
          (T, v) ∈ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewFinalShell.predicate_spec
    (S : IdentityCenteredExceptionalDecisionFinalViewFinalShell) :
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
theorem identityCenteredExceptionalDecisionFinalViewFinalShell_true :
    identityCenteredExceptionalDecisionFinalViewFinalShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows.map Prod.fst := by
    rw [identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows_fst]
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
def identityCenteredExceptionalDecisionFinalViewFinalShellDecidable :
    Decidable identityCenteredExceptionalDecisionFinalViewFinalShell.predicate :=
  identityCenteredExceptionalDecisionFinalViewFinalShell.decidablePredicate

/--
Cas Couret : le shell sur la famille identité fournit bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalShell_entry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈
        identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée documentaire canonique du résumé terminal de vue
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalShell_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_triplet

/--
Cas Couret : la valeur documentaire canonique du résumé terminal de vue
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalShell_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_cases

/--
Validation groupée minimale du shell canonique de la vue finale terminale
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalShellOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalShell.predicate
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈ identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows_len,
    identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows_fst,
    identityCenteredExceptionalDecisionFinalViewFinalShell_true,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalShell_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalShell_cases
  ⟩
  intro T hT
  exact identityCenteredExceptionalDecisionFinalViewFinalShell_true T hT

end

end CouretUnification.Core