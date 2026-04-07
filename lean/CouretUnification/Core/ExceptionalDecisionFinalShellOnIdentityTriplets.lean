import CouretUnification.Core.ExceptionalDecisionFinalSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du résumé documentaire final
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste finale
des couples `(triplet, valeur de décision)` déjà stabilisés.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà du résumé final canonique.
-/
structure IdentityCenteredExceptionalDecisionFinalShell where
  summary : IdentityCenteredExceptionalDecisionFinalSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell final canonique purement local :
on prend exactement le résumé documentaire final déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionFinalShell :
    IdentityCenteredExceptionalDecisionFinalShell where
  summary := identityCenteredExceptionalDecisionFinalSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ v : ExceptionalDecisionValue,
          (T, v) ∈ identityCenteredExceptionalDecisionFinalSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalDecisionFinalShell.predicate_spec
    (S : IdentityCenteredExceptionalDecisionFinalShell) :
    S.predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ S.summary.rows := by
  exact S.predicate_eq

/--
Le prédicat documentaire local porté par le shell canonique est bien vérifié :
tout triplet de la famille identité apparaît bien dans la liste finale
des couples `(triplet, valeur de décision)`.
-/
theorem identityCenteredExceptionalDecisionFinalShell_true :
    identityCenteredExceptionalDecisionFinalShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalDecisionFinalShell.summary.rows.map Prod.fst := by
    rw [identityCenteredExceptionalDecisionFinalShell.summary.rows_fst]
    exact hmem
  rcases List.mem_map.1 hmem' with ⟨p, hp, hpT⟩
  cases p with
  | mk t v =>
      simp at hpT
      cases hpT
      exact ⟨v, by simpa using hp⟩

/--
Version calculatoire : décidabilité locale purement documentaire
du prédicat empaqueté par le shell canonique.
-/
def identityCenteredExceptionalDecisionFinalShellDecidable :
    Decidable identityCenteredExceptionalDecisionFinalShell.predicate :=
  identityCenteredExceptionalDecisionFinalShell.decidablePredicate

/--
Cas Couret : le shell final sur la famille identité fournit bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalShell_entry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈
        identityCenteredExceptionalDecisionFinalShell.summary.rows := by
  exact
    identityCenteredExceptionalDecisionFinalShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée documentaire canonique finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalShell_triplet :
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_triplet

/--
Cas Couret : la valeur documentaire canonique finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalShell_cases :
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_cases

/--
Validation groupée minimale du shell final canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalShellOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalShell.predicate
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈ identityCenteredExceptionalDecisionFinalShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalShell.summary.rows_len,
    identityCenteredExceptionalDecisionFinalShell.summary.rows_fst,
    identityCenteredExceptionalDecisionFinalShell_true,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalShell_triplet,
    couretIdentityCenteredExceptionalDecisionFinalShell_cases
  ⟩
  intro T hT
  exact identityCenteredExceptionalDecisionFinalShell_true T hT

end

end CouretUnification.Core