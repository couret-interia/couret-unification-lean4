import CouretUnification.Core.ExceptionalDecisionFinalViewSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement documentaire autour du résumé canonique
de la vue finale des décisions sur la famille finie des 21 triplets
centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste
des couples `(triplet, valeur de décision)` déjà stabilisés.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà du résumé de vue finale.
-/
structure IdentityCenteredExceptionalDecisionFinalViewShell where
  summary : IdentityCenteredExceptionalDecisionFinalViewSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell canonique purement documentaire :
on prend exactement le résumé de vue finale déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionFinalViewShell :
    IdentityCenteredExceptionalDecisionFinalViewShell where
  summary := identityCenteredExceptionalDecisionFinalViewSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ v : ExceptionalDecisionValue,
          (T, v) ∈ identityCenteredExceptionalDecisionFinalViewSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalDecisionFinalViewShell.predicate_spec
    (S : IdentityCenteredExceptionalDecisionFinalViewShell) :
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
theorem identityCenteredExceptionalDecisionFinalViewShell_true :
    identityCenteredExceptionalDecisionFinalViewShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalDecisionFinalViewShell.summary.rows.map Prod.fst := by
    rw [identityCenteredExceptionalDecisionFinalViewShell.summary.rows_fst]
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
def identityCenteredExceptionalDecisionFinalViewShellDecidable :
    Decidable identityCenteredExceptionalDecisionFinalViewShell.predicate :=
  identityCenteredExceptionalDecisionFinalViewShell.decidablePredicate

/--
Cas Couret : le shell sur la famille identité fournit bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewShell_entry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈
        identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
  exact
    identityCenteredExceptionalDecisionFinalViewShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée documentaire canonique du résumé de vue finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewShell_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_triplet

/--
Cas Couret : la valeur documentaire canonique du résumé de vue finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewShell_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_cases

/--
Validation groupée minimale du shell canonique de la vue finale
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewShellOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewShell.predicate
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈ identityCenteredExceptionalDecisionFinalViewShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewShell.summary.rows_len,
    identityCenteredExceptionalDecisionFinalViewShell.summary.rows_fst,
    identityCenteredExceptionalDecisionFinalViewShell_true,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewShell_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewShell_cases
  ⟩
  intro T hT
  exact identityCenteredExceptionalDecisionFinalViewShell_true T hT

end

end CouretUnification.Core