import CouretUnification.Core.ExceptionalDecisionSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du résumé documentaire canonique
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste
des couples `(triplet, valeur de décision)` déjà stabilisés.

On n’introduit encore :
- aucun raffinement analytique supplémentaire ;
- aucune structure hors de la famille identité ;
- aucune dépendance logique nouvelle au-delà du résumé canonique.
-/
structure IdentityCenteredExceptionalDecisionShell where
  summary : IdentityCenteredExceptionalDecisionSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ v : ExceptionalDecisionValue, (T, v) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell canonique purement locale :
on prend exactement le résumé documentaire des décisions déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionShell :
    IdentityCenteredExceptionalDecisionShell where
  summary := identityCenteredExceptionalDecisionSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ v : ExceptionalDecisionValue,
          (T, v) ∈ identityCenteredExceptionalDecisionSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalDecisionShell.predicate_spec
    (S : IdentityCenteredExceptionalDecisionShell) :
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
theorem identityCenteredExceptionalDecisionShell_true :
    identityCenteredExceptionalDecisionShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalDecisionShell.summary.rows.map Prod.fst := by
    rw [identityCenteredExceptionalDecisionShell.summary.rows_fst]
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
def identityCenteredExceptionalDecisionShellDecidable :
    Decidable identityCenteredExceptionalDecisionShell.predicate :=
  identityCenteredExceptionalDecisionShell.decidablePredicate

/--
Cas Couret : le shell local sur la famille identité fournit bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionShell_entry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈ identityCenteredExceptionalDecisionShell.summary.rows := by
  exact
    identityCenteredExceptionalDecisionShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée documentaire canonique du résumé
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionShell_triplet :
    couretIdentityCenteredExceptionalDecisionSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionSummaryEntry_triplet

/--
Cas Couret : la valeur documentaire canonique du résumé
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionShell_cases :
    couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionSummaryEntry_cases

/--
Validation groupée minimale du shell canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionShellOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionShell.predicate
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈ identityCenteredExceptionalDecisionShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalDecisionSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionShell.summary.rows_len,
    identityCenteredExceptionalDecisionShell.summary.rows_fst,
    identityCenteredExceptionalDecisionShell_true,
    ?_,
    couretIdentityCenteredExceptionalDecisionShell_triplet,
    couretIdentityCenteredExceptionalDecisionShell_cases
  ⟩
  intro T hT
  exact identityCenteredExceptionalDecisionShell_true T hT

end

end CouretUnification.Core