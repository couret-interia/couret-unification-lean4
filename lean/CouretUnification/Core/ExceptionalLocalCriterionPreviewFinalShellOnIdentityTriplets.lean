import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du résumé documentaire final
sur la famille finie des 21 triplets centrés sur l’identité.

On ne décide ici qu’un prédicat documentaire minimal :
tout triplet de `identityCenteredTriplets` apparaît dans la liste finale
des couples `(triplet, bool)` déjà stabilisés.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewFinalShell where
  summary : IdentityCenteredExceptionalLocalCriterionPreviewFinalSummary
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ b : Bool, (T, b) ∈ summary.rows
  decidablePredicate : Decidable predicate

/--
Shell canonique purement locale :
on prend exactement le résumé documentaire final déjà construit,
muni du prédicat documentaire minimal de couverture des triplets
de la famille identité par les couples `(triplet, bool)`.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalShell :
    IdentityCenteredExceptionalLocalCriterionPreviewFinalShell where
  summary := identityCenteredExceptionalLocalCriterionPreviewFinalSummary
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        ∃ b : Bool, (T, b) ∈
          identityCenteredExceptionalLocalCriterionPreviewFinalSummary.rows
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat documentaire local
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionPreviewFinalShell.predicate_spec
    (S : IdentityCenteredExceptionalLocalCriterionPreviewFinalShell) :
    S.predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          ∃ b : Bool, (T, b) ∈ S.summary.rows := by
  exact S.predicate_eq

/--
Le prédicat documentaire local porté par le shell canonique est bien vérifié :
tout triplet de la famille identité apparaît bien dans la liste finale
des couples `(triplet, bool)`.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewFinalShell_true :
    identityCenteredExceptionalLocalCriterionPreviewFinalShell.predicate := by
  intro T hmem
  have hmem' :
      T ∈ identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows.map Prod.fst := by
    rw [identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows_fst]
    exact hmem
  rcases List.mem_map.1 hmem' with ⟨p, hp, hpT⟩
  cases p with
  | mk t b =>
      simp at hpT
      cases hpT
      exact ⟨b, by simpa using hp⟩

/--
Version calculatoire : décidabilité locale purement documentaire
du prédicat empaqueté par le shell canonique.
-/
def identityCenteredExceptionalLocalCriterionPreviewFinalShellDecidable :
    Decidable identityCenteredExceptionalLocalCriterionPreviewFinalShell.predicate :=
  identityCenteredExceptionalLocalCriterionPreviewFinalShell.decidablePredicate

/--
Cas Couret : le shell local sur la famille identité fournit bien
une entrée finale documentaire pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalShell_entry :
    ∃ b : Bool,
      (couretTriplet, b) ∈
        identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows := by
  exact
    identityCenteredExceptionalLocalCriterionPreviewFinalShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : le couple documentaire canonique final
reste bien `(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewFinalShell_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair_eq

/--
Validation groupée minimale du shell purement local
sur la famille identité :
- le résumé documentaire final a bien longueur 21 ;
- sa projection sur les triplets redonne bien la famille identité ;
- le prédicat empaqueté est vrai ;
- le cas Couret admet bien une entrée documentaire finale ;
- le couple canonique de Couret vaut bien `(couretTriplet, true)`.
-/
theorem exceptionalLocalCriterionPreviewFinalShellOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewFinalShell.predicate
      ∧ (∃ b : Bool,
            (couretTriplet, b) ∈
              identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows)
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalSummaryPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows_len,
    identityCenteredExceptionalLocalCriterionPreviewFinalShell.summary.rows_fst,
    identityCenteredExceptionalLocalCriterionPreviewFinalShell_true,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalShell_entry,
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalShell_pair
  ⟩

end

end CouretUnification.Core