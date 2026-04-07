import CouretUnification.Core.ExceptionalLocalCriterionShellOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Ligne documentaire décidable purement locale, sur la famille finie des
21 triplets centrés sur l’identité :

- un triplet de la famille ;
- le critère local synthétique déjà isolé ;
- une décidabilité purement locale de ce critère.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionDecidableEntry where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  predicate : Prop
  predicate_eq :
    predicate = satisfiesExceptionalLocalPredicateOnIdentityTriplets triplet
  decidablePredicate : Decidable predicate

/--
Constructeur canonique d’une ligne documentaire décidable locale :
à partir d’un triplet déjà dans la famille identité, on lui associe
le critère local synthétique correspondant et sa décidabilité locale
(classique, purement documentaire).
-/
def mkIdentityCenteredExceptionalLocalCriterionDecidableEntry
    (T : Triplet) (hmem : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalLocalCriterionDecidableEntry where
  triplet := T
  inFamily := hmem
  predicate := satisfiesExceptionalLocalPredicateOnIdentityTriplets T
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Table documentaire purement locale de la décidabilité du critère local
synthétique sur la famille identité.
-/
def identityCenteredExceptionalLocalCriterionDecidableTable :
    List IdentityCenteredExceptionalLocalCriterionDecidableEntry :=
  identityCenteredTriplets.attach.map
    (fun T =>
      mkIdentityCenteredExceptionalLocalCriterionDecidableEntry
        T.1
        T.2)

/-- La table documentaire locale décidable a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionDecidableTable_length :
    identityCenteredExceptionalLocalCriterionDecidableTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionDecidableTable,
    identityCenteredTriplets_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionDecidableTable_triplet :
    identityCenteredExceptionalLocalCriterionDecidableTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionDecidableTable
  simp [mkIdentityCenteredExceptionalLocalCriterionDecidableEntry]

/--
En oubliant la décidabilité, on retrouve exactement la table documentaire
du critère local synthétique déjà isolée.
-/
theorem identityCenteredExceptionalLocalCriterionDecidableTable_forgetsToCriterionTable :
    identityCenteredExceptionalLocalCriterionDecidableTable.map
        (fun E => (E.triplet, E.predicate)) =
      identityCenteredExceptionalLocalCriterionTable := by
  unfold identityCenteredExceptionalLocalCriterionDecidableTable
  unfold identityCenteredExceptionalLocalCriterionTable
  simp [mkIdentityCenteredExceptionalLocalCriterionDecidableEntry]

/-- Dépliage exact du critère empaqueté dans une ligne documentaire décidable. -/
theorem IdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate_iff
    (E : IdentityCenteredExceptionalLocalCriterionDecidableEntry) :
    E.predicate ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet := by
  simp [E.predicate_eq]

/--
Version calculatoire : une ligne documentaire décidable fournit bien une
décidabilité du critère local synthétique sous-jacent.
-/
def IdentityCenteredExceptionalLocalCriterionDecidableEntry.decidable
    (E : IdentityCenteredExceptionalLocalCriterionDecidableEntry) :
    Decidable (satisfiesExceptionalLocalPredicateOnIdentityTriplets E.triplet) := by
  classical
  simpa [E.predicate_eq] using E.decidablePredicate

/--
Cas Couret : ligne documentaire décidable canonique dans la table locale
associée au critère local synthétique.
-/
def couretIdentityCenteredExceptionalLocalCriterionDecidableEntry :
    IdentityCenteredExceptionalLocalCriterionDecidableEntry :=
  mkIdentityCenteredExceptionalLocalCriterionDecidableEntry
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, le critère local synthétique empaqueté
dans la ligne décidable canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionDecidableEntry_true :
    couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionDecidableEntry,
    mkIdentityCenteredExceptionalLocalCriterionDecidableEntry]
    using couretExceptionalLocalPredicateOnIdentityTriplets_true

/--
Version calculatoire spécialisée au cas Couret :
décidabilité locale du critère local synthétique empaqueté.
-/
def couretIdentityCenteredExceptionalLocalCriterionDecidable :
    Decidable couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate :=
  couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.decidablePredicate

/--
Validation groupée minimale du cas Couret au niveau de la table
documentaire décidable du critère local synthétique sur la famille identité.
-/
theorem exceptionalLocalCriterionDecidableTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionDecidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionDecidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionDecidableTable.map
          (fun E => (E.triplet, E.predicate)) =
            identityCenteredExceptionalLocalCriterionTable
      ∧ couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionDecidableTable_length,
    identityCenteredExceptionalLocalCriterionDecidableTable_triplet,
    identityCenteredExceptionalLocalCriterionDecidableTable_forgetsToCriterionTable,
    couretIdentityCenteredExceptionalLocalCriterionDecidableEntry_true
  ⟩

end

end CouretUnification.Core