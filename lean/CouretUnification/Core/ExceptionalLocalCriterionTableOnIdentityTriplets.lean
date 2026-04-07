import CouretUnification.Core.ExceptionalLocalPredicateOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Table documentaire purement locale du critère local synthétique
sur la famille finie des 21 triplets centrés sur l’identité.

À chaque triplet de `identityCenteredTriplets`, on associe le prédicat
local synthétique déjà isolé :
` satisfiesExceptionalLocalPredicateOnIdentityTriplets T `.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
def identityCenteredExceptionalLocalCriterionTable : List (Triplet × Prop) :=
  identityCenteredTriplets.map
    (fun T => (T, satisfiesExceptionalLocalPredicateOnIdentityTriplets T))

/-- La table documentaire locale du critère synthétique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionTable_length :
    identityCenteredExceptionalLocalCriterionTable.length = 21 := by
  simp [identityCenteredExceptionalLocalCriterionTable, identityCenteredTriplets_length]

/-- La projection sur la première composante redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionTable_fst :
    identityCenteredExceptionalLocalCriterionTable.map Prod.fst = identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionTable
  rw [List.map_map]
  have hfun :
      (Prod.fst ∘ fun T => (T, satisfiesExceptionalLocalPredicateOnIdentityTriplets T)) =
        (fun T => T) := by
    funext T
    rfl
  rw [hfun]
  simp

/--
Version transportée du critère local synthétique sur la famille identité :
on demande explicitement l’appartenance à `identityCenteredTriplets`
et la satisfaction du critère local synthétique déjà isolé.
-/
def isExceptionalLocalCriterionOnIdentityTriplets (T : Triplet) : Prop :=
  T ∈ identityCenteredTriplets
    ∧ satisfiesExceptionalLocalPredicateOnIdentityTriplets T

/--
Le transport explicite sur la famille identité est équivalent
au seul critère local synthétique, puisque celui-ci implique déjà
l’appartenance à la famille.
-/
theorem isExceptionalLocalCriterionOnIdentityTriplets_iff
    {T : Triplet} :
    isExceptionalLocalCriterionOnIdentityTriplets T ↔
      satisfiesExceptionalLocalPredicateOnIdentityTriplets T := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨
      satisfiesExceptionalLocalPredicateOnIdentityTriplets_mem h,
      h
    ⟩

/--
Le transport explicite du critère local synthétique sur la famille identité
est équivalent au prédicat transporté précédent
`isExceptionalCandidateOnIdentityTriplets`.
-/
theorem isExceptionalLocalCriterionOnIdentityTriplets_transport_iff
    {T : Triplet} :
    isExceptionalLocalCriterionOnIdentityTriplets T ↔
      isExceptionalCandidateOnIdentityTriplets T := by
  constructor
  · intro h
    exact
      (satisfiesExceptionalLocalPredicateOnIdentityTriplets_iff (T := T)).mp h.2
  · intro h
    exact ⟨
      h.1,
      (satisfiesExceptionalLocalPredicateOnIdentityTriplets_iff (T := T)).mpr h
    ⟩

/--
Cas Couret : le triplet distingué satisfait bien le critère local synthétique
transporté sur la famille identité.
-/
theorem couretTriplet_isExceptionalLocalCriterionOnIdentityTriplets :
    isExceptionalLocalCriterionOnIdentityTriplets couretTriplet := by
  exact ⟨
    couretExceptionalLocalPredicateOnIdentityTriplets_mem,
    couretExceptionalLocalPredicateOnIdentityTriplets_true
  ⟩

/--
Validation groupée minimale du cas Couret au niveau de la table documentaire
du critère local synthétique sur la famille identité.
-/
theorem couretExceptionalLocalCriterionTableOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionTable.map Prod.fst =
          identityCenteredTriplets
      ∧ isExceptionalLocalCriterionOnIdentityTriplets couretTriplet := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionTable_length,
    identityCenteredExceptionalLocalCriterionTable_fst,
    couretTriplet_isExceptionalLocalCriterionOnIdentityTriplets
  ⟩

end

end CouretUnification.Core