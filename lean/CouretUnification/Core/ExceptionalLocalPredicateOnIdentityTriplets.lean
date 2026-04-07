import CouretUnification.Core.ExceptionalCandidateWitnessesOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Prédicat local synthétique, sur la famille finie des 21 triplets centrés sur
l’identité, dérivé des témoins explicites déjà empaquetés :

un triplet satisfait ce prédicat s’il admet un témoin explicite
`IdentityCenteredExceptionalWitness` sur cette famille.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
def satisfiesExceptionalLocalPredicateOnIdentityTriplets (T : Triplet) : Prop :=
  ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = T

/--
Introduction canonique du prédicat synthétique
à partir d’un témoin explicite déjà empaqueté.
-/
theorem IdentityCenteredExceptionalWitness.satisfiesLocalPredicate
    (W : IdentityCenteredExceptionalWitness) :
    satisfiesExceptionalLocalPredicateOnIdentityTriplets W.candidate.triplet := by
  exact ⟨W, rfl⟩

/--
Élimination minimale : le prédicat synthétique implique bien
l’appartenance à la famille identité.
-/
theorem satisfiesExceptionalLocalPredicateOnIdentityTriplets_mem
    {T : Triplet}
    (h : satisfiesExceptionalLocalPredicateOnIdentityTriplets T) :
    T ∈ identityCenteredTriplets := by
  rcases h with ⟨W, rfl⟩
  exact W.inFamily

/--
Élimination minimale : le prédicat synthétique implique bien
la satisfaction du prédicat local exceptionnel.
-/
theorem satisfiesExceptionalLocalPredicateOnIdentityTriplets_local
    {T : Triplet}
    (h : satisfiesExceptionalLocalPredicateOnIdentityTriplets T) :
    isLocalExceptionalCandidate T := by
  rcases h with ⟨W, rfl⟩
  exact W.localExceptional

/--
Le prédicat synthétique dérivé des témoins explicites
est équivalent au prédicat transporté précédent sur la famille identité.
-/
theorem satisfiesExceptionalLocalPredicateOnIdentityTriplets_iff
    {T : Triplet} :
    satisfiesExceptionalLocalPredicateOnIdentityTriplets T ↔
      isExceptionalCandidateOnIdentityTriplets T := by
  constructor
  · intro h
    rcases h with ⟨W, rfl⟩
    exact W.toPredicate
  · intro h
    exact isExceptionalCandidateOnIdentityTriplets_hasExplicitWitness h

/--
Version existentielle minimale :
le prédicat synthétique fournit bien un témoin explicite empaqueté.
-/
theorem satisfiesExceptionalLocalPredicateOnIdentityTriplets_hasWitness
    {T : Triplet}
    (h : satisfiesExceptionalLocalPredicateOnIdentityTriplets T) :
    Nonempty IdentityCenteredExceptionalWitness := by
  rcases h with ⟨W, _hW⟩
  exact ⟨W⟩

/--
Cas Couret : prédicat local synthétique canonique
sur la famille identité.
-/
def couretExceptionalLocalPredicateOnIdentityTriplets : Prop :=
  satisfiesExceptionalLocalPredicateOnIdentityTriplets couretTriplet

/--
Dans le cas Couret, le prédicat local synthétique
sur la famille identité est bien satisfait.
-/
theorem couretExceptionalLocalPredicateOnIdentityTriplets_true :
    couretExceptionalLocalPredicateOnIdentityTriplets := by
  exact couretIdentityCenteredExceptionalWitness.satisfiesLocalPredicate

/--
Dans le cas Couret, le prédicat synthétique implique bien
l’appartenance à la famille identité.
-/
theorem couretExceptionalLocalPredicateOnIdentityTriplets_mem :
    couretTriplet ∈ identityCenteredTriplets := by
  exact satisfiesExceptionalLocalPredicateOnIdentityTriplets_mem
    couretExceptionalLocalPredicateOnIdentityTriplets_true

/--
Dans le cas Couret, le prédicat synthétique implique bien
le prédicat local exceptionnel.
-/
theorem couretExceptionalLocalPredicateOnIdentityTriplets_local :
    isLocalExceptionalCandidate couretTriplet := by
  exact satisfiesExceptionalLocalPredicateOnIdentityTriplets_local
    couretExceptionalLocalPredicateOnIdentityTriplets_true

/--
Validation groupée minimale du cas Couret au niveau du prédicat local
synthétique sur la famille identité.
-/
theorem couretExceptionalLocalPredicateOnIdentityTriplets_valid :
    satisfiesExceptionalLocalPredicateOnIdentityTriplets couretTriplet
      ∧ isExceptionalCandidateOnIdentityTriplets couretTriplet := by
  refine ⟨couretExceptionalLocalPredicateOnIdentityTriplets_true, ?_⟩
  exact
    (satisfiesExceptionalLocalPredicateOnIdentityTriplets_iff
      (T := couretTriplet)).mp
      couretExceptionalLocalPredicateOnIdentityTriplets_true

end

end CouretUnification.Core