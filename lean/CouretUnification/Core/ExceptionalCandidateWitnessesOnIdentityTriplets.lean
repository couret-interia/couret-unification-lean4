import CouretUnification.Core.ExceptionalCandidatesOnIdentityTriplets
import CouretUnification.Core.TripletExceptionalWitness
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Témoin explicite, sur la famille finie des 21 triplets centrés sur l’identité :

- un candidat exceptionnel déjà transporté sur la famille identité ;
- un témoin local explicite de candidature exceptionnelle pour ce triplet.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalWitness where
  candidate : IdentityCenteredExceptionalCandidate
  witness : TripletExceptionalWitness candidate.triplet

/--
Constructeur canonique :
à partir d’un candidat exceptionnel déjà empaqueté sur la famille identité,
on lui adjoint le témoin local explicite canonique.
-/
def canonicalIdentityCenteredExceptionalWitness
    (C : IdentityCenteredExceptionalCandidate) :
    IdentityCenteredExceptionalWitness where
  candidate := C
  witness := canonicalTripletExceptionalWitness C.triplet C.localExceptional

/--
Le témoin empaqueté reste bien dans la famille finie
des triplets centrés sur l’identité.
-/
theorem IdentityCenteredExceptionalWitness.inFamily
    (W : IdentityCenteredExceptionalWitness) :
    W.candidate.triplet ∈ identityCenteredTriplets := by
  exact W.candidate.inFamily

/--
Le témoin empaqueté conserve bien le prédicat local exceptionnel.
-/
theorem IdentityCenteredExceptionalWitness.localExceptional
    (W : IdentityCenteredExceptionalWitness) :
    isLocalExceptionalCandidate W.candidate.triplet := by
  exact W.candidate.localExceptional

/--
Le témoin empaqueté induit bien le prédicat transporté
sur la famille identité.
-/
theorem IdentityCenteredExceptionalWitness.toPredicate
    (W : IdentityCenteredExceptionalWitness) :
    isExceptionalCandidateOnIdentityTriplets W.candidate.triplet := by
  exact W.candidate.toPredicate

/--
Le témoin local explicite empaqueté vérifie bien
le prédicat local de candidature exceptionnelle.
-/
theorem IdentityCenteredExceptionalWitness.witnessPredicate
    (W : IdentityCenteredExceptionalWitness) :
    isLocalExceptionalCandidate W.candidate.triplet := by
  exact W.witness.predicate

/--
Le témoin local explicite empaqueté fournit bien
un candidat local explicite.
-/
def IdentityCenteredExceptionalWitness.localCandidate
    (W : IdentityCenteredExceptionalWitness) :
    TripletLocalExceptionalCandidate W.candidate.triplet :=
  W.witness.localCandidate

/--
Introduction canonique :
tout candidat exceptionnel déjà transporté sur la famille identité
fournit un témoin explicite sur cette famille.
-/
theorem IdentityCenteredExceptionalCandidate.hasCanonicalWitness
    (C : IdentityCenteredExceptionalCandidate) :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = C.triplet := by
  refine ⟨canonicalIdentityCenteredExceptionalWitness C, rfl⟩

/--
Élimination minimale :
le prédicat transporté sur la famille identité fournit bien
un témoin explicite empaqueté.
-/
theorem isExceptionalCandidateOnIdentityTriplets_hasExplicitWitness
    {T : Triplet}
    (h : isExceptionalCandidateOnIdentityTriplets T) :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = T := by
  rcases isExceptionalCandidateOnIdentityTriplets_hasWitness h with ⟨C, rfl⟩
  exact ⟨canonicalIdentityCenteredExceptionalWitness C, rfl⟩

/--
Cas Couret : témoin explicite canonique sur la famille identité.
-/
def couretIdentityCenteredExceptionalWitness :
    IdentityCenteredExceptionalWitness :=
  canonicalIdentityCenteredExceptionalWitness
    couretIdentityCenteredExceptionalCandidate

/--
Dans le cas Couret, le témoin explicite canonique reste bien
dans la famille identité.
-/
theorem couretIdentityCenteredExceptionalWitness_inFamily :
    couretIdentityCenteredExceptionalWitness.candidate.triplet ∈ identityCenteredTriplets := by
  exact couretIdentityCenteredExceptionalWitness.inFamily

/--
Dans le cas Couret, le témoin explicite canonique satisfait bien
le prédicat local exceptionnel.
-/
theorem couretIdentityCenteredExceptionalWitness_localExceptional :
    isLocalExceptionalCandidate
      couretIdentityCenteredExceptionalWitness.candidate.triplet := by
  exact couretIdentityCenteredExceptionalWitness.localExceptional

/--
Dans le cas Couret, le témoin explicite canonique induit bien
le prédicat transporté sur la famille identité.
-/
theorem couretIdentityCenteredExceptionalWitness_predicate :
    isExceptionalCandidateOnIdentityTriplets couretTriplet := by
  simpa using couretIdentityCenteredExceptionalWitness.toPredicate

/--
Validation groupée minimale du cas Couret au niveau des témoins explicites
sur la famille identité.
-/
theorem couretIdentityCenteredExceptionalWitness_valid :
    isExceptionalCandidateOnIdentityTriplets couretTriplet
      ∧ couretIdentityCenteredExceptionalWitness.candidate.triplet = couretTriplet := by
  exact ⟨
    couretIdentityCenteredExceptionalWitness_predicate,
    rfl
  ⟩

end

end CouretUnification.Core