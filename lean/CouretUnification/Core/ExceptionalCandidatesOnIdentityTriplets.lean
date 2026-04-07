import CouretUnification.Core.ExceptionalTriplets
import CouretUnification.Core.TripletExceptionalPredicate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Prédicat transporté sur la famille finie des 21 triplets centrés sur l’identité :

un triplet est ici vu comme "candidat exceptionnel sur la famille identité"
s’il appartient à `identityCenteredTriplets` et satisfait déjà
le prédicat local `isLocalExceptionalCandidate`.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision globale,
- aucune classification finale.
-/
def isExceptionalCandidateOnIdentityTriplets (T : Triplet) : Prop :=
  T ∈ identityCenteredTriplets ∧ isLocalExceptionalCandidate T

/--
Table documentaire purement locale :
à chaque triplet centré sur l’identité, on associe le prédicat local déjà défini.

C’est un transport de prédicat sur une famille finie,
pas une extraction filtrée.
-/
def identityCenteredExceptionalTable : List (Triplet × Prop) :=
  identityCenteredTriplets.map (fun T => (T, isLocalExceptionalCandidate T))

/-- La table transportée a bien longueur 21. -/
theorem identityCenteredExceptionalTable_length :
    identityCenteredExceptionalTable.length = 21 := by
  simp [identityCenteredExceptionalTable, identityCenteredTriplets_length]

/-- La projection sur la première composante redonne bien la famille finie source. -/
theorem identityCenteredExceptionalTable_fst :
    identityCenteredExceptionalTable.map Prod.fst = identityCenteredTriplets := by
  unfold identityCenteredExceptionalTable
  rw [List.map_map]
  have hfun :
      (Prod.fst ∘ fun T => (T, isLocalExceptionalCandidate T)) = fun T => T := by
    funext T
    rfl
  rw [hfun]
  simp

/-- Dépliage exact du prédicat transporté. -/
theorem isExceptionalCandidateOnIdentityTriplets_iff
    {T : Triplet} :
    isExceptionalCandidateOnIdentityTriplets T ↔
      T ∈ identityCenteredTriplets ∧ isLocalExceptionalCandidate T := by
  rfl

/-- Introduction minimale du prédicat transporté. -/
theorem isExceptionalCandidateOnIdentityTriplets_intro
    {T : Triplet}
    (hmem : T ∈ identityCenteredTriplets)
    (hloc : isLocalExceptionalCandidate T) :
    isExceptionalCandidateOnIdentityTriplets T := by
  exact ⟨hmem, hloc⟩

/-- Élimination minimale : appartenance à la famille finie. -/
theorem isExceptionalCandidateOnIdentityTriplets_mem
    {T : Triplet}
    (h : isExceptionalCandidateOnIdentityTriplets T) :
    T ∈ identityCenteredTriplets := by
  exact h.1

/-- Élimination minimale : satisfaction du prédicat local exceptionnel. -/
theorem isExceptionalCandidateOnIdentityTriplets_local
    {T : Triplet}
    (h : isExceptionalCandidateOnIdentityTriplets T) :
    isLocalExceptionalCandidate T := by
  exact h.2

/--
Témoin empaqueté, purement local, d’un candidat exceptionnel
à l’intérieur de la famille finie centrée sur l’identité.
-/
structure IdentityCenteredExceptionalCandidate where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  localExceptional : isLocalExceptionalCandidate triplet

/-- Tout témoin empaqueté induit le prédicat transporté correspondant. -/
theorem IdentityCenteredExceptionalCandidate.toPredicate
    (W : IdentityCenteredExceptionalCandidate) :
    isExceptionalCandidateOnIdentityTriplets W.triplet := by
  exact ⟨W.inFamily, W.localExceptional⟩

/--
Version existentielle minimale :
le prédicat transporté fournit bien un témoin empaqueté
sur la famille centrée sur l’identité.
-/
theorem isExceptionalCandidateOnIdentityTriplets_hasWitness
    {T : Triplet}
    (h : isExceptionalCandidateOnIdentityTriplets T) :
    ∃ W : IdentityCenteredExceptionalCandidate, W.triplet = T := by
  refine ⟨
    { triplet := T
    , inFamily := h.1
    , localExceptional := h.2 },
    rfl
  ⟩

/--
Cas Couret : le triplet distingué appartient bien à la famille des 21 triplets
centrés sur l’identité.
-/
theorem couretTriplet_mem_identityCenteredTriplets :
    couretTriplet ∈ identityCenteredTriplets := by
  native_decide

/--
Cas Couret : le triplet distingué satisfait bien le prédicat transporté
sur la famille centrée sur l’identité.
-/
theorem couretTriplet_isExceptionalCandidateOnIdentityTriplets :
    isExceptionalCandidateOnIdentityTriplets couretTriplet := by
  exact ⟨
    couretTriplet_mem_identityCenteredTriplets,
    couretTriplet_isLocalExceptionalCandidate
  ⟩

/-- Témoin empaqueté canonique du cas Couret sur la famille identité. -/
def couretIdentityCenteredExceptionalCandidate :
    IdentityCenteredExceptionalCandidate where
  triplet := couretTriplet
  inFamily := couretTriplet_mem_identityCenteredTriplets
  localExceptional := couretTriplet_isLocalExceptionalCandidate

/--
Validation groupée minimale du cas Couret au niveau du transport sur la famille
centrée sur l’identité.
-/
theorem couretIdentityCenteredExceptionalCandidate_valid :
    isExceptionalCandidateOnIdentityTriplets couretTriplet
      ∧ couretIdentityCenteredExceptionalCandidate.triplet = couretTriplet := by
  exact ⟨
    couretTriplet_isExceptionalCandidateOnIdentityTriplets,
    rfl
  ⟩

end

end CouretUnification.Core