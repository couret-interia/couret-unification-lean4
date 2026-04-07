import CouretUnification.Core.ExceptionalPartitionOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Valeur canonique de décision documentaire sur la famille identité :
un triplet est déclaré soit exceptionnel, soit non exceptionnel.
-/
inductive ExceptionalDecisionValue where
  | exceptional
  | nonExceptional
deriving DecidableEq, Repr

/--
Décision canonique minimale sur un triplet :
on lit simplement son appartenance à la partie exceptionnelle
de la partition canonique.
-/
def decideExceptionalOnIdentityTriplets
    (T : Triplet) : ExceptionalDecisionValue := by
  classical
  exact
    if T ∈ identityCenteredExceptionalPartition.exceptionalPart then
      ExceptionalDecisionValue.exceptional
    else
      ExceptionalDecisionValue.nonExceptional

/--
Caractérisation de la décision canonique : valeur `exceptional`
ssi le triplet appartient à la partie exceptionnelle de la partition.
-/
theorem decideExceptionalOnIdentityTriplets_eq_exceptional_iff
    {T : Triplet} :
    decideExceptionalOnIdentityTriplets T =
        ExceptionalDecisionValue.exceptional ↔
      T ∈ identityCenteredExceptionalPartition.exceptionalPart := by
  classical
  by_cases hT : T ∈ identityCenteredExceptionalPartition.exceptionalPart
  · simp [decideExceptionalOnIdentityTriplets, hT]
  · simp [decideExceptionalOnIdentityTriplets, hT]

/--
Caractérisation de la décision canonique, sur la famille identité :
valeur `nonExceptional` ssi le triplet appartient à la partie
non exceptionnelle de la partition.
-/
theorem decideExceptionalOnIdentityTriplets_eq_nonExceptional_iff
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    decideExceptionalOnIdentityTriplets T =
        ExceptionalDecisionValue.nonExceptional ↔
      T ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
  classical
  by_cases hE : T ∈ identityCenteredExceptionalPartition.exceptionalPart
  · have hN :
      T ∉ identityCenteredExceptionalPartition.nonExceptionalPart := by
      exact identityCenteredExceptionalPartition_disjoint hE
    simp [decideExceptionalOnIdentityTriplets, hE, hN]
  · have hN :
      T ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
      exact (identityCenteredExceptionalPartition_cover hT).resolve_left hE
    simp [decideExceptionalOnIdentityTriplets, hE, hN]

/--
La décision canonique prend toujours l’une des deux valeurs prévues.
-/
theorem decideExceptionalOnIdentityTriplets_cases
    (T : Triplet) :
    decideExceptionalOnIdentityTriplets T =
        ExceptionalDecisionValue.exceptional
      ∨
      decideExceptionalOnIdentityTriplets T =
        ExceptionalDecisionValue.nonExceptional := by
  classical
  by_cases hT : T ∈ identityCenteredExceptionalPartition.exceptionalPart
  · left
    simp [decideExceptionalOnIdentityTriplets, hT]
  · right
    simp [decideExceptionalOnIdentityTriplets, hT]

/--
Objet canonique de décision documentaire ponctuelle
sur la famille identité.
-/
structure IdentityCenteredExceptionalDecision where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  value : ExceptionalDecisionValue
  exceptional_spec :
    value = ExceptionalDecisionValue.exceptional →
      triplet ∈ identityCenteredExceptionalPartition.exceptionalPart
  nonExceptional_spec :
    value = ExceptionalDecisionValue.nonExceptional →
      triplet ∈ identityCenteredExceptionalPartition.nonExceptionalPart

/--
Constructeur canonique :
à partir d’un triplet déjà situé dans la famille identité,
on en extrait la décision documentaire minimale correspondante.
-/
def canonicalIdentityCenteredExceptionalDecision
    (T : Triplet)
    (hT : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalDecision where
  triplet := T
  inFamily := hT
  value := decideExceptionalOnIdentityTriplets T
  exceptional_spec := by
    intro h
    exact (decideExceptionalOnIdentityTriplets_eq_exceptional_iff).mp h
  nonExceptional_spec := by
    intro h
    exact (decideExceptionalOnIdentityTriplets_eq_nonExceptional_iff hT).mp h

/--
Toute décision canonique ponctuelle recolle bien avec la partition :
le triplet appartient à l’une des deux parties.
-/
theorem IdentityCenteredExceptionalDecision.mem_partition
    (D : IdentityCenteredExceptionalDecision) :
    D.triplet ∈ identityCenteredExceptionalPartition.exceptionalPart
      ∨
      D.triplet ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
  cases hD : D.value with
  | exceptional =>
      left
      exact D.exceptional_spec hD
  | nonExceptional =>
      right
      exact D.nonExceptional_spec hD

/--
Cas Couret : décision canonique ponctuelle sur la famille identité.
-/
def couretIdentityCenteredExceptionalDecision :
    IdentityCenteredExceptionalDecision :=
  canonicalIdentityCenteredExceptionalDecision
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la décision canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecision_triplet :
    couretIdentityCenteredExceptionalDecision.triplet = couretTriplet := by
  rfl

/--
Dans le cas Couret, la décision canonique est bien prise
sur la famille identité.
-/
theorem couretIdentityCenteredExceptionalDecision_inFamily :
    couretIdentityCenteredExceptionalDecision.triplet ∈ identityCenteredTriplets := by
  exact couretIdentityCenteredExceptionalDecision.inFamily

/--
Dans le cas Couret, la décision canonique prend bien l’une des deux valeurs.
-/
theorem couretIdentityCenteredExceptionalDecision_cases :
    couretIdentityCenteredExceptionalDecision.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecision.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact decideExceptionalOnIdentityTriplets_cases couretTriplet

/--
Validation groupée minimale de la couche de décision canonique
sur la famille identité.
-/
theorem exceptionalDecisionOnIdentityTriplets_valid :
    (∀ T,
        decideExceptionalOnIdentityTriplets T =
            ExceptionalDecisionValue.exceptional
          ∨
          decideExceptionalOnIdentityTriplets T =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T,
            decideExceptionalOnIdentityTriplets T =
              ExceptionalDecisionValue.exceptional →
              T ∈ identityCenteredExceptionalPartition.exceptionalPart)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            decideExceptionalOnIdentityTriplets T =
              ExceptionalDecisionValue.nonExceptional →
              T ∈ identityCenteredExceptionalPartition.nonExceptionalPart)
      ∧ couretIdentityCenteredExceptionalDecision.triplet = couretTriplet
      ∧ couretIdentityCenteredExceptionalDecision.triplet ∈ identityCenteredTriplets := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T
    exact decideExceptionalOnIdentityTriplets_cases T
  · intro T hT
    exact (decideExceptionalOnIdentityTriplets_eq_exceptional_iff).mp hT
  · intro T hmem hT
    exact (decideExceptionalOnIdentityTriplets_eq_nonExceptional_iff hmem).mp hT
  · exact couretIdentityCenteredExceptionalDecision_triplet
  · exact couretIdentityCenteredExceptionalDecision_inFamily

end

end CouretUnification.Core