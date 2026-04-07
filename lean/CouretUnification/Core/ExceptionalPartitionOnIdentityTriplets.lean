import CouretUnification.Core.ExceptionalClassificationOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Partition documentaire canonique de la famille finie des 21 triplets
centrés sur l’identité, obtenue à partir de la classification globale minimale :

- une partie exceptionnelle ;
- une partie non exceptionnelle ;
- couverture de la famille identité ;
- disjonction documentaire des deux parties.

On n’introduit encore :
- aucun raffinement analytique ;
- aucune structure supplémentaire hors de la famille identité ;
- aucune nouvelle dépendance logique au-delà de la classification canonique.
-/
structure IdentityCenteredExceptionalPartition where
  exceptionalPart : List Triplet
  exceptional_len : exceptionalPart.length ≤ 21
  exceptional_family :
    ∀ T, T ∈ exceptionalPart → T ∈ identityCenteredTriplets

  nonExceptionalPart : List Triplet
  nonExceptional_len : nonExceptionalPart.length ≤ 21
  nonExceptional_family :
    ∀ T, T ∈ nonExceptionalPart → T ∈ identityCenteredTriplets

  cover :
    ∀ T, T ∈ identityCenteredTriplets →
      T ∈ exceptionalPart ∨ T ∈ nonExceptionalPart

  disjoint :
    ∀ T, T ∈ exceptionalPart → T ∉ nonExceptionalPart

/--
Partition canonique minimale :
on reprend simplement les deux composantes de la classification canonique
déjà construite.
-/
def identityCenteredExceptionalPartition :
    IdentityCenteredExceptionalPartition where
  exceptionalPart :=
    identityCenteredExceptionalClassification.exceptionalTriplets
  exceptional_len :=
    identityCenteredExceptionalClassification.exceptional_len
  exceptional_family :=
    identityCenteredExceptionalClassification.exceptional_family

  nonExceptionalPart :=
    identityCenteredExceptionalClassification.nonExceptionalTriplets
  nonExceptional_len :=
    identityCenteredExceptionalClassification.nonExceptional_len
  nonExceptional_family :=
    identityCenteredExceptionalClassification.nonExceptional_family

  cover :=
    identityCenteredExceptionalClassification.cover
  disjoint :=
    identityCenteredExceptionalClassification.disjoint

/--
Dans la partition canonique, la partie exceptionnelle a bien longueur
majorée par `21`.
-/
theorem identityCenteredExceptionalPartition_exceptional_length :
    identityCenteredExceptionalPartition.exceptionalPart.length ≤ 21 := by
  exact identityCenteredExceptionalPartition.exceptional_len

/--
Dans la partition canonique, la partie non exceptionnelle a bien longueur
majorée par `21`.
-/
theorem identityCenteredExceptionalPartition_nonExceptional_length :
    identityCenteredExceptionalPartition.nonExceptionalPart.length ≤ 21 := by
  exact identityCenteredExceptionalPartition.nonExceptional_len

/--
Dans la partition canonique, toute entrée de la partie exceptionnelle
appartient bien à la famille identité.
-/
theorem identityCenteredExceptionalPartition_exceptional_family
    {T : Triplet}
    (hT : T ∈ identityCenteredExceptionalPartition.exceptionalPart) :
    T ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalPartition.exceptional_family T hT

/--
Dans la partition canonique, toute entrée de la partie non exceptionnelle
appartient bien à la famille identité.
-/
theorem identityCenteredExceptionalPartition_nonExceptional_family
    {T : Triplet}
    (hT : T ∈ identityCenteredExceptionalPartition.nonExceptionalPart) :
    T ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalPartition.nonExceptional_family T hT

/--
La partition canonique couvre bien toute la famille identité.
-/
theorem identityCenteredExceptionalPartition_cover
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    T ∈ identityCenteredExceptionalPartition.exceptionalPart
      ∨ T ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
  exact identityCenteredExceptionalPartition.cover T hT

/--
La partition canonique est bien disjointe au sens documentaire minimal :
un triplet exceptionnel ne peut pas appartenir simultanément
à la partie non exceptionnelle.
-/
theorem identityCenteredExceptionalPartition_disjoint
    {T : Triplet}
    (hT : T ∈ identityCenteredExceptionalPartition.exceptionalPart) :
    T ∉ identityCenteredExceptionalPartition.nonExceptionalPart := by
  exact identityCenteredExceptionalPartition.disjoint T hT

/--
Le filtre exceptionnel canonique coïncide bien avec la partie exceptionnelle
de la partition canonique.
-/
theorem identityCenteredExceptionalPartition_exceptional_eq_filter :
    identityCenteredExceptionalPartition.exceptionalPart =
      exceptionalFilterOnIdentityTriplets := by
  rfl

/--
Le complément canonique coïncide bien avec la partie non exceptionnelle
de la partition canonique.
-/
theorem identityCenteredExceptionalPartition_nonExceptional_eq_filter :
    identityCenteredExceptionalPartition.nonExceptionalPart =
      nonExceptionalFilterOnIdentityTriplets := by
  rfl

/--
Cas Couret : le couple documentaire canonique final reste bien
`(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalPartition_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalClassification_pair

/--
Validation groupée minimale de la partition canonique sur la famille identité.
-/
theorem exceptionalPartitionOnIdentityTriplets_valid :
    identityCenteredExceptionalPartition.exceptionalPart.length ≤ 21
      ∧ identityCenteredExceptionalPartition.nonExceptionalPart.length ≤ 21
      ∧ (∀ T, T ∈ identityCenteredExceptionalPartition.exceptionalPart →
            T ∈ identityCenteredTriplets)
      ∧ (∀ T, T ∈ identityCenteredExceptionalPartition.nonExceptionalPart →
            T ∈ identityCenteredTriplets)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            T ∈ identityCenteredExceptionalPartition.exceptionalPart
              ∨ T ∈ identityCenteredExceptionalPartition.nonExceptionalPart)
      ∧ (∀ T, T ∈ identityCenteredExceptionalPartition.exceptionalPart →
            T ∉ identityCenteredExceptionalPartition.nonExceptionalPart)
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalPartition_exceptional_length,
    identityCenteredExceptionalPartition_nonExceptional_length,
    identityCenteredExceptionalPartition.exceptional_family,
    identityCenteredExceptionalPartition.nonExceptional_family,
    identityCenteredExceptionalPartition.cover,
    identityCenteredExceptionalPartition.disjoint,
    couretIdentityCenteredExceptionalPartition_pair
  ⟩

end

end CouretUnification.Core