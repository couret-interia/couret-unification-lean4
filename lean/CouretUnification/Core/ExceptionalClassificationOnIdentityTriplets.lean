import CouretUnification.Core.ExceptionalFilterOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Complément documentaire du filtre exceptionnel sur la famille des 21 triplets
centrés sur l’identité : on conserve les triplets de la famille qui ne sont
pas retenus par `exceptionalFilterOnIdentityTriplets`.
-/
def nonExceptionalFilterOnIdentityTriplets : List Triplet := by
  classical
  exact identityCenteredTriplets.filter
    (fun T => T ∉ exceptionalFilterOnIdentityTriplets)

/--
Caractérisation du complément documentaire :
un triplet appartient à `nonExceptionalFilterOnIdentityTriplets`
ssi il appartient à la famille identité et n’est pas dans le filtre exceptionnel.
-/
theorem nonExceptionalFilterOnIdentityTriplets_mem_iff
    {T : Triplet} :
    T ∈ nonExceptionalFilterOnIdentityTriplets ↔
      T ∈ identityCenteredTriplets ∧
        T ∉ exceptionalFilterOnIdentityTriplets := by
  classical
  unfold nonExceptionalFilterOnIdentityTriplets
  simp

/--
Tout triplet retenu par le complément documentaire appartient bien
à la famille finie des triplets centrés sur l’identité.
-/
theorem nonExceptionalFilterOnIdentityTriplets_mem_family
    {T : Triplet}
    (hT : T ∈ nonExceptionalFilterOnIdentityTriplets) :
    T ∈ identityCenteredTriplets := by
  exact (nonExceptionalFilterOnIdentityTriplets_mem_iff.mp hT).1

/--
Le complément documentaire a longueur majorée par `21`.
-/
theorem nonExceptionalFilterOnIdentityTriplets_length_le :
    nonExceptionalFilterOnIdentityTriplets.length ≤ 21 := by
  classical
  unfold nonExceptionalFilterOnIdentityTriplets
  calc
    (identityCenteredTriplets.filter
      (fun T => T ∉ exceptionalFilterOnIdentityTriplets)).length
        ≤ identityCenteredTriplets.length := by
          simpa using
            List.length_filter_le
              (fun T : Triplet => T ∉ exceptionalFilterOnIdentityTriplets)
              identityCenteredTriplets
    _ = 21 := by
      exact identityCenteredTriplets_length

/--
Partition documentaire minimale de la famille identité :
tout triplet de `identityCenteredTriplets` est soit exceptionnel,
soit non-exceptionnel.
-/
theorem exceptionalClassificationOnIdentityTriplets_cover
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    T ∈ exceptionalFilterOnIdentityTriplets ∨
      T ∈ nonExceptionalFilterOnIdentityTriplets := by
  classical
  by_cases hE : T ∈ exceptionalFilterOnIdentityTriplets
  · exact Or.inl hE
  · exact Or.inr <|
      (nonExceptionalFilterOnIdentityTriplets_mem_iff).mpr ⟨hT, hE⟩

/--
Disjonction documentaire minimale :
un triplet exceptionnel ne peut pas appartenir simultanément
au complément documentaire.
-/
theorem exceptionalClassificationOnIdentityTriplets_disjoint
    {T : Triplet}
    (hE : T ∈ exceptionalFilterOnIdentityTriplets) :
    T ∉ nonExceptionalFilterOnIdentityTriplets := by
  intro hN
  exact (nonExceptionalFilterOnIdentityTriplets_mem_iff.mp hN).2 hE

/--
Objet canonique de classification globale minimale sur la famille identité.
-/
structure IdentityCenteredExceptionalClassification where
  exceptionalTriplets : List Triplet
  exceptional_len : exceptionalTriplets.length ≤ 21
  exceptional_family :
    ∀ T, T ∈ exceptionalTriplets → T ∈ identityCenteredTriplets

  nonExceptionalTriplets : List Triplet
  nonExceptional_len : nonExceptionalTriplets.length ≤ 21
  nonExceptional_family :
    ∀ T, T ∈ nonExceptionalTriplets → T ∈ identityCenteredTriplets

  cover :
    ∀ T, T ∈ identityCenteredTriplets →
      T ∈ exceptionalTriplets ∨ T ∈ nonExceptionalTriplets

  disjoint :
    ∀ T, T ∈ exceptionalTriplets → T ∉ nonExceptionalTriplets

/--
Classification canonique minimale :
- exceptionnels = `exceptionalFilterOnIdentityTriplets`,
- non-exceptionnels = son complément dans `identityCenteredTriplets`.
-/
def identityCenteredExceptionalClassification :
    IdentityCenteredExceptionalClassification where
  exceptionalTriplets := exceptionalFilterOnIdentityTriplets
  exceptional_len := exceptionalFilterOnIdentityTriplets_length_le
  exceptional_family := by
    intro T hT
    exact exceptionalFilterOnIdentityTriplets_mem_family hT

  nonExceptionalTriplets := nonExceptionalFilterOnIdentityTriplets
  nonExceptional_len := nonExceptionalFilterOnIdentityTriplets_length_le
  nonExceptional_family := by
    intro T hT
    exact nonExceptionalFilterOnIdentityTriplets_mem_family hT

  cover := by
    intro T hT
    exact exceptionalClassificationOnIdentityTriplets_cover hT

  disjoint := by
    intro T hT
    exact exceptionalClassificationOnIdentityTriplets_disjoint hT

/--
Dans la classification canonique, la partie exceptionnelle a bien longueur
majorée par `21`.
-/
theorem identityCenteredExceptionalClassification_exceptional_length :
    identityCenteredExceptionalClassification.exceptionalTriplets.length ≤ 21 := by
  exact identityCenteredExceptionalClassification.exceptional_len

/--
Dans la classification canonique, la partie non-exceptionnelle a bien longueur
majorée par `21`.
-/
theorem identityCenteredExceptionalClassification_nonExceptional_length :
    identityCenteredExceptionalClassification.nonExceptionalTriplets.length ≤ 21 := by
  exact identityCenteredExceptionalClassification.nonExceptional_len

/--
Cas Couret : le couple documentaire canonique final reste bien
`(couretTriplet, true)`.
-/
theorem couretIdentityCenteredExceptionalClassification_pair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
      (couretTriplet, true) := by
  exact couretExceptionalFilterCanonicalPair

/--
Validation groupée minimale de la classification globale sur la famille identité.
-/
theorem exceptionalClassificationOnIdentityTriplets_valid :
    identityCenteredExceptionalClassification.exceptionalTriplets.length ≤ 21
      ∧ identityCenteredExceptionalClassification.nonExceptionalTriplets.length ≤ 21
      ∧ (∀ T, T ∈ identityCenteredExceptionalClassification.exceptionalTriplets →
            T ∈ identityCenteredTriplets)
      ∧ (∀ T, T ∈ identityCenteredExceptionalClassification.nonExceptionalTriplets →
            T ∈ identityCenteredTriplets)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            T ∈ identityCenteredExceptionalClassification.exceptionalTriplets
              ∨ T ∈ identityCenteredExceptionalClassification.nonExceptionalTriplets)
      ∧ (∀ T, T ∈ identityCenteredExceptionalClassification.exceptionalTriplets →
            T ∉ identityCenteredExceptionalClassification.nonExceptionalTriplets)
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
          (couretTriplet, true) := by
  exact ⟨
    identityCenteredExceptionalClassification_exceptional_length,
    identityCenteredExceptionalClassification_nonExceptional_length,
    identityCenteredExceptionalClassification.exceptional_family,
    identityCenteredExceptionalClassification.nonExceptional_family,
    identityCenteredExceptionalClassification.cover,
    identityCenteredExceptionalClassification.disjoint,
    couretIdentityCenteredExceptionalClassification_pair
  ⟩

end

end CouretUnification.Core