import CouretUnification.Core.ExceptionalDecisionCanonicalResolverOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Exemples canoniques d’usage du résolveur des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne construit aucune nouvelle couche :
il illustre seulement l’usage direct du résolveur canonique.
-/

/-- Exemple direct : la sortie du résolveur a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalResolverExample_length :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalResolver_length

/-- Exemple direct : la projection sur les triplets redonne la famille identité. -/
theorem exceptionalDecisionCanonicalResolverExample_triplet :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalResolver_triplet

/--
Entrée d’exemple obtenue par le résolveur canonique.
-/
def exceptionalDecisionCanonicalResolverExampleEntry
    (T : Triplet)
    (hT : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT

/--
Exemple direct :
le résolveur recolle bien au triplet demandé.
-/
theorem exceptionalDecisionCanonicalResolverExampleEntry_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet = T := by
  change (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet = T
  exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_triplet hT

/--
Exemple direct :
l’entrée résolue appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalResolverExampleEntry_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet ∈
      identityCenteredTriplets := by
  change (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet ∈
      identityCenteredTriplets
  exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_inFamily hT

/--
Exemple direct :
l’entrée résolue appartient bien aux lignes du résolveur canonique.
-/
theorem exceptionalDecisionCanonicalResolverExampleEntry_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet,
      (exceptionalDecisionCanonicalResolverExampleEntry T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalResolver.rows := by
  change ((resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet,
      (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalBridge.rows
  exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_mem_rows hT

/--
Exemple direct :
la valeur résolue prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalResolverExampleEntry_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  change (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value =
        ExceptionalDecisionValue.nonExceptional
  exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_value_cases hT

/--
Exemple combiné :
pour tout triplet de la famille identité, le résolveur fournit une entrée
bien formée, calibrée et appartenant à la sortie stable.
-/
theorem exceptionalDecisionCanonicalResolverExample_bundle
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet = T
      ∧ (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet ∈
          identityCenteredTriplets
      ∧ (((exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet,
            (exceptionalDecisionCanonicalResolverExampleEntry T hT).value) ∈
            identityCenteredExceptionalDecisionCanonicalResolver.rows)
      ∧ ((exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
            ExceptionalDecisionValue.exceptional
          ∨
          (exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalResolverExampleEntry_triplet hT,
    exceptionalDecisionCanonicalResolverExampleEntry_inFamily hT,
    exceptionalDecisionCanonicalResolverExampleEntry_mem_rows hT,
    exceptionalDecisionCanonicalResolverExampleEntry_cases hT
  ⟩

/--
Exemple sur le cas Couret :
l’entrée résolue porte bien sur le triplet distingué.
-/
theorem exceptionalDecisionCanonicalResolverExample_couret_triplet :
    couretExceptionalDecisionCanonicalResolvedEntry.triplet = couretTriplet := by
  exact couretExceptionalDecisionCanonicalResolvedEntry_triplet

/--
Exemple sur le cas Couret :
l’entrée résolue appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalResolverExample_couret_inFamily :
    couretExceptionalDecisionCanonicalResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretExceptionalDecisionCanonicalResolvedEntry_inFamily

/--
Exemple sur le cas Couret :
la valeur résolue prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalResolverExample_couret_cases :
    couretExceptionalDecisionCanonicalResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalResolvedEntry_cases

/--
Exemple combiné sur le cas Couret.
-/
theorem exceptionalDecisionCanonicalResolverExample_couret_bundle :
    couretExceptionalDecisionCanonicalResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalResolverExample_couret_triplet,
    exceptionalDecisionCanonicalResolverExample_couret_inFamily,
    exceptionalDecisionCanonicalResolverExample_couret_cases
  ⟩

/--
Validation groupée minimale des exemples canoniques du résolveur :
- calibrage de la sortie ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalResolverExamplesOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalResolver.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet ∈
              identityCenteredTriplets)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((exceptionalDecisionCanonicalResolverExampleEntry T hT).triplet,
             (exceptionalDecisionCanonicalResolverExampleEntry T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalResolver.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (exceptionalDecisionCanonicalResolverExampleEntry T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    exceptionalDecisionCanonicalResolverExample_length,
    exceptionalDecisionCanonicalResolverExample_triplet,
    ?_,
    ?_,
    ?_,
    ?_,
    exceptionalDecisionCanonicalResolverExample_couret_triplet,
    exceptionalDecisionCanonicalResolverExample_couret_inFamily,
    exceptionalDecisionCanonicalResolverExample_couret_cases
  ⟩
  · intro T hT
    exact exceptionalDecisionCanonicalResolverExampleEntry_triplet hT
  · intro T hT
    exact exceptionalDecisionCanonicalResolverExampleEntry_inFamily hT
  · intro T hT
    exact exceptionalDecisionCanonicalResolverExampleEntry_mem_rows hT
  · intro T hT
    exact exceptionalDecisionCanonicalResolverExampleEntry_cases hT

end

end CouretUnification.Core