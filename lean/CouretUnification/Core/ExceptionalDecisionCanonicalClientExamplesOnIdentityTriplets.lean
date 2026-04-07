import CouretUnification.Core.ExceptionalDecisionCanonicalClientOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Exemples canoniques d’usage du client des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne construit aucune nouvelle couche :
il illustre seulement l’usage direct du client canonique.
-/

/-- Exemple direct : la sortie du client a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalClientExample_length :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalClient_length

/-- Exemple direct : la projection sur les triplets redonne la famille identité. -/
theorem exceptionalDecisionCanonicalClientExample_triplet :
    identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient_triplet

/--
Entrée d’exemple obtenue par le client canonique.
-/
def exceptionalDecisionCanonicalClientExampleEntry
    (T : Triplet)
    (hT : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalClient.resolve T hT

/--
Exemple direct :
le client recolle bien au triplet demandé.
-/
theorem exceptionalDecisionCanonicalClientExampleEntry_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet = T := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet hT

/--
Exemple direct :
l’entrée résolue appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalClientExampleEntry_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet ∈
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_inFamily hT

/--
Exemple direct :
l’entrée résolue appartient bien aux lignes du client canonique.
-/
theorem exceptionalDecisionCanonicalClientExampleEntry_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((exceptionalDecisionCanonicalClientExampleEntry T hT).triplet,
      (exceptionalDecisionCanonicalClientExampleEntry T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalClient.rows := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_mem_rows hT

/--
Exemple direct :
la valeur résolue prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalClientExampleEntry_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (exceptionalDecisionCanonicalClientExampleEntry T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (exceptionalDecisionCanonicalClientExampleEntry T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_value_cases hT

/--
Exemple direct :
tout triplet de la famille identité admet bien une entrée dans le client canonique.
-/
theorem exceptionalDecisionCanonicalClientExample_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClient.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalClient_hasEntry_of_mem_family hT

/--
Exemple combiné :
pour tout triplet de la famille identité, le client fournit une entrée
bien formée, calibrée et appartenant à la sortie stable.
-/
theorem exceptionalDecisionCanonicalClientExample_bundle
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClient.hasEntry T
      ∧ (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet = T
      ∧ (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet ∈
          identityCenteredTriplets
      ∧ (((exceptionalDecisionCanonicalClientExampleEntry T hT).triplet,
            (exceptionalDecisionCanonicalClientExampleEntry T hT).value) ∈
            identityCenteredExceptionalDecisionCanonicalClient.rows)
      ∧ ((exceptionalDecisionCanonicalClientExampleEntry T hT).value =
            ExceptionalDecisionValue.exceptional
          ∨
          (exceptionalDecisionCanonicalClientExampleEntry T hT).value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalClientExample_hasEntry_of_mem_family hT,
    exceptionalDecisionCanonicalClientExampleEntry_triplet hT,
    exceptionalDecisionCanonicalClientExampleEntry_inFamily hT,
    exceptionalDecisionCanonicalClientExampleEntry_mem_rows hT,
    exceptionalDecisionCanonicalClientExampleEntry_cases hT
  ⟩

/--
Exemple sur le cas Couret :
l’entrée résolue porte bien sur le triplet distingué.
-/
theorem exceptionalDecisionCanonicalClientExample_couret_triplet :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_triplet

/--
Exemple sur le cas Couret :
l’entrée résolue appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalClientExample_couret_inFamily :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_inFamily

/--
Exemple sur le cas Couret :
la valeur résolue prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalClientExample_couret_cases :
    couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_cases

/--
Exemple combiné sur le cas Couret.
-/
theorem exceptionalDecisionCanonicalClientExample_couret_bundle :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalClientExample_couret_triplet,
    exceptionalDecisionCanonicalClientExample_couret_inFamily,
    exceptionalDecisionCanonicalClientExample_couret_cases
  ⟩

/--
Validation groupée minimale des exemples canoniques du client :
- calibrage de la sortie ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalClientExamplesOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalClient.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalClientExampleEntry T hT).triplet ∈
              identityCenteredTriplets)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((exceptionalDecisionCanonicalClientExampleEntry T hT).triplet,
             (exceptionalDecisionCanonicalClientExampleEntry T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalClient.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (exceptionalDecisionCanonicalClientExampleEntry T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (exceptionalDecisionCanonicalClientExampleEntry T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    exceptionalDecisionCanonicalClientExample_length,
    exceptionalDecisionCanonicalClientExample_triplet,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    exceptionalDecisionCanonicalClientExample_couret_triplet,
    exceptionalDecisionCanonicalClientExample_couret_inFamily,
    exceptionalDecisionCanonicalClientExample_couret_cases
  ⟩
  · intro T hT
    exact exceptionalDecisionCanonicalClientExample_hasEntry_of_mem_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientExampleEntry_triplet hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientExampleEntry_inFamily hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientExampleEntry_mem_rows hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientExampleEntry_cases hT

end

end CouretUnification.Core