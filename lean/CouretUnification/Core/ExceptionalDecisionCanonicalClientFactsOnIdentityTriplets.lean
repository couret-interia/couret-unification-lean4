import CouretUnification.Core.ExceptionalDecisionCanonicalClientOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Petite bibliothèque de faits canoniques réutilisables côté client
pour les décisions exceptionnelles sur la famille finie des 21 triplets
centrés sur l’identité.

Ce fichier ne crée aucune nouvelle couche documentaire.
Il regroupe seulement des faits courts et réutilisables bâtis directement
sur le client canonique stable.
-/

/-- La sortie du client canonique a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalClientFacts_length :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalClient_length

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem exceptionalDecisionCanonicalClientFacts_triplet :
    identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient_triplet

/--
Toute ligne de la sortie du client canonique porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionCanonicalClientFacts_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient_mem_family hp

/--
Toute ligne de la sortie du client canonique prend bien l’une des deux valeurs
documentaires prévues.
-/
theorem exceptionalDecisionCanonicalClientFacts_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  exact identityCenteredExceptionalDecisionCanonicalClient_value_cases hp

/--
Tout triplet de la famille identité admet bien une entrée documentaire
dans le client canonique.
-/
theorem exceptionalDecisionCanonicalClientFacts_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClient.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalClient_hasEntry_of_mem_family hT

/--
La résolution canonique côté client recolle bien au triplet demandé.
-/
theorem exceptionalDecisionCanonicalClientFacts_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet = T := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet hT

/--
L’entrée résolue par le client appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalClientFacts_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_inFamily hT

/--
L’entrée résolue par le client appartient bien aux lignes canoniques.
-/
theorem exceptionalDecisionCanonicalClientFacts_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalClient.rows := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_mem_rows hT

/--
La valeur résolue par le client prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalClientFacts_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact identityCenteredExceptionalDecisionCanonicalClient_resolve_value_cases hT

/--
Fait groupé réutilisable :
pour tout triplet de la famille identité, le client fournit une résolution
bien formée, calibrée et appartenant à la sortie stable.
-/
theorem exceptionalDecisionCanonicalClientFacts_resolve_bundle
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet = T
      ∧ (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet ∈
          identityCenteredTriplets
      ∧ (((identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet,
            (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value) ∈
            identityCenteredExceptionalDecisionCanonicalClient.rows)
      ∧ ((identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
            ExceptionalDecisionValue.exceptional
          ∨
          (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalClientFacts_resolve_triplet hT,
    exceptionalDecisionCanonicalClientFacts_resolve_inFamily hT,
    exceptionalDecisionCanonicalClientFacts_resolve_mem_rows hT,
    exceptionalDecisionCanonicalClientFacts_resolve_value_cases hT
  ⟩

/--
Cas Couret : l’entrée résolue du client porte bien sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalClientFacts_triplet :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_triplet

/--
Cas Couret : l’entrée résolue du client appartient bien à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalClientFacts_inFamily :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_inFamily

/--
Cas Couret : la valeur résolue du client prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalClientFacts_cases :
    couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalClientResolvedEntry_cases

/--
Fait groupé réutilisable sur le cas Couret côté client.
-/
theorem couretExceptionalDecisionCanonicalClientFacts_bundle :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalClientResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    couretExceptionalDecisionCanonicalClientFacts_triplet,
    couretExceptionalDecisionCanonicalClientFacts_inFamily,
    couretExceptionalDecisionCanonicalClientFacts_cases
  ⟩

/--
Validation groupée minimale de la bibliothèque de faits canoniques côté client :
- calibrage de la sortie ;
- faits de famille et de résolution ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalClientFactsOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalClient.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet ∈
              identityCenteredTriplets)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalClient.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
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
    exceptionalDecisionCanonicalClientFacts_length,
    exceptionalDecisionCanonicalClientFacts_triplet,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalClientFacts_triplet,
    couretExceptionalDecisionCanonicalClientFacts_inFamily,
    couretExceptionalDecisionCanonicalClientFacts_cases
  ⟩
  · intro p hp
    exact exceptionalDecisionCanonicalClientFacts_mem_family hp
  · intro p hp
    exact exceptionalDecisionCanonicalClientFacts_value_cases hp
  · intro T hT
    exact exceptionalDecisionCanonicalClientFacts_hasEntry_of_mem_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientFacts_resolve_triplet hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientFacts_resolve_inFamily hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientFacts_resolve_mem_rows hT
  · intro T hT
    exact exceptionalDecisionCanonicalClientFacts_resolve_value_cases hT

end

end CouretUnification.Core