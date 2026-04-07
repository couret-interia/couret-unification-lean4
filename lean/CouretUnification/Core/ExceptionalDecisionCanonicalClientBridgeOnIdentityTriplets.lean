import CouretUnification.Core.ExceptionalDecisionCanonicalClientExamplesOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionCanonicalClientFactsOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Pont canonique minimal côté client pour les décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il relie proprement :
- le client canonique stable ;
- les exemples canoniques côté client ;
- les faits canoniques côté client.

Il sert de point de raccord unique pour les futurs fichiers aval.
-/

/--
Pont canonique minimal côté client.
-/
structure IdentityCenteredExceptionalDecisionCanonicalClientBridge where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromClient :
    rows = identityCenteredExceptionalDecisionCanonicalClient.rows

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      identityCenteredExceptionalDecisionCanonicalClient.hasEntry T

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T, ∀ hT : T ∈ identityCenteredTriplets,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Pont canonique minimal côté client :
on réutilise directement le client canonique déjà stabilisé.
-/
def identityCenteredExceptionalDecisionCanonicalClientBridge :
    IdentityCenteredExceptionalDecisionCanonicalClientBridge where
  rows := identityCenteredExceptionalDecisionCanonicalClient.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalClient.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalClient.rows_fst

  rows_fromClient := rfl

  hasEntry := identityCenteredExceptionalDecisionCanonicalClient.hasEntry
  hasEntry_spec := by
    intro _
    rfl

  resolve := identityCenteredExceptionalDecisionCanonicalClient.resolve
  resolve_spec := by
    intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClient.resolve_spec T hT

/-- Le pont canonique côté client a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_length :
    identityCenteredExceptionalDecisionCanonicalClientBridge.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalClientBridge.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_triplet :
    identityCenteredExceptionalDecisionCanonicalClientBridge.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClientBridge.rows_fst

/-- Le pont canonique côté client se réécrit bien vers le client stable. -/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_fromClient :
    identityCenteredExceptionalDecisionCanonicalClientBridge.rows =
      identityCenteredExceptionalDecisionCanonicalClient.rows := by
  exact identityCenteredExceptionalDecisionCanonicalClientBridge.rows_fromClient

/--
Toute ligne transportée par le pont canonique côté client porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalClientBridge_fromClient] using hp
  exact exceptionalDecisionCanonicalClientFacts_mem_family hp'

/--
Toute ligne transportée par le pont canonique côté client prend bien
l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalClientBridge_fromClient] using hp
  exact exceptionalDecisionCanonicalClientFacts_value_cases hp'

/--
Tout triplet de la famille identité admet bien une entrée
dans le pont canonique côté client.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry T := by
  rw [identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry_spec]
  exact exceptionalDecisionCanonicalClientFacts_hasEntry_of_mem_family hT

/--
La résolution canonique côté client recolle bien au triplet demandé.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet = T := by
  exact (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve_spec T hT).1

/--
L’entrée résolue par le pont côté client appartient bien à ses lignes canoniques.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalClientBridge.rows := by
  exact (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve_spec T hT).2

/--
La résolution canonique côté client conserve bien l’appartenance
à la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  rw [identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_triplet hT]
  exact hT

/--
La valeur résolue par le pont côté client prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalClientBridge_value_cases
      (identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_mem_rows hT)

/--
Fait groupé réutilisable :
pour tout triplet de la famille identité, le pont côté client fournit une
résolution bien formée, calibrée et appartenant à la sortie stable.
-/
theorem identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_bundle
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry T
      ∧ (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet = T
      ∧ (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet ∈
          identityCenteredTriplets
      ∧ (((identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet,
            (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value) ∈
            identityCenteredExceptionalDecisionCanonicalClientBridge.rows)
      ∧ ((identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
            ExceptionalDecisionValue.exceptional
          ∨
          (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
            ExceptionalDecisionValue.nonExceptional) := by
  have hBundle :=
    exceptionalDecisionCanonicalClientExample_bundle hT
  simpa [identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry_spec,
    identityCenteredExceptionalDecisionCanonicalClientBridge_fromClient] using hBundle

/--
Entrée résolue canonique du cas Couret dans le pont côté client.
-/
abbrev couretExceptionalDecisionCanonicalClientBridgeResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalClientBridge.resolve
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du pont côté client porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet = couretTriplet := by
  exact couretExceptionalDecisionCanonicalClientFacts_triplet

/--
Dans le cas Couret, l’entrée résolue du pont côté client appartient bien
à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretExceptionalDecisionCanonicalClientFacts_inFamily

/--
Dans le cas Couret, la valeur résolue du pont côté client prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_cases :
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalClientFacts_cases

/--
Fait groupé réutilisable sur le cas Couret côté client.
-/
theorem couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_bundle :
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  exact couretExceptionalDecisionCanonicalClientFacts_bundle

/--
Validation groupée minimale du pont canonique côté client :
- calibrage de la sortie ;
- raccord au client ;
- faits de famille et de résolution ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalClientBridgeOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalClientBridge.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalClientBridge.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalClientBridge.rows =
          identityCenteredExceptionalDecisionCanonicalClient.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet ∈
              identityCenteredTriplets)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalClientBridge.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalClientBridge.resolve T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalClientBridgeResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalClientBridge_length,
    identityCenteredExceptionalDecisionCanonicalClientBridge_triplet,
    identityCenteredExceptionalDecisionCanonicalClientBridge_fromClient,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalClientBridgeResolvedEntry_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_hasEntry_of_mem_family hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_triplet hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_inFamily hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_mem_rows hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge_resolve_value_cases hT

end

end CouretUnification.Core