import CouretUnification.Core.ExceptionalDecisionCanonicalFactsOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Pont canonique minimal entre :
- l’API canonique stable ;
- la couche de requête canonique ;
- la petite bibliothèque de faits réutilisables.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il fixe seulement un point de raccord propre pour les développements aval.
-/

/--
Pont canonique minimal sur la famille des 21 triplets centrés sur l’identité.
-/
structure IdentityCenteredExceptionalDecisionCanonicalBridge where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromAPI :
    rows = exceptionalDecisionCanonicalRowsOnIdentityTriplets

  rows_fromQuery :
    rows = identityCenteredExceptionalDecisionCanonicalQuery.rows

  mem_family :
    ∀ p, p ∈ rows → p.1 ∈ identityCenteredTriplets

  hasEntry_of_mem_family :
    ∀ T, T ∈ identityCenteredTriplets →
      identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T

/--
Pont canonique minimal :
on raccorde directement la sortie canonique stable à la couche de requête
et aux faits canoniques déjà établis.
-/
def identityCenteredExceptionalDecisionCanonicalBridge :
    IdentityCenteredExceptionalDecisionCanonicalBridge where
  rows := exceptionalDecisionCanonicalRowsOnIdentityTriplets
  rows_len := exceptionalDecisionCanonicalAPI_length
  rows_fst := exceptionalDecisionCanonicalAPI_triplet

  rows_fromAPI := rfl
  rows_fromQuery := rfl

  mem_family := by
    intro p hp
    exact exceptionalDecisionCanonicalAPI_mem_family hp

  hasEntry_of_mem_family := by
    intro T hT
    exact exceptionalDecisionCanonicalFacts_hasEntry_of_mem_family hT

/-- Le pont canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalBridge_length :
    identityCenteredExceptionalDecisionCanonicalBridge.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalBridge_triplet :
    identityCenteredExceptionalDecisionCanonicalBridge.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.rows_fst

/-- Le pont canonique se réécrit bien vers l’API stable. -/
theorem identityCenteredExceptionalDecisionCanonicalBridge_fromAPI :
    identityCenteredExceptionalDecisionCanonicalBridge.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.rows_fromAPI

/-- Le pont canonique se réécrit bien vers la couche de requête. -/
theorem identityCenteredExceptionalDecisionCanonicalBridge_fromQuery :
    identityCenteredExceptionalDecisionCanonicalBridge.rows =
      identityCenteredExceptionalDecisionCanonicalQuery.rows := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.rows_fromQuery

/--
Toute ligne transportée par le pont canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalBridge_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.mem_family p hp

/--
Tout triplet de la famille identité admet bien une entrée
via le pont canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalBridge_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalBridge.hasEntry_of_mem_family T hT

/--
Toute ligne du pont canonique prend bien l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalBridge_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalBridge_fromQuery] using hp
  exact identityCenteredExceptionalDecisionCanonicalQuery_value_cases hp'

/--
Cas Couret : l’entrée canonique stable du pont porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalBridge_triplet :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalFacts_triplet

/--
Cas Couret : l’entrée canonique stable du pont prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalBridge_cases :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalFacts_cases

/--
Cas Couret : le triplet distingué admet bien une entrée
dans la couche de requête raccordée par le pont canonique.
-/
theorem couretExceptionalDecisionCanonicalBridge_hasEntry :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet := by
  exact couretExceptionalDecisionCanonicalFacts_hasEntry

/--
Validation groupée minimale du pont canonique :
- calibrage de la sortie ;
- raccord à l’API et à la requête ;
- faits de famille et d’existence d’entrée ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalBridgeOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalBridge.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalBridge.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalBridge.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalBridge.rows =
          identityCenteredExceptionalDecisionCanonicalQuery.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T)
      ∧ identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet
      ∧ couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalBridge_length,
    identityCenteredExceptionalDecisionCanonicalBridge_triplet,
    identityCenteredExceptionalDecisionCanonicalBridge_fromAPI,
    identityCenteredExceptionalDecisionCanonicalBridge_fromQuery,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalBridge_hasEntry,
    couretExceptionalDecisionCanonicalBridge_triplet,
    couretExceptionalDecisionCanonicalBridge_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalBridge_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalBridge_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalBridge_hasEntry_of_mem_family hT

end

end CouretUnification.Core