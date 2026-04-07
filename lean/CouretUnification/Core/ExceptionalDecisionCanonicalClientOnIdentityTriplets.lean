import CouretUnification.Core.ExceptionalDecisionCanonicalServiceOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Client canonique minimal des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il montre comment un fichier aval consomme uniquement le service canonique stable.
-/

/--
Client canonique minimal branché sur le service stable.
-/
structure IdentityCenteredExceptionalDecisionCanonicalClient where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromService :
    rows = identityCenteredExceptionalDecisionCanonicalService.rows

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      identityCenteredExceptionalDecisionCanonicalService.hasEntry T

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T, ∀ hT : T ∈ identityCenteredTriplets,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Client canonique minimal :
on réutilise directement le service canonique déjà stabilisé.
-/
def identityCenteredExceptionalDecisionCanonicalClient :
    IdentityCenteredExceptionalDecisionCanonicalClient where
  rows := identityCenteredExceptionalDecisionCanonicalService.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalService.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalService.rows_fst

  rows_fromService := rfl

  hasEntry := identityCenteredExceptionalDecisionCanonicalService.hasEntry
  hasEntry_spec := by
    intro T
    rfl

  resolve := identityCenteredExceptionalDecisionCanonicalService.resolve
  resolve_spec := by
    intro T hT
    exact identityCenteredExceptionalDecisionCanonicalService.resolve_spec T hT

/-- Le client canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalClient_length :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalClient.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalClient_triplet :
    identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalClient.rows_fst

/-- Le client canonique se réécrit bien vers le service canonique. -/
theorem identityCenteredExceptionalDecisionCanonicalClient_fromService :
    identityCenteredExceptionalDecisionCanonicalClient.rows =
      identityCenteredExceptionalDecisionCanonicalService.rows := by
  exact identityCenteredExceptionalDecisionCanonicalClient.rows_fromService

/--
Toute ligne transportée par le client canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalService.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalClient_fromService] using hp
  exact identityCenteredExceptionalDecisionCanonicalService_mem_family hp'

/--
Toute ligne transportée par le client canonique prend bien
l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalClient.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalService.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalClient_fromService] using hp
  exact identityCenteredExceptionalDecisionCanonicalService_value_cases hp'

/--
Tout triplet de la famille identité admet bien une entrée
dans le client canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalClient.hasEntry T := by
  change identityCenteredExceptionalDecisionCanonicalService.hasEntry T
  exact identityCenteredExceptionalDecisionCanonicalService_hasEntry_of_mem_family hT

/--
La résolution canonique du client recolle bien au triplet demandé.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet = T := by
  exact (identityCenteredExceptionalDecisionCanonicalClient.resolve_spec T hT).1

/--
L’entrée résolue par le client appartient bien à ses lignes canoniques.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalClient.rows := by
  exact (identityCenteredExceptionalDecisionCanonicalClient.resolve_spec T hT).2

/--
La résolution canonique du client conserve bien l’appartenance
à la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  rw [identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet hT]
  exact hT

/--
La valeur résolue par le client prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalClient_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalClient.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalClient_value_cases
      (identityCenteredExceptionalDecisionCanonicalClient_resolve_mem_rows hT)

/--
Entrée résolue canonique du cas Couret dans le client.
-/
abbrev couretExceptionalDecisionCanonicalClientResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalClient.resolve
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du client porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalClientResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du client appartient bien
à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalClientResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalClientResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalClient_resolve_inFamily
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la valeur résolue du client prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalClientResolvedEntry_cases :
    couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalClientResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalClient_resolve_value_cases
      couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale du client canonique :
- calibrage de la sortie ;
- raccord au service ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalClientOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalClient.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalClient.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalClient.rows =
          identityCenteredExceptionalDecisionCanonicalService.rows
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
    identityCenteredExceptionalDecisionCanonicalClient_length,
    identityCenteredExceptionalDecisionCanonicalClient_triplet,
    identityCenteredExceptionalDecisionCanonicalClient_fromService,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalClientResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalClientResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalClientResolvedEntry_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalClient_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalClient_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClient_hasEntry_of_mem_family hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClient_resolve_triplet hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClient_resolve_mem_rows hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClient_resolve_value_cases hT

end

end CouretUnification.Core