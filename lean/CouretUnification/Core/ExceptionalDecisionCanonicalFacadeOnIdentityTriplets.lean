import CouretUnification.Core.ExceptionalDecisionCanonicalClientBridgeOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Façade canonique minimale des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier fournit le point d’entrée public le plus simple pour les futurs
usages aval. Il masque les détails de la chaîne interne et se branche
uniquement sur le bridge canonique côté client déjà stabilisé.
-/

/--
Façade canonique minimale branchée sur le bridge stable côté client.
-/
structure IdentityCenteredExceptionalDecisionCanonicalFacade where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromBridge :
    rows = identityCenteredExceptionalDecisionCanonicalClientBridge.rows

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry T

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T, ∀ hT : T ∈ identityCenteredTriplets,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Façade canonique minimale :
on réutilise directement le bridge canonique côté client déjà stabilisé.
-/
def identityCenteredExceptionalDecisionCanonicalFacade :
    IdentityCenteredExceptionalDecisionCanonicalFacade where
  rows := identityCenteredExceptionalDecisionCanonicalClientBridge.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalClientBridge.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalClientBridge.rows_fst

  rows_fromBridge := rfl

  hasEntry := identityCenteredExceptionalDecisionCanonicalClientBridge.hasEntry
  hasEntry_spec := by
    intro _
    rfl

  resolve := identityCenteredExceptionalDecisionCanonicalClientBridge.resolve
  resolve_spec := by
    intro T hT
    exact identityCenteredExceptionalDecisionCanonicalClientBridge.resolve_spec T hT

/-- La façade canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalFacade_length :
    identityCenteredExceptionalDecisionCanonicalFacade.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalFacade.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalFacade_triplet :
    identityCenteredExceptionalDecisionCanonicalFacade.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalFacade.rows_fst

/-- La façade canonique se réécrit bien vers le bridge canonique côté client. -/
theorem identityCenteredExceptionalDecisionCanonicalFacade_fromBridge :
    identityCenteredExceptionalDecisionCanonicalFacade.rows =
      identityCenteredExceptionalDecisionCanonicalClientBridge.rows := by
  exact identityCenteredExceptionalDecisionCanonicalFacade.rows_fromBridge

/--
Toute ligne transportée par la façade canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalFacade.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalFacade_fromBridge] using hp
  exact identityCenteredExceptionalDecisionCanonicalClientBridge_mem_family hp'

/--
Toute ligne transportée par la façade canonique prend bien
l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalFacade.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalClientBridge.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalFacade_fromBridge] using hp
  exact identityCenteredExceptionalDecisionCanonicalClientBridge_value_cases hp'

/--
Tout triplet de la famille identité admet bien une entrée
dans la façade canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalFacade.hasEntry T := by
  rw [identityCenteredExceptionalDecisionCanonicalFacade.hasEntry_spec]
  exact identityCenteredExceptionalDecisionCanonicalClientBridge_hasEntry_of_mem_family hT

/--
La résolution canonique de la façade recolle bien au triplet demandé.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet = T := by
  exact (identityCenteredExceptionalDecisionCanonicalFacade.resolve_spec T hT).1

/--
L’entrée résolue par la façade appartient bien à ses lignes canoniques.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalFacade.rows := by
  exact (identityCenteredExceptionalDecisionCanonicalFacade.resolve_spec T hT).2

/--
La résolution canonique de la façade conserve bien l’appartenance
à la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  rw [identityCenteredExceptionalDecisionCanonicalFacade_resolve_triplet hT]
  exact hT

/--
La valeur résolue par la façade prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalFacade_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalFacade_value_cases
      (identityCenteredExceptionalDecisionCanonicalFacade_resolve_mem_rows hT)

/--
Entrée résolue canonique du cas Couret dans la façade.
-/
abbrev couretExceptionalDecisionCanonicalFacadeResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalFacade.resolve
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue de la façade porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalFacadeResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalFacadeResolvedEntry.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalDecisionCanonicalFacade_resolve_triplet
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue de la façade appartient bien
à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalFacadeResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalFacadeResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalFacade_resolve_inFamily
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la valeur résolue de la façade prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalFacadeResolvedEntry_cases :
    couretExceptionalDecisionCanonicalFacadeResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalFacadeResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalFacade_resolve_value_cases
      couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale de la façade canonique :
- calibrage de la sortie ;
- raccord au bridge côté client ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalFacadeOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalFacade.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalFacade.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalFacade.rows =
          identityCenteredExceptionalDecisionCanonicalClientBridge.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalFacade.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalFacade.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalFacade.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet ∈
              identityCenteredTriplets)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalFacade.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalFacade.resolve T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalFacadeResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalFacadeResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalFacadeResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalFacadeResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalFacade_length,
    identityCenteredExceptionalDecisionCanonicalFacade_triplet,
    identityCenteredExceptionalDecisionCanonicalFacade_fromBridge,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalFacadeResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalFacadeResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalFacadeResolvedEntry_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalFacade_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalFacade_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalFacade_hasEntry_of_mem_family hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalFacade_resolve_triplet hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalFacade_resolve_inFamily hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalFacade_resolve_mem_rows hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalFacade_resolve_value_cases hT

end

end CouretUnification.Core