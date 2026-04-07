import CouretUnification.Core.ExceptionalDecisionCanonicalResolverOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Workflow canonique minimal des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il fournit un point d’entrée unique qui raccorde proprement :

- la couche de requête canonique ;
- le bridge canonique ;
- le résolveur canonique.

Il sert de gabarit réutilisable pour les futurs fichiers métier.
-/

/--
Workflow canonique minimal sur la famille identité.
-/
structure IdentityCenteredExceptionalDecisionCanonicalWorkflow where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromQuery :
    rows = identityCenteredExceptionalDecisionCanonicalQuery.rows

  rows_fromBridge :
    rows = identityCenteredExceptionalDecisionCanonicalBridge.rows

  rows_fromResolver :
    rows = identityCenteredExceptionalDecisionCanonicalResolver.rows

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T, ∀ hT : T ∈ identityCenteredTriplets,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Workflow canonique minimal :
on réutilise directement le bridge canonique, la couche de requête
et le résolveur canonique déjà stabilisés.
-/
def identityCenteredExceptionalDecisionCanonicalWorkflow :
    IdentityCenteredExceptionalDecisionCanonicalWorkflow where
  rows := identityCenteredExceptionalDecisionCanonicalBridge.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalBridge.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalBridge.rows_fst

  rows_fromQuery := identityCenteredExceptionalDecisionCanonicalBridge_fromQuery
  rows_fromBridge := rfl
  rows_fromResolver := rfl

  hasEntry := identityCenteredExceptionalDecisionCanonicalQuery.hasEntry
  hasEntry_spec := by
    intro T
    rfl

  resolve := identityCenteredExceptionalDecisionCanonicalResolver.resolve
  resolve_spec := by
    intro T hT
    exact identityCenteredExceptionalDecisionCanonicalResolver.resolve_spec T hT

/-- Le workflow canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_length :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalWorkflow.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_triplet :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalWorkflow.rows_fst

/-- Le workflow canonique se réécrit bien vers la couche de requête. -/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_fromQuery :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
      identityCenteredExceptionalDecisionCanonicalQuery.rows := by
  exact identityCenteredExceptionalDecisionCanonicalWorkflow.rows_fromQuery

/-- Le workflow canonique se réécrit bien vers le bridge canonique. -/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_fromBridge :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
      identityCenteredExceptionalDecisionCanonicalBridge.rows := by
  exact identityCenteredExceptionalDecisionCanonicalWorkflow.rows_fromBridge

/-- Le workflow canonique se réécrit bien vers le résolveur canonique. -/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_fromResolver :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
      identityCenteredExceptionalDecisionCanonicalResolver.rows := by
  exact identityCenteredExceptionalDecisionCanonicalWorkflow.rows_fromResolver

/--
Toute ligne transportée par le workflow canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalWorkflow_fromBridge] using hp
  exact identityCenteredExceptionalDecisionCanonicalBridge_mem_family hp'

/--
Toute ligne transportée par le workflow canonique prend bien
l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalWorkflow_fromBridge] using hp
  exact identityCenteredExceptionalDecisionCanonicalBridge_value_cases hp'

/--
Tout triplet de la famille identité admet bien une entrée
dans le workflow canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry T := by
  rw [identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry_spec]
  exact identityCenteredExceptionalDecisionCanonicalBridge_hasEntry_of_mem_family hT

/--
La résolution canonique du workflow recolle bien au triplet demandé.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).triplet = T := by
  exact (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve_spec T hT).1

/--
L’entrée résolue par le workflow appartient bien à ses lignes canoniques.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalWorkflow.rows := by
  exact (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve_spec T hT).2

/--
La résolution canonique du workflow conserve bien l’appartenance
à la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  rw [identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_triplet hT]
  exact hT

/--
La valeur résolue par le workflow prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalWorkflow_value_cases
      (identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_mem_rows hT)

/--
Entrée résolue canonique du cas Couret dans le workflow.
-/
abbrev couretExceptionalDecisionCanonicalWorkflowResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalWorkflow.resolve
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du workflow porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalWorkflowResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_triplet
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du workflow appartient bien
à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalWorkflowResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_inFamily
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la valeur résolue du workflow prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalWorkflowResolvedEntry_cases :
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalWorkflowResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_value_cases
      couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale du workflow canonique :
- calibrage de la sortie ;
- raccord à la requête, au bridge et au résolveur ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalWorkflowOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalWorkflow.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalWorkflow.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
          identityCenteredExceptionalDecisionCanonicalQuery.rows
      ∧ identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
          identityCenteredExceptionalDecisionCanonicalBridge.rows
      ∧ identityCenteredExceptionalDecisionCanonicalWorkflow.rows =
          identityCenteredExceptionalDecisionCanonicalResolver.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalWorkflow.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalWorkflow.resolve T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalWorkflowResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalWorkflowResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalWorkflowResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalWorkflowResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalWorkflow_length,
    identityCenteredExceptionalDecisionCanonicalWorkflow_triplet,
    identityCenteredExceptionalDecisionCanonicalWorkflow_fromQuery,
    identityCenteredExceptionalDecisionCanonicalWorkflow_fromBridge,
    identityCenteredExceptionalDecisionCanonicalWorkflow_fromResolver,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalWorkflowResolvedEntry_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_hasEntry_of_mem_family hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_triplet hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_mem_rows hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalWorkflow_resolve_value_cases hT

end

end CouretUnification.Core