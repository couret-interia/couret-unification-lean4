import CouretUnification.Core.ExceptionalDecisionCanonicalWorkflowOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Service canonique minimal des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il expose simplement une petite interface de service au-dessus du workflow
canonique déjà stabilisé.
-/

/--
Service canonique minimal branché sur le workflow stable.
-/
structure IdentityCenteredExceptionalDecisionCanonicalService where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  rows_fromWorkflow :
    rows = identityCenteredExceptionalDecisionCanonicalWorkflow.rows

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry T

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T, ∀ hT : T ∈ identityCenteredTriplets,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Service canonique minimal :
on réutilise directement le workflow canonique déjà stabilisé.
-/
def identityCenteredExceptionalDecisionCanonicalService :
    IdentityCenteredExceptionalDecisionCanonicalService where
  rows := identityCenteredExceptionalDecisionCanonicalWorkflow.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalWorkflow.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalWorkflow.rows_fst

  rows_fromWorkflow := rfl

  hasEntry := identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry
  hasEntry_spec := by
    intro T
    rfl

  resolve := identityCenteredExceptionalDecisionCanonicalWorkflow.resolve
  resolve_spec := by
    intro T hT
    exact identityCenteredExceptionalDecisionCanonicalWorkflow.resolve_spec T hT

/-- Le service canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalService_length :
    identityCenteredExceptionalDecisionCanonicalService.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalService.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalService_triplet :
    identityCenteredExceptionalDecisionCanonicalService.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalService.rows_fst

/-- Le service canonique se réécrit bien vers le workflow canonique. -/
theorem identityCenteredExceptionalDecisionCanonicalService_fromWorkflow :
    identityCenteredExceptionalDecisionCanonicalService.rows =
      identityCenteredExceptionalDecisionCanonicalWorkflow.rows := by
  exact identityCenteredExceptionalDecisionCanonicalService.rows_fromWorkflow

/--
Toute ligne transportée par le service canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalService.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalService_fromWorkflow] using hp
  exact identityCenteredExceptionalDecisionCanonicalWorkflow_mem_family hp'

/--
Toute ligne transportée par le service canonique prend bien
l’une des deux valeurs documentaires prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalService.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  have hp' : p ∈ identityCenteredExceptionalDecisionCanonicalWorkflow.rows := by
    simpa [identityCenteredExceptionalDecisionCanonicalService_fromWorkflow] using hp
  exact identityCenteredExceptionalDecisionCanonicalWorkflow_value_cases hp'

/--
Tout triplet de la famille identité admet bien une entrée
dans le service canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalService.hasEntry T := by
  change identityCenteredExceptionalDecisionCanonicalWorkflow.hasEntry T
  exact identityCenteredExceptionalDecisionCanonicalWorkflow_hasEntry_of_mem_family hT

/--
La résolution canonique du service recolle bien au triplet demandé.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_resolve_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).triplet = T := by
  exact (identityCenteredExceptionalDecisionCanonicalService.resolve_spec T hT).1

/--
L’entrée résolue par le service appartient bien à ses lignes canoniques.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_resolve_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((identityCenteredExceptionalDecisionCanonicalService.resolve T hT).triplet,
      (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalService.rows := by
  exact (identityCenteredExceptionalDecisionCanonicalService.resolve_spec T hT).2

/--
La résolution canonique du service conserve bien l’appartenance
à la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_resolve_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).triplet ∈
      identityCenteredTriplets := by
  rw [identityCenteredExceptionalDecisionCanonicalService_resolve_triplet hT]
  exact hT

/--
La valeur résolue par le service prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalService_resolve_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalService_value_cases
      (identityCenteredExceptionalDecisionCanonicalService_resolve_mem_rows hT)

/--
Entrée résolue canonique du cas Couret dans le service.
-/
abbrev couretExceptionalDecisionCanonicalServiceResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  identityCenteredExceptionalDecisionCanonicalService.resolve
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du service porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalServiceResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalServiceResolvedEntry.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalDecisionCanonicalService_resolve_triplet
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue du service appartient bien
à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalServiceResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalServiceResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalService_resolve_inFamily
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la valeur résolue du service prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalServiceResolvedEntry_cases :
    couretExceptionalDecisionCanonicalServiceResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalServiceResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalService_resolve_value_cases
      couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale du service canonique :
- calibrage de la sortie ;
- raccord au workflow ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalServiceOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalService.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalService.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionCanonicalService.rows =
          identityCenteredExceptionalDecisionCanonicalWorkflow.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalService.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalService.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalService.hasEntry T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalService.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalService.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalService.resolve T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalServiceResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalServiceResolvedEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalServiceResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalServiceResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalService_length,
    identityCenteredExceptionalDecisionCanonicalService_triplet,
    identityCenteredExceptionalDecisionCanonicalService_fromWorkflow,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalServiceResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalServiceResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalServiceResolvedEntry_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalService_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalService_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalService_hasEntry_of_mem_family hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalService_resolve_triplet hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalService_resolve_mem_rows hT
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalService_resolve_value_cases hT

end

end CouretUnification.Core