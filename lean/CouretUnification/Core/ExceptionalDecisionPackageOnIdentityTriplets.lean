import CouretUnification.Core.ExceptionalDecisionTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Il regroupe :
- la table des décisions canoniques ponctuelles ;
- la table des couples `(triplet, valeur de décision)` ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionPackage where
  decisionTable : List IdentityCenteredExceptionalDecision
  decisionTable_len : decisionTable.length = 21
  decisionTable_triplet :
    decisionTable.map (fun D => D.triplet) = identityCenteredTriplets

  valueTable : List (Triplet × ExceptionalDecisionValue)
  valueTable_len : valueTable.length = 21
  valueTable_triplet :
    valueTable.map Prod.fst = identityCenteredTriplets
  valueTable_fromDecisionTable :
    valueTable =
      decisionTable.map (fun D => (D.triplet, D.value))

/--
Paquet canonique minimal :
on regroupe simplement la table des décisions déjà construite
et sa projection documentaire en couples `(triplet, valeur)`.
-/
def identityCenteredExceptionalDecisionPackage :
    IdentityCenteredExceptionalDecisionPackage where
  decisionTable := identityCenteredExceptionalDecisionTable
  decisionTable_len := identityCenteredExceptionalDecisionTable_length
  decisionTable_triplet := identityCenteredExceptionalDecisionTable_triplet

  valueTable := identityCenteredExceptionalDecisionValueTable
  valueTable_len := identityCenteredExceptionalDecisionValueTable_length
  valueTable_triplet := identityCenteredExceptionalDecisionValueTable_triplet
  valueTable_fromDecisionTable := rfl

/-- La table des décisions du paquet canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionPackage_decisionTable_length :
    identityCenteredExceptionalDecisionPackage.decisionTable.length = 21 := by
  exact identityCenteredExceptionalDecisionPackage.decisionTable_len

/-- La table des valeurs du paquet canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionPackage_valueTable_length :
    identityCenteredExceptionalDecisionPackage.valueTable.length = 21 := by
  exact identityCenteredExceptionalDecisionPackage.valueTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionPackage_triplet_projections :
    identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => D.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionPackage.valueTable.map Prod.fst =
        identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionPackage.decisionTable_triplet,
    identityCenteredExceptionalDecisionPackage.valueTable_triplet
  ⟩

/--
La table des valeurs du paquet canonique est bien la projection documentaire
de la table des décisions.
-/
theorem identityCenteredExceptionalDecisionPackage_coherence :
    identityCenteredExceptionalDecisionPackage.valueTable =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
  exact identityCenteredExceptionalDecisionPackage.valueTable_fromDecisionTable

/--
Toute ligne de la table des valeurs du paquet canonique porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionPackage_valueTable_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionPackage.valueTable) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionPackage.valueTable.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionPackage.valueTable_triplet] using hmem

/--
Toute entrée de la table des décisions du paquet canonique recolle bien
avec la partition canonique exceptionnelle / non exceptionnelle.
-/
theorem identityCenteredExceptionalDecisionPackage_mem_partition
    {D : IdentityCenteredExceptionalDecision}
    (_hD : D ∈ identityCenteredExceptionalDecisionPackage.decisionTable) :
    D.triplet ∈ identityCenteredExceptionalPartition.exceptionalPart
      ∨
      D.triplet ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
  exact D.mem_partition

/--
Cas Couret : la ligne canonique de décision porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionPackage_triplet :
    couretIdentityCenteredExceptionalDecisionTableEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionTableEntry_triplet

/--
Cas Couret : la ligne canonique de décision appartient bien
à la famille identité.
-/
theorem couretIdentityCenteredExceptionalDecisionPackage_inFamily :
    couretIdentityCenteredExceptionalDecisionTableEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretIdentityCenteredExceptionalDecisionTableEntry_inFamily

/--
Cas Couret : la ligne canonique prend bien l’une des deux valeurs
de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionPackage_cases :
    couretIdentityCenteredExceptionalDecisionTableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionTableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionTableEntry_cases

/--
Validation groupée minimale du paquet canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionPackage.decisionTable.length = 21
      ∧ identityCenteredExceptionalDecisionPackage.valueTable.length = 21
      ∧ identityCenteredExceptionalDecisionPackage.decisionTable.map
          (fun D => D.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionPackage.valueTable.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionPackage.valueTable =
          identityCenteredExceptionalDecisionPackage.decisionTable.map
            (fun D => (D.triplet, D.value))
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionPackage.valueTable →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ D, D ∈ identityCenteredExceptionalDecisionPackage.decisionTable →
            D.triplet ∈ identityCenteredExceptionalPartition.exceptionalPart
              ∨ D.triplet ∈ identityCenteredExceptionalPartition.nonExceptionalPart)
      ∧ couretIdentityCenteredExceptionalDecisionTableEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalDecisionTableEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretIdentityCenteredExceptionalDecisionTableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionTableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionPackage_decisionTable_length,
    identityCenteredExceptionalDecisionPackage_valueTable_length,
    identityCenteredExceptionalDecisionPackage.decisionTable_triplet,
    identityCenteredExceptionalDecisionPackage.valueTable_triplet,
    identityCenteredExceptionalDecisionPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionPackage_triplet,
    couretIdentityCenteredExceptionalDecisionPackage_inFamily,
    couretIdentityCenteredExceptionalDecisionPackage_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionPackage_valueTable_mem_family hp
  · intro D hD
    exact identityCenteredExceptionalDecisionPackage_mem_partition hD

end

end CouretUnification.Core