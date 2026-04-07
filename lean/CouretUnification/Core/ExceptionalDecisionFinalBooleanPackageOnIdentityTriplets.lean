import CouretUnification.Core.ExceptionalDecisionFinalBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la couche booléenne finale des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- la table décidable finale des décisions canoniques ;
- la table booléenne explicite finale associée ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalDecisionFinalDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalDecisionFinalBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_fromDecidableTable :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique minimal :
on regroupe simplement la table décidable finale déjà construite
et la table booléenne explicite finale qui en est extraite.
-/
def identityCenteredExceptionalDecisionFinalBooleanPackage :
    IdentityCenteredExceptionalDecisionFinalBooleanPackage where
  decidableTable := identityCenteredExceptionalDecisionFinalDecidableTable
  decidableTable_len := identityCenteredExceptionalDecisionFinalDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalDecisionFinalDecidableTable_triplet

  booleanTable := identityCenteredExceptionalDecisionFinalBooleanTable
  booleanTable_len := identityCenteredExceptionalDecisionFinalBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalDecisionFinalBooleanTable_triplet
  booleanTable_fromDecidableTable := by
    calc
      identityCenteredExceptionalDecisionFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionFinalShell.summary.rows := by
          exact identityCenteredExceptionalDecisionFinalBooleanTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) := by
          exact identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs.symm

/-- La table décidable du paquet canonique final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne du paquet canonique final est bien la projection documentaire
de la table décidable finale sous-jacente.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_coherence :
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_fromDecidableTable

/--
Toute ligne de la table booléenne du paquet canonique final porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_booleanTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalBooleanEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_triplet] using hmem

/--
Toute ligne de la table décidable du paquet canonique final porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_decidableTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalDecidableEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable_triplet] using hmem

/--
Cas Couret : la ligne booléenne finale canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_triplet

/--
Cas Couret : la ligne booléenne finale canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_cases

/--
Cas Couret : la présentation booléenne explicite finale canonique prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = false := by
  exact couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_boolValue_cases

/--
Validation groupée minimale du paquet canonique booléen final des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.boolValue = false) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalBooleanPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalBooleanPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalBooleanPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_cases,
    couretIdentityCenteredExceptionalDecisionFinalBooleanPackage_boolValue_cases
  ⟩
  · intro E hE
    exact identityCenteredExceptionalDecisionFinalBooleanPackage_decidableTable_mem_family hE
  · intro E hE
    exact identityCenteredExceptionalDecisionFinalBooleanPackage_booleanTable_mem_family hE

end

end CouretUnification.Core