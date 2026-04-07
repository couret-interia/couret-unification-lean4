import CouretUnification.Core.ExceptionalDecisionBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la couche booléenne des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- la table décidable des décisions canoniques ;
- la table booléenne explicite associée ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalDecisionDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalDecisionBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_fromDecidableTable :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique minimal :
on regroupe simplement la table décidable déjà construite
et la table booléenne explicite qui en est extraite.
-/
def identityCenteredExceptionalDecisionBooleanPackage :
    IdentityCenteredExceptionalDecisionBooleanPackage where
  decidableTable := identityCenteredExceptionalDecisionDecidableTable
  decidableTable_len := identityCenteredExceptionalDecisionDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalDecisionDecidableTable_triplet

  booleanTable := identityCenteredExceptionalDecisionBooleanTable
  booleanTable_len := identityCenteredExceptionalDecisionBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalDecisionBooleanTable_triplet
  booleanTable_fromDecidableTable :=
    by
      calc
        identityCenteredExceptionalDecisionBooleanTable.map
            (fun E => (E.triplet, E.value)) =
          identityCenteredExceptionalDecisionShell.summary.rows := by
            exact identityCenteredExceptionalDecisionBooleanTable_forgetsToDecisionPairs
        _ =
          identityCenteredExceptionalDecisionDecidableTable.map
            (fun E => (E.triplet, E.value)) := by
            exact identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs.symm

/-- La table décidable du paquet canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionBooleanPackage_decidableTable_length :
    identityCenteredExceptionalDecisionBooleanPackage.decidableTable.length = 21 := by
  exact identityCenteredExceptionalDecisionBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionBooleanPackage_booleanTable_length :
    identityCenteredExceptionalDecisionBooleanPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalDecisionBooleanPackage.booleanTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionBooleanPackage_triplet_projections :
    identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne du paquet canonique est bien la projection documentaire
de la table décidable sous-jacente.
-/
theorem identityCenteredExceptionalDecisionBooleanPackage_coherence :
    identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalDecisionBooleanPackage.booleanTable_fromDecidableTable

/--
Toute ligne de la table booléenne du paquet canonique porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionBooleanPackage_booleanTable_mem_family
    {E : IdentityCenteredExceptionalDecisionBooleanEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionBooleanPackage.booleanTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionBooleanPackage.booleanTable_triplet] using hmem

/--
Toute ligne de la table décidable du paquet canonique porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionBooleanPackage_decidableTable_mem_family
    {E : IdentityCenteredExceptionalDecisionDecidableEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionBooleanPackage.decidableTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionBooleanPackage.decidableTable_triplet] using hmem

/--
Cas Couret : la ligne booléenne canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanPackage_triplet :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionBooleanEntry_triplet

/--
Cas Couret : la ligne booléenne canonique prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanPackage_cases :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionBooleanEntry_cases

/--
Cas Couret : la présentation booléenne explicite canonique prend bien
l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionBooleanPackage_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = false := by
  exact couretIdentityCenteredExceptionalDecisionBooleanEntry_boolValue_cases

/--
Validation groupée minimale du paquet canonique booléen des décisions
sur la famille identité.
-/
theorem exceptionalDecisionBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionBooleanPackage.decidableTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionBooleanPackage.booleanTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionBooleanEntry.boolValue = false) := by
  refine ⟨
    identityCenteredExceptionalDecisionBooleanPackage_decidableTable_length,
    identityCenteredExceptionalDecisionBooleanPackage_booleanTable_length,
    identityCenteredExceptionalDecisionBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionBooleanPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionBooleanPackage_triplet,
    couretIdentityCenteredExceptionalDecisionBooleanPackage_cases,
    couretIdentityCenteredExceptionalDecisionBooleanPackage_boolValue_cases
  ⟩
  · intro E hE
    exact identityCenteredExceptionalDecisionBooleanPackage_decidableTable_mem_family hE
  · intro E hE
    exact identityCenteredExceptionalDecisionBooleanPackage_booleanTable_mem_family hE

end

end CouretUnification.Core