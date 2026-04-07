import CouretUnification.Core.ExceptionalDecisionFinalViewFinalBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la couche booléenne finale terminale de vue
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- la table décidable finale terminale de vue des décisions canoniques ;
- la table booléenne explicite finale terminale associée ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_fromDecidableTable :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique minimal :
on regroupe simplement la table décidable finale terminale de vue déjà construite
et la table booléenne explicite finale terminale qui en est extraite.
-/
def identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage :
    IdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage where
  decidableTable := identityCenteredExceptionalDecisionFinalViewFinalDecidableTable
  decidableTable_len :=
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_triplet

  booleanTable := identityCenteredExceptionalDecisionFinalViewFinalBooleanTable
  booleanTable_len :=
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_triplet
  booleanTable_fromDecidableTable := by
    calc
      identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
          exact
            identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) := by
          exact
            identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_forgetsToDecisionPairs.symm

/-- La table décidable du paquet canonique final terminal a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique final terminal a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne du paquet canonique final terminal est bien la projection documentaire
de la table décidable finale terminale de vue sous-jacente.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_coherence :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_fromDecidableTable

/--
Toute ligne de la table booléenne du paquet canonique final terminal porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_booleanTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_triplet] using hmem

/--
Toute ligne de la table décidable du paquet canonique final terminal porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_decidableTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewFinalDecidableEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable_triplet] using hmem

/--
Cas Couret : la ligne booléenne finale terminale canonique de vue porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_triplet

/--
Cas Couret : la ligne booléenne finale terminale canonique de vue prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_cases

/--
Cas Couret : la présentation booléenne explicite finale terminale canonique de vue
prend bien l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = false := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry_boolValue_cases

/--
Validation groupée minimale du paquet canonique booléen final terminal de vue
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry.boolValue = false) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_boolValue_cases
  ⟩
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_decidableTable_mem_family hE
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_booleanTable_mem_family hE

end

end CouretUnification.Core