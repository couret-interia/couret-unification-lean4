import CouretUnification.Core.ExceptionalDecisionFinalViewBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la couche booléenne finale de vue
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- la table décidable finale de vue des décisions canoniques ;
- la table booléenne explicite finale associée ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalDecisionFinalViewDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalDecisionFinalViewBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_fromDecidableTable :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique minimal :
on regroupe simplement la table décidable finale de vue déjà construite
et la table booléenne explicite finale qui en est extraite.
-/
def identityCenteredExceptionalDecisionFinalViewBooleanPackage :
    IdentityCenteredExceptionalDecisionFinalViewBooleanPackage where
  decidableTable := identityCenteredExceptionalDecisionFinalViewDecidableTable
  decidableTable_len :=
    identityCenteredExceptionalDecisionFinalViewDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewDecidableTable_triplet

  booleanTable := identityCenteredExceptionalDecisionFinalViewBooleanTable
  booleanTable_len :=
    identityCenteredExceptionalDecisionFinalViewBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewBooleanTable_triplet
  booleanTable_fromDecidableTable := by
    calc
      identityCenteredExceptionalDecisionFinalViewBooleanTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
          exact
            identityCenteredExceptionalDecisionFinalViewBooleanTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinalViewDecidableTable.map
          (fun E => (E.triplet, E.value)) := by
          exact
            identityCenteredExceptionalDecisionFinalViewDecidableTable_forgetsToDecisionPairs.symm

/-- La table décidable du paquet canonique final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne du paquet canonique final est bien la projection documentaire
de la table décidable finale de vue sous-jacente.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_coherence :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_fromDecidableTable

/--
Toute ligne de la table booléenne du paquet canonique final porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_booleanTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewBooleanEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_triplet] using hmem

/--
Toute ligne de la table décidable du paquet canonique final porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_decidableTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewDecidableEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable_triplet] using hmem

/--
Cas Couret : la ligne booléenne finale canonique de vue porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_triplet

/--
Cas Couret : la ligne booléenne finale canonique de vue prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_cases

/--
Cas Couret : la présentation booléenne explicite finale canonique de vue
prend bien l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = false := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry_boolValue_cases

/--
Validation groupée minimale du paquet canonique booléen final de vue
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewBooleanEntry.boolValue = false) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewBooleanPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewBooleanPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewBooleanPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewBooleanPackage_boolValue_cases
  ⟩
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewBooleanPackage_decidableTable_mem_family hE
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewBooleanPackage_booleanTable_mem_family hE

end

end CouretUnification.Core