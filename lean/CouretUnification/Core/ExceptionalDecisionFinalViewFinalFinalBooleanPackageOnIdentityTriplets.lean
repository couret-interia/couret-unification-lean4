import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la couche booléenne finale terminale ultime de vue
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- la table décidable finale terminale ultime de vue des décisions canoniques ;
- la table booléenne explicite finale terminale ultime associée ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage where
  decidableTable : List IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets

  booleanTable : List IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_fromDecidableTable :
    booleanTable.map (fun E => (E.triplet, E.value)) =
      decidableTable.map (fun E => (E.triplet, E.value))

/--
Paquet canonique minimal :
on regroupe simplement la table décidable finale terminale ultime de vue déjà construite
et la table booléenne explicite finale terminale ultime qui en est extraite.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage where
  decidableTable := identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable
  decidableTable_len :=
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_length
  decidableTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_triplet

  booleanTable := identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable
  booleanTable_len :=
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_length
  booleanTable_triplet :=
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_triplet
  booleanTable_fromDecidableTable := by
    calc
      identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionFinalViewFinalFinalShell.summary.rows := by
          exact
            identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) := by
          exact
            identityCenteredExceptionalDecisionFinalViewFinalFinalDecidableTable_forgetsToDecisionPairs.symm

/-- La table décidable du paquet canonique final terminal ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique final terminal ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable_len

/-- Les deux projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable_triplet
  ⟩

/--
La table booléenne du paquet canonique final terminal ultime est bien la projection documentaire
de la table décidable finale terminale ultime de vue sous-jacente.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_coherence :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable_fromDecidableTable

/--
Toute ligne de la table booléenne du paquet canonique final terminal ultime porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_booleanTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable_triplet] using hmem

/--
Toute ligne de la table décidable du paquet canonique final terminal ultime porte bien
sur un triplet de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_decidableTable_mem_family
    {E : IdentityCenteredExceptionalDecisionFinalViewFinalFinalDecidableEntry}
    (hE : E ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable) :
    E.triplet ∈ identityCenteredTriplets := by
  have hmem :
      E.triplet ∈
        identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.map
          (fun F => F.triplet) := by
    exact List.mem_map.mpr ⟨E, hE, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable_triplet] using hmem

/--
Cas Couret : la ligne booléenne finale terminale ultime canonique de vue porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.triplet = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_triplet

/--
Cas Couret : la ligne booléenne finale terminale ultime canonique de vue prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_cases

/--
Cas Couret : la présentation booléenne explicite finale terminale ultime canonique de vue
prend bien l’une des deux valeurs booléennes prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_boolValue_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = true
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = false := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry_boolValue_cases

/--
Validation groupée minimale du paquet canonique booléen final terminal ultime de vue
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable.map
              (fun E => (E.triplet, E.value))
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ (∀ E, E ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable →
            E.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.triplet =
          couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.value =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = true
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanEntry.boolValue = false) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_coherence,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_cases,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_boolValue_cases
  ⟩
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_decidableTable_mem_family hE
  · intro E hE
    exact
      identityCenteredExceptionalDecisionFinalViewFinalFinalBooleanPackage_booleanTable_mem_family hE

end

end CouretUnification.Core