import CouretUnification.Core.ExceptionalDecisionFinalOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire final canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Il regroupe :
- le paquet booléen documentaire déjà stabilisé ;
- la vue finale canonique des couples `(triplet, valeur de décision)` ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalPackage where
  booleanPackage : IdentityCenteredExceptionalDecisionBooleanPackage
  finalView : IdentityCenteredExceptionalDecisionFinal

  booleanToFinal :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

  decidableToFinal :
    booleanPackage.decidableTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

/--
Paquet final canonique minimal :
on regroupe simplement le paquet booléen déjà construit
et la vue finale canonique qui en résume la sortie documentaire.
-/
def identityCenteredExceptionalDecisionFinalPackage :
    IdentityCenteredExceptionalDecisionFinalPackage where
  booleanPackage := identityCenteredExceptionalDecisionBooleanPackage
  finalView := identityCenteredExceptionalDecisionFinal

  booleanToFinal := by
    calc
      identityCenteredExceptionalDecisionBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionShell.summary.rows := by
          exact identityCenteredExceptionalDecisionBooleanTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinal.rows := by
          exact identityCenteredExceptionalDecisionFinal_fromBooleanTable.symm

  decidableToFinal := by
    calc
      identityCenteredExceptionalDecisionBooleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
        identityCenteredExceptionalDecisionShell.summary.rows := by
          exact identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs
      _ =
        identityCenteredExceptionalDecisionFinal.rows := by
          exact identityCenteredExceptionalDecisionFinal_fromDecidableTable.symm

/-- La table booléenne du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable_len

/-- La table décidable du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable_len

/-- La vue finale du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalPackage_finalView_length :
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows.map Prod.fst =
        identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows_fst
  ⟩

/--
La table booléenne du paquet final oublie bien vers la vue finale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalPackage_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalPackage.booleanToFinal

/--
La table décidable du paquet final oublie bien vers la vue finale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalPackage_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalPackage.decidableToFinal

/--
Toute ligne de la vue finale du paquet final porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalPackage_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalPackage.finalView.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinal_mem_family hp

/--
Cas Couret : l’entrée documentaire canonique finale porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalEntry_triplet

/--
Cas Couret : la valeur documentaire canonique finale prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalEntry_cases

/--
Validation groupée minimale du paquet final canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalPackage.finalView.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalPackage.finalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalPackage.finalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalPackage.finalView.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalPackage_finalView_length,
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows_fst,
    identityCenteredExceptionalDecisionFinalPackage_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalPackage_fromDecidableTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalPackage_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalPackage_mem_family hp

end

end CouretUnification.Core