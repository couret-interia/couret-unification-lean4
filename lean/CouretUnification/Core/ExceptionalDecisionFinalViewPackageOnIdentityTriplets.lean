import CouretUnification.Core.ExceptionalDecisionFinalViewOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la vue finale des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- le paquet booléen final déjà stabilisé ;
- la vue finale canonique des couples `(triplet, valeur de décision)` ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewPackage where
  booleanPackage : IdentityCenteredExceptionalDecisionFinalBooleanPackage
  finalView : IdentityCenteredExceptionalDecisionFinalView

  booleanToFinal :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

  decidableToFinal :
    booleanPackage.decidableTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

/--
Paquet final canonique minimal :
on regroupe simplement le paquet booléen final déjà construit
et la vue finale canonique qui en résume la sortie documentaire.
-/
def identityCenteredExceptionalDecisionFinalViewPackage :
    IdentityCenteredExceptionalDecisionFinalViewPackage where
  booleanPackage := identityCenteredExceptionalDecisionFinalBooleanPackage
  finalView := identityCenteredExceptionalDecisionFinalView

  booleanToFinal := by
    exact identityCenteredExceptionalDecisionFinalView_coherence

  decidableToFinal := by
    exact identityCenteredExceptionalDecisionFinalView_fromDecidableTable

/-- La table booléenne du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable_len

/-- La table décidable du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable_len

/-- La vue finale du paquet final a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewPackage_finalView_length :
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows.map Prod.fst =
        identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows_fst
  ⟩

/--
La table booléenne du paquet final oublie bien vers la vue finale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewPackage_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewPackage.booleanToFinal

/--
La table décidable du paquet final oublie bien vers la vue finale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewPackage_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewPackage.decidableToFinal

/--
Toute ligne de la vue finale du paquet final porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewPackage_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalView_mem_family hp

/--
Cas Couret : l’entrée documentaire canonique finale porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet

/--
Cas Couret : la valeur documentaire canonique finale prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases

/--
Validation groupée minimale du paquet final canonique de la vue des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewPackage_finalView_length,
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows_fst,
    identityCenteredExceptionalDecisionFinalViewPackage_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewPackage_fromDecidableTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewPackage_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewPackage_mem_family hp

end

end CouretUnification.Core