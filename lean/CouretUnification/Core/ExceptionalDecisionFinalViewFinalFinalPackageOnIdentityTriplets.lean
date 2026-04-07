import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la vue finale terminale ultime des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- le paquet booléen final terminal de vue déjà stabilisé ;
- la vue finale terminale ultime canonique des couples `(triplet, valeur de décision)` ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage where
  booleanPackage : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanPackage
  finalView : IdentityCenteredExceptionalDecisionFinalViewFinalFinal

  booleanToFinal :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

  decidableToFinal :
    booleanPackage.decidableTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

/--
Paquet final terminal ultime canonique minimal :
on regroupe simplement le paquet booléen final terminal de vue déjà construit
et la vue finale terminale ultime canonique qui en résume la sortie documentaire.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalPackage :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage where
  booleanPackage := identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage
  finalView := identityCenteredExceptionalDecisionFinalViewFinalFinal

  booleanToFinal := by
    exact identityCenteredExceptionalDecisionFinalViewFinalFinal_coherence

  decidableToFinal := by
    exact identityCenteredExceptionalDecisionFinalViewFinalFinal_fromDecidableTable

/-- La table booléenne du paquet final terminal ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable_len

/-- La table décidable du paquet final terminal ultime a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable_len

/-- La vue finale terminale ultime du paquet a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_finalView_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows.map Prod.fst =
        identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows_fst
  ⟩

/--
La table booléenne du paquet final terminal ultime oublie bien vers la vue finale
terminale ultime canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanToFinal

/--
La table décidable du paquet final terminal ultime oublie bien vers la vue finale
terminale ultime canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.decidableToFinal

/--
Toute ligne de la vue finale terminale ultime du paquet porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal_mem_family hp

/--
Cas Couret : l’entrée documentaire canonique finale terminale ultime porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_triplet

/--
Cas Couret : la valeur documentaire canonique finale terminale ultime prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_cases

/--
Validation groupée minimale du paquet final terminal ultime canonique de la vue
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_finalView_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows_fst,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromDecidableTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalPackage_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_mem_family hp

end

end CouretUnification.Core