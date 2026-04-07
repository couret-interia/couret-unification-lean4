import CouretUnification.Core.ExceptionalDecisionFinalViewFinalOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire canonique de la vue finale terminale des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il regroupe :
- le paquet booléen final de vue déjà stabilisé ;
- la vue finale terminale canonique des couples `(triplet, valeur de décision)` ;
- leurs cohérences documentaires minimales.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalPackage where
  booleanPackage : IdentityCenteredExceptionalDecisionFinalViewBooleanPackage
  finalView : IdentityCenteredExceptionalDecisionFinalViewFinal

  booleanToFinal :
    booleanPackage.booleanTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

  decidableToFinal :
    booleanPackage.decidableTable.map (fun E => (E.triplet, E.value)) =
      finalView.rows

/--
Paquet final terminal canonique minimal :
on regroupe simplement le paquet booléen final de vue déjà construit
et la vue finale terminale canonique qui en résume la sortie documentaire.
-/
def identityCenteredExceptionalDecisionFinalViewFinalPackage :
    IdentityCenteredExceptionalDecisionFinalViewFinalPackage where
  booleanPackage := identityCenteredExceptionalDecisionFinalViewBooleanPackage
  finalView := identityCenteredExceptionalDecisionFinalViewFinal

  booleanToFinal := by
    exact identityCenteredExceptionalDecisionFinalViewFinal_coherence

  decidableToFinal := by
    exact identityCenteredExceptionalDecisionFinalViewFinal_fromDecidableTable

/-- La table booléenne du paquet final terminal a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_booleanTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable_len

/-- La table décidable du paquet final terminal a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_decidableTable_length :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable_len

/-- La vue finale terminale du paquet a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_finalView_length :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows.length = 21 := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_triplet_projections :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
        (fun E => E.triplet) = identityCenteredTriplets
      ∧
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows.map Prod.fst =
        identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows_fst
  ⟩

/--
La table booléenne du paquet final terminal oublie bien vers la vue finale
terminale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanToFinal

/--
La table décidable du paquet final terminal oublie bien vers la vue finale
terminale canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalPackage.decidableToFinal

/--
Toute ligne de la vue finale terminale du paquet porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinal_mem_family hp

/--
Cas Couret : l’entrée documentaire canonique finale terminale porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalPackage_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_triplet

/--
Cas Couret : la valeur documentaire canonique finale terminale prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalPackage_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_cases

/--
Validation groupée minimale du paquet final terminal canonique de la vue
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalPackage_booleanTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalPackage_decidableTable_length,
    identityCenteredExceptionalDecisionFinalViewFinalPackage_finalView_length,
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows_fst,
    identityCenteredExceptionalDecisionFinalViewFinalPackage_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewFinalPackage_fromDecidableTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalPackage_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalPackage_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinalPackage_mem_family hp

end

end CouretUnification.Core