import CouretUnification.Core.ExceptionalDecisionCanonicalAPIOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Lemmes de migration pour la couche canonique des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

But :
- faciliter les `rw` et `simpa` ;
- fournir des égalités courtes vers la sortie canonique ;
- aider à migrer progressivement les anciens fichiers historiques
  vers l’API stable introduite dans
  `ExceptionalDecisionCanonicalAPIOnIdentityTriplets`.
-/

/-- Réécriture de `Final.rows` vers la sortie canonique. -/
theorem identityCenteredExceptionalDecisionFinal_rows_toCanonical :
    identityCenteredExceptionalDecisionFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinal

/-- Réécriture de `FinalSummary.rows` vers la sortie canonique. -/
theorem identityCenteredExceptionalDecisionFinalSummary_rows_toCanonical :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalSummary

/-- Réécriture de `FinalView.rows` vers la sortie canonique. -/
theorem identityCenteredExceptionalDecisionFinalView_rows_toCanonical :
    identityCenteredExceptionalDecisionFinalView.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalView

/-- Réécriture de `FinalViewFinal.rows` vers la sortie canonique. -/
theorem identityCenteredExceptionalDecisionFinalViewFinal_rows_toCanonical :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalViewFinal

/-- Réécriture de `FinalViewFinalFinal.rows` vers la sortie canonique. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_toCanonical :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalViewFinalFinal

/--
Réécriture de la table décidable `Final`, oubliée vers `(triplet, valeur)`,
vers la sortie canonique.
-/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_toCanonical :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalDecidableTable

/--
Réécriture de la table booléenne `Final`, oubliée vers `(triplet, valeur)`,
vers la sortie canonique.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_toCanonical :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalBooleanTable

/--
Réécriture de la table décidable `FinalView`, oubliée vers `(triplet, valeur)`,
vers la sortie canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_toCanonical :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalViewDecidableTable

/--
Réécriture de la table booléenne `FinalView`, oubliée vers `(triplet, valeur)`,
vers la sortie canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_toCanonical :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalAPI_fromFinalViewBooleanTable

/-- La sortie canonique a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalRows_length :
    exceptionalDecisionCanonicalRowsOnIdentityTriplets.length = 21 := by
  exact exceptionalDecisionCanonicalAPI_length

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem exceptionalDecisionCanonicalRows_triplet :
    exceptionalDecisionCanonicalRowsOnIdentityTriplets.map Prod.fst =
      identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalAPI_triplet

/--
Toute ligne de la sortie canonique porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionCanonicalRows_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets) :
    p.1 ∈ identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalAPI_mem_family hp

/--
Version `iff` pratique pour migrer des preuves de membership
sur `Final.rows`.
-/
theorem mem_identityCenteredExceptionalDecisionFinal_rows_iff_canonical
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinal.rows ↔
      p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  constructor <;> intro hp <;> simpa [identityCenteredExceptionalDecisionFinal_rows_toCanonical] using hp

/--
Version `iff` pratique pour migrer des preuves de membership
sur `FinalView.rows`.
-/
theorem mem_identityCenteredExceptionalDecisionFinalView_rows_iff_canonical
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalView.rows ↔
      p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  constructor <;> intro hp <;> simpa [identityCenteredExceptionalDecisionFinalView_rows_toCanonical] using hp

/--
Version `iff` pratique pour migrer des preuves de membership
sur `FinalViewFinal.rows`.
-/
theorem mem_identityCenteredExceptionalDecisionFinalViewFinal_rows_iff_canonical
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows ↔
      p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  constructor <;> intro hp <;> simpa [identityCenteredExceptionalDecisionFinalViewFinal_rows_toCanonical] using hp

/--
Version `iff` pratique pour migrer des preuves de membership
sur `FinalViewFinalFinal.rows`.
-/
theorem mem_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_iff_canonical
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows ↔
      p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets := by
  constructor <;> intro hp <;> simpa [identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_toCanonical] using hp

/--
L’entrée canonique publique du cas Couret porte bien sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalEntry_triplet_rw :
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_triplet

/--
L’entrée canonique publique du cas Couret prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalEntry_cases_rw :
    couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_cases

/--
Validation groupée minimale des lemmes de migration :
- les principales couches historiques se réécrivent vers la sortie canonique ;
- la sortie canonique reste bien calibrée ;
- le cas Couret recolle bien à l’entrée publique stable.
-/
theorem exceptionalDecisionMigrationLemmasOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinal.rows =
        exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          exceptionalDecisionCanonicalRowsOnIdentityTriplets
      ∧ exceptionalDecisionCanonicalRowsOnIdentityTriplets.length = 21
      ∧ exceptionalDecisionCanonicalRowsOnIdentityTriplets.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ p, p ∈ exceptionalDecisionCanonicalRowsOnIdentityTriplets →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinal_rows_toCanonical,
    identityCenteredExceptionalDecisionFinalSummary_rows_toCanonical,
    identityCenteredExceptionalDecisionFinalView_rows_toCanonical,
    identityCenteredExceptionalDecisionFinalViewFinal_rows_toCanonical,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_toCanonical,
    exceptionalDecisionCanonicalRows_length,
    exceptionalDecisionCanonicalRows_triplet,
    ?_,
    couretExceptionalDecisionCanonicalEntry_triplet_rw,
    couretExceptionalDecisionCanonicalEntry_cases_rw
  ⟩
  intro p hp
  exact exceptionalDecisionCanonicalRows_mem_family hp

end

end CouretUnification.Core