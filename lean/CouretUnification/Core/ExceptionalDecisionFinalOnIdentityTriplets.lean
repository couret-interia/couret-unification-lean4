import CouretUnification.Core.ExceptionalDecisionBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue finale documentaire canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Elle stabilise simplement la liste des couples
`(triplet, valeur de décision)` déjà obtenue dans la chaîne documentaire.
-/
structure IdentityCenteredExceptionalDecisionFinal where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromSummary :
    rows = identityCenteredExceptionalDecisionSummary.rows

/--
Vue finale canonique minimale :
on reprend simplement le résumé documentaire canonique des décisions.
-/
def identityCenteredExceptionalDecisionFinal :
    IdentityCenteredExceptionalDecisionFinal where
  rows := identityCenteredExceptionalDecisionSummary.rows
  rows_len := identityCenteredExceptionalDecisionSummary.rows_len
  rows_fst := identityCenteredExceptionalDecisionSummary.rows_fst
  rows_fromSummary := rfl

/-- La vue finale canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinal_length :
    identityCenteredExceptionalDecisionFinal.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinal.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinal_triplet :
    identityCenteredExceptionalDecisionFinal.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinal.rows_fst

/--
La vue finale canonique coïncide bien avec le résumé documentaire canonique.
-/
theorem identityCenteredExceptionalDecisionFinal_coherence :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionSummary.rows := by
  exact identityCenteredExceptionalDecisionFinal.rows_fromSummary

/--
La vue finale canonique coïncide aussi avec la projection documentaire
de la table des décisions du paquet canonique.
-/
theorem identityCenteredExceptionalDecisionFinal_fromDecisionTable :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
  calc
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionSummary.rows := by
        exact identityCenteredExceptionalDecisionFinal_coherence
    _ =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
        exact identityCenteredExceptionalDecisionSummary_fromDecisionTable

/--
La vue finale canonique coïncide aussi avec la table décidable
des décisions, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinal_fromDecidableTable :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionSummary.rows := by
        exact identityCenteredExceptionalDecisionFinal_coherence
    _ =
      identityCenteredExceptionalDecisionShell.summary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionDecidableTable_forgetsToDecisionPairs.symm

/--
La vue finale canonique coïncide aussi avec la table booléenne
des décisions, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinal_fromBooleanTable :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionSummary.rows := by
        exact identityCenteredExceptionalDecisionFinal_coherence
    _ =
      identityCenteredExceptionalDecisionShell.summary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionBooleanTable_forgetsToDecisionPairs.symm

/--
Toute ligne de la vue finale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinal_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinal.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinal.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinal_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans la vue finale.
-/
def couretIdentityCenteredExceptionalDecisionFinalEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionSummaryEntry

/--
Dans le cas Couret, l’entrée documentaire canonique finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionSummaryEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionSummaryEntry_cases

/--
Validation groupée minimale de la vue finale canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinal.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          identityCenteredExceptionalDecisionSummary.rows
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          identityCenteredExceptionalDecisionPackage.decisionTable.map
            (fun D => (D.triplet, D.value))
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          identityCenteredExceptionalDecisionDecidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          identityCenteredExceptionalDecisionBooleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinal.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinal_length,
    identityCenteredExceptionalDecisionFinal_triplet,
    identityCenteredExceptionalDecisionFinal_coherence,
    identityCenteredExceptionalDecisionFinal_fromDecisionTable,
    identityCenteredExceptionalDecisionFinal_fromDecidableTable,
    identityCenteredExceptionalDecisionFinal_fromBooleanTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinal_mem_family hp

end

end CouretUnification.Core