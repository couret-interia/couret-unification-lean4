import CouretUnification.Core.ExceptionalDecisionFinalPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire final canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Il condense simplement la vue finale déjà stabilisée :
- une liste de couples `(triplet, valeur de décision)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale du paquet canonique.
-/
structure IdentityCenteredExceptionalDecisionFinalSummary where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalPackage :
    rows = identityCenteredExceptionalDecisionFinalPackage.finalView.rows

/--
Résumé final canonique minimal :
on reprend simplement la vue finale déjà stabilisée dans le paquet final.
-/
def identityCenteredExceptionalDecisionFinalSummary :
    IdentityCenteredExceptionalDecisionFinalSummary where
  rows := identityCenteredExceptionalDecisionFinalPackage.finalView.rows
  rows_len := identityCenteredExceptionalDecisionFinalPackage.finalView.rows_len
  rows_fst := identityCenteredExceptionalDecisionFinalPackage.finalView.rows_fst
  rows_fromFinalPackage := rfl

/-- Le résumé final canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalSummary_length :
    identityCenteredExceptionalDecisionFinalSummary.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalSummary.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalSummary_triplet :
    identityCenteredExceptionalDecisionFinalSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalSummary.rows_fst

/--
Le résumé final canonique coïncide bien avec la vue finale
déjà stabilisée dans le paquet final.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_coherence :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalSummary.rows_fromFinalPackage

/--
Le résumé final canonique coïncide aussi avec le résumé documentaire
canonique précédent.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_fromSummary :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionSummary.rows := by
  calc
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionSummary.rows := by
        exact identityCenteredExceptionalDecisionFinal_coherence

/--
Le résumé final canonique coïncide aussi avec la projection documentaire
de la table des décisions du paquet canonique.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_fromDecisionTable :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
        exact identityCenteredExceptionalDecisionFinal_fromDecisionTable

/--
Le résumé final canonique coïncide aussi avec la table décidable
des décisions, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinal_fromDecidableTable

/--
Le résumé final canonique coïncide aussi avec la table booléenne
des décisions, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinal_fromBooleanTable

/--
Toute ligne du résumé final porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalSummary.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalSummary.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalSummary_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans le résumé final.
-/
def couretIdentityCenteredExceptionalDecisionFinalSummaryEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalEntry

/--
Dans le cas Couret, l’entrée documentaire canonique finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalEntry_cases

/--
Validation groupée minimale du résumé final canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalSummary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionSummary.rows
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionPackage.decisionTable.map
            (fun D => (D.triplet, D.value))
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionDecidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionBooleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalSummary.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalSummary_length,
    identityCenteredExceptionalDecisionFinalSummary_triplet,
    identityCenteredExceptionalDecisionFinalSummary_coherence,
    identityCenteredExceptionalDecisionFinalSummary_fromSummary,
    identityCenteredExceptionalDecisionFinalSummary_fromDecisionTable,
    identityCenteredExceptionalDecisionFinalSummary_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalSummary_fromBooleanTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalSummaryEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalSummary_mem_family hp

end

end CouretUnification.Core