import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire canonique de la vue finale terminale ultime des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il condense simplement le paquet de vue finale terminale ultime déjà stabilisé :
- une liste de couples `(triplet, valeur de décision)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale terminale ultime du paquet canonique.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinalSummary where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalViewFinalFinalPackage :
    rows = identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows

/--
Résumé canonique minimal de la vue finale terminale ultime :
on reprend simplement la vue finale terminale ultime déjà stabilisée
dans le paquet de vue finale terminale ultime.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinalSummary :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinalSummary where
  rows := identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows
  rows_len := identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows_len
  rows_fst := identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows_fst
  rows_fromFinalViewFinalFinalPackage := rfl

/-- Le résumé canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows_fst

/--
Le résumé canonique coïncide bien avec la vue finale terminale ultime
déjà stabilisée dans le paquet de vue finale terminale ultime.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_coherence :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
  exact
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows_fromFinalViewFinalFinalPackage

/--
Le résumé canonique coïncide aussi avec la table booléenne finale terminale ultime,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact
          identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromBooleanTable.symm

/--
Le résumé canonique coïncide aussi avec la table décidable finale terminale ultime,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact
          identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_fromDecidableTable.symm

/--
Le résumé canonique coïncide aussi avec la vue finale terminale ultime canonique
déjà stabilisée en amont.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromFinalView :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
        rfl

/--
Toute ligne du résumé de vue finale terminale ultime porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈
        identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans le résumé de vue finale terminale ultime.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry

/--
Dans le cas Couret, l’entrée documentaire canonique du résumé de vue finale
terminale ultime porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique du résumé de vue finale
terminale ultime prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_cases

/--
Validation groupée minimale du résumé canonique de la vue finale terminale ultime
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.booleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalFinal.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_coherence,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromFinalView,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalSummaryEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_mem_family hp

end

end CouretUnification.Core