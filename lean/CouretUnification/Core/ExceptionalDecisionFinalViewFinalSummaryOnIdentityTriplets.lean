import CouretUnification.Core.ExceptionalDecisionFinalViewFinalPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire canonique de la vue finale terminale des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il condense simplement le paquet de vue finale terminale déjà stabilisé :
- une liste de couples `(triplet, valeur de décision)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale terminale du paquet canonique.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalSummary where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalViewFinalPackage :
    rows = identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows

/--
Résumé canonique minimal de la vue finale terminale :
on reprend simplement la vue finale terminale déjà stabilisée
dans le paquet de vue finale terminale.
-/
def identityCenteredExceptionalDecisionFinalViewFinalSummary :
    IdentityCenteredExceptionalDecisionFinalViewFinalSummary where
  rows := identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows
  rows_len := identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows_len
  rows_fst := identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows_fst
  rows_fromFinalViewFinalPackage := rfl

/-- Le résumé canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_length :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalViewFinalSummary.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinalSummary.rows_fst

/--
Le résumé canonique coïncide bien avec la vue finale terminale
déjà stabilisée dans le paquet de vue finale terminale.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_coherence :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalSummary.rows_fromFinalViewFinalPackage

/--
Le résumé canonique coïncide aussi avec la table booléenne finale terminale,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinalPackage_fromBooleanTable.symm

/--
Le résumé canonique coïncide aussi avec la table décidable finale terminale,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinalPackage_fromDecidableTable.symm

/--
Le résumé canonique coïncide aussi avec la vue finale terminale canonique
déjà stabilisée en amont.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_fromFinalView :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        rfl

/--
Toute ligne du résumé de vue finale terminale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalSummary_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans le résumé de vue finale terminale.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry

/--
Dans le cas Couret, l’entrée documentaire canonique du résumé de vue finale terminale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique du résumé de vue finale terminale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_cases

/--
Validation groupée minimale du résumé canonique de la vue finale terminale
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinalPackage.booleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
          identityCenteredExceptionalDecisionFinalViewFinal.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalSummary_length,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_coherence,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_fromFinalView,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalSummaryEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinalSummary_mem_family hp

end

end CouretUnification.Core