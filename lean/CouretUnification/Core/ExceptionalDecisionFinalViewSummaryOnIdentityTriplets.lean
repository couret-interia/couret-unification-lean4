import CouretUnification.Core.ExceptionalDecisionFinalViewPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire canonique de la vue finale des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Il condense simplement le paquet de vue finale déjà stabilisé :
- une liste de couples `(triplet, valeur de décision)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue finale du paquet canonique.
-/
structure IdentityCenteredExceptionalDecisionFinalViewSummary where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalViewPackage :
    rows = identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows

/--
Résumé canonique minimal de la vue finale :
on reprend simplement la vue finale déjà stabilisée dans le paquet de vue finale.
-/
def identityCenteredExceptionalDecisionFinalViewSummary :
    IdentityCenteredExceptionalDecisionFinalViewSummary where
  rows := identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows
  rows_len := identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows_len
  rows_fst := identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows_fst
  rows_fromFinalViewPackage := rfl

/-- Le résumé canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewSummary_length :
    identityCenteredExceptionalDecisionFinalViewSummary.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalViewSummary.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewSummary_triplet :
    identityCenteredExceptionalDecisionFinalViewSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewSummary.rows_fst

/--
Le résumé canonique coïncide bien avec la vue finale
déjà stabilisée dans le paquet de vue finale.
-/
theorem identityCenteredExceptionalDecisionFinalViewSummary_coherence :
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
  exact identityCenteredExceptionalDecisionFinalViewSummary.rows_fromFinalViewPackage

/--
Le résumé canonique coïncide aussi avec la table booléenne finale,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewSummary_fromBooleanTable :
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewPackage_fromBooleanTable.symm

/--
Le résumé canonique coïncide aussi avec la table décidable finale,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewSummary_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewPackage_fromDecidableTable.symm

/--
Le résumé canonique coïncide aussi avec la vue finale canonique
déjà stabilisée en amont.
-/
theorem identityCenteredExceptionalDecisionFinalViewSummary_fromFinalView :
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewSummary_coherence
    _ =
      identityCenteredExceptionalDecisionFinalView.rows := by
        rfl

/--
Toute ligne du résumé de vue finale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewSummary_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewSummary.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalViewSummary.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewSummary_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans le résumé de vue finale.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewEntry

/--
Dans le cas Couret, l’entrée documentaire canonique du résumé de vue finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique du résumé de vue finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases

/--
Validation groupée minimale du résumé canonique de la vue finale
des décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewSummary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows =
          identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows =
          identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows =
          identityCenteredExceptionalDecisionFinalViewPackage.booleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows =
          identityCenteredExceptionalDecisionFinalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewSummary.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewSummary_length,
    identityCenteredExceptionalDecisionFinalViewSummary_triplet,
    identityCenteredExceptionalDecisionFinalViewSummary_coherence,
    identityCenteredExceptionalDecisionFinalViewSummary_fromBooleanTable,
    identityCenteredExceptionalDecisionFinalViewSummary_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalViewSummary_fromFinalView,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewSummaryEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewSummary_mem_family hp

end

end CouretUnification.Core