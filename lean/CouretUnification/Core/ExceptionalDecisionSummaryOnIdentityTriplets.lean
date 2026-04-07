import CouretUnification.Core.ExceptionalDecisionPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé documentaire canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Il condense simplement la table des couples
`(triplet, valeur de décision)` déjà stabilisée dans le paquet canonique.
-/
structure IdentityCenteredExceptionalDecisionSummary where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromPackage :
    rows = identityCenteredExceptionalDecisionPackage.valueTable

/--
Résumé canonique minimal :
on reprend simplement la table des couples `(triplet, valeur)`
déjà stabilisée dans le paquet documentaire des décisions.
-/
def identityCenteredExceptionalDecisionSummary :
    IdentityCenteredExceptionalDecisionSummary where
  rows := identityCenteredExceptionalDecisionPackage.valueTable
  rows_len := identityCenteredExceptionalDecisionPackage.valueTable_len
  rows_fst := identityCenteredExceptionalDecisionPackage.valueTable_triplet
  rows_fromPackage := rfl

/-- Le résumé canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionSummary_length :
    identityCenteredExceptionalDecisionSummary.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionSummary.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionSummary_triplet :
    identityCenteredExceptionalDecisionSummary.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionSummary.rows_fst

/--
Le résumé canonique coïncide bien avec la table des valeurs
du paquet canonique des décisions.
-/
theorem identityCenteredExceptionalDecisionSummary_coherence :
    identityCenteredExceptionalDecisionSummary.rows =
      identityCenteredExceptionalDecisionPackage.valueTable := by
  exact identityCenteredExceptionalDecisionSummary.rows_fromPackage

/--
Le résumé canonique coïncide aussi avec la projection documentaire
de la table des décisions du paquet canonique.
-/
theorem identityCenteredExceptionalDecisionSummary_fromDecisionTable :
    identityCenteredExceptionalDecisionSummary.rows =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
  calc
    identityCenteredExceptionalDecisionSummary.rows =
      identityCenteredExceptionalDecisionPackage.valueTable := by
        exact identityCenteredExceptionalDecisionSummary_coherence
    _ =
      identityCenteredExceptionalDecisionPackage.decisionTable.map
        (fun D => (D.triplet, D.value)) := by
        exact identityCenteredExceptionalDecisionPackage_coherence

/--
Toute ligne du résumé canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionSummary_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionSummary.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionSummary.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionSummary_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans le résumé des décisions.
-/
def couretIdentityCenteredExceptionalDecisionSummaryEntry :
    Triplet × ExceptionalDecisionValue :=
  ( couretIdentityCenteredExceptionalDecisionTableEntry.triplet
  , couretIdentityCenteredExceptionalDecisionTableEntry.value )

/--
Dans le cas Couret, l’entrée documentaire canonique du résumé
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionSummaryEntry_triplet :
    couretIdentityCenteredExceptionalDecisionSummaryEntry.1 = couretTriplet := by
  simp [couretIdentityCenteredExceptionalDecisionSummaryEntry,
    couretIdentityCenteredExceptionalDecisionTableEntry_triplet]

/--
Dans le cas Couret, la valeur documentaire canonique du résumé
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionSummaryEntry_cases :
    couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionSummaryEntry]
    using couretIdentityCenteredExceptionalDecisionTableEntry_cases

/--
Validation groupée minimale du résumé canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionSummaryOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionSummary.rows.length = 21
      ∧ identityCenteredExceptionalDecisionSummary.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionSummary.rows =
          identityCenteredExceptionalDecisionPackage.valueTable
      ∧ identityCenteredExceptionalDecisionSummary.rows =
          identityCenteredExceptionalDecisionPackage.decisionTable.map
            (fun D => (D.triplet, D.value))
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionSummary.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionSummaryEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionSummaryEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionSummary_length,
    identityCenteredExceptionalDecisionSummary_triplet,
    identityCenteredExceptionalDecisionSummary_coherence,
    identityCenteredExceptionalDecisionSummary_fromDecisionTable,
    ?_,
    couretIdentityCenteredExceptionalDecisionSummaryEntry_triplet,
    couretIdentityCenteredExceptionalDecisionSummaryEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionSummary_mem_family hp

end

end CouretUnification.Core