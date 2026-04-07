import CouretUnification.Core.ExceptionalDecisionFinalBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue documentaire finale canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

Elle stabilise simplement la liste des couples
`(triplet, valeur de décision)` déjà obtenue dans le paquet booléen final.
-/
structure IdentityCenteredExceptionalDecisionFinalView where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromBooleanPackage :
    rows =
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value))

/--
Vue finale canonique minimale :
on reprend simplement la projection documentaire
du paquet booléen final déjà stabilisé.
-/
def identityCenteredExceptionalDecisionFinalView :
    IdentityCenteredExceptionalDecisionFinalView where
  rows :=
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
      (fun E => (E.triplet, E.value))
  rows_len := by
    simpa using
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_len
  rows_fst := by
    rw [List.map_map]
    have hfun :
        (Prod.fst ∘
          fun E : IdentityCenteredExceptionalDecisionFinalBooleanEntry =>
            (E.triplet, E.value)) =
          (fun E : IdentityCenteredExceptionalDecisionFinalBooleanEntry =>
            E.triplet) := by
      funext E
      rfl
    rw [hfun]
    exact
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable_triplet
  rows_fromBooleanPackage := rfl

/-- La vue finale canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalView_length :
    identityCenteredExceptionalDecisionFinalView.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalView.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalView_triplet :
    identityCenteredExceptionalDecisionFinalView.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalView.rows_fst

/--
La vue finale canonique coïncide bien avec la projection documentaire
du paquet booléen final.
-/
theorem identityCenteredExceptionalDecisionFinalView_coherence :
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalDecisionFinalView.rows_fromBooleanPackage

/--
La vue finale canonique coïncide aussi avec la table décidable finale,
oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalView_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalView_coherence
    _ =
      identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalBooleanPackage_coherence

/--
La vue finale canonique coïncide aussi avec la vue finale précédente
déjà stabilisée en amont de la chaîne.
-/
theorem identityCenteredExceptionalDecisionFinalView_fromFinal :
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionFinal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalView_fromDecidableTable
    _ =
      identityCenteredExceptionalDecisionFinalShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionFinalSummary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionFinal.rows := by
        exact identityCenteredExceptionalDecisionFinal_coherence.symm

/--
Toute ligne de la vue finale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalView_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalView.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalView.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalView_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans la vue finale.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewEntry :
    Triplet × ExceptionalDecisionValue :=
  ( couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.triplet
  , couretIdentityCenteredExceptionalDecisionFinalBooleanEntry.value )

/--
Dans le cas Couret, l’entrée documentaire canonique finale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewEntry.1 = couretTriplet := by
  simp [couretIdentityCenteredExceptionalDecisionFinalViewEntry,
    couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_triplet]

/--
Dans le cas Couret, la valeur documentaire canonique finale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  simpa [couretIdentityCenteredExceptionalDecisionFinalViewEntry]
    using couretIdentityCenteredExceptionalDecisionFinalBooleanEntry_cases

/--
Validation groupée minimale de la vue finale canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalView.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          identityCenteredExceptionalDecisionFinal.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalView.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalView_length,
    identityCenteredExceptionalDecisionFinalView_triplet,
    identityCenteredExceptionalDecisionFinalView_coherence,
    identityCenteredExceptionalDecisionFinalView_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalView_fromFinal,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalView_mem_family hp

end

end CouretUnification.Core