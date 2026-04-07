import CouretUnification.Core.ExceptionalDecisionFinalViewFinalBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue documentaire finale canonique terminale ultime de la chaîne de vue
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

Elle stabilise simplement la liste des couples
`(triplet, valeur de décision)` déjà obtenue dans le paquet booléen final
terminal de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinalFinal where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromBooleanPackage :
    rows =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value))

/--
Vue finale terminale ultime canonique minimale :
on reprend simplement la projection documentaire du paquet booléen final
terminal de vue déjà stabilisé.
-/
def identityCenteredExceptionalDecisionFinalViewFinalFinal :
    IdentityCenteredExceptionalDecisionFinalViewFinalFinal where
  rows :=
    identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
      (fun E => (E.triplet, E.value))
  rows_len := by
    simpa using
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_len
  rows_fst := by
    rw [List.map_map]
    have hfun :
        (Prod.fst ∘
          fun E : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry =>
            (E.triplet, E.value)) =
          (fun E : IdentityCenteredExceptionalDecisionFinalViewFinalBooleanEntry =>
            E.triplet) := by
      funext E
      rfl
    rw [hfun]
    exact
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable_triplet
  rows_fromBooleanPackage := rfl

/-- La vue finale terminale ultime canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_length :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_triplet :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal.rows_fst

/--
La vue finale terminale ultime canonique coïncide bien avec la projection
documentaire du paquet booléen final terminal de vue.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_coherence :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal.rows_fromBooleanPackage

/--
La vue finale terminale ultime canonique coïncide aussi avec la table
décidable finale terminale de vue, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinal_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage_coherence

/--
La vue finale terminale ultime canonique coïncide aussi avec la vue finale
terminale canonique précédente déjà stabilisée en amont.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_fromFinalView :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinal_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_coherence.symm

/--
Toute ligne de la vue finale terminale ultime porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinalFinal_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans la vue finale terminale ultime.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry

/--
Dans le cas Couret, l’entrée documentaire canonique finale terminale ultime
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique finale terminale ultime
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_cases

/--
Validation groupée minimale de la vue finale terminale ultime canonique des
décisions sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalFinalOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          identityCenteredExceptionalDecisionFinalViewFinalBooleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          identityCenteredExceptionalDecisionFinalViewFinal.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinalFinal_length,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_triplet,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_coherence,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_fromFinalView,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalFinalEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal_mem_family hp

end

end CouretUnification.Core