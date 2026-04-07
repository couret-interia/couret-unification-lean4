import CouretUnification.Core.ExceptionalDecisionFinalViewBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue documentaire finale canonique terminale de la chaîne de vue
des décisions sur la famille finie des 21 triplets centrés sur l’identité.

Elle stabilise simplement la liste des couples
`(triplet, valeur de décision)` déjà obtenue dans le paquet booléen final de vue.
-/
structure IdentityCenteredExceptionalDecisionFinalViewFinal where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromBooleanPackage :
    rows =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value))

/--
Vue finale terminale canonique minimale :
on reprend simplement la projection documentaire du paquet booléen final de vue
déjà stabilisé.
-/
def identityCenteredExceptionalDecisionFinalViewFinal :
    IdentityCenteredExceptionalDecisionFinalViewFinal where
  rows :=
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
      (fun E => (E.triplet, E.value))
  rows_len := by
    simpa using
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_len
  rows_fst := by
    rw [List.map_map]
    have hfun :
        (Prod.fst ∘
          fun E : IdentityCenteredExceptionalDecisionFinalViewBooleanEntry =>
            (E.triplet, E.value)) =
          (fun E : IdentityCenteredExceptionalDecisionFinalViewBooleanEntry =>
            E.triplet) := by
      funext E
      rfl
    rw [hfun]
    exact
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable_triplet
  rows_fromBooleanPackage := rfl

/-- La vue finale terminale canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionFinalViewFinal_length :
    identityCenteredExceptionalDecisionFinalViewFinal.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionFinalViewFinal.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionFinalViewFinal_triplet :
    identityCenteredExceptionalDecisionFinalViewFinal.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionFinalViewFinal.rows_fst

/--
La vue finale terminale canonique coïncide bien avec la projection documentaire
du paquet booléen final de vue.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinal_coherence :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  exact identityCenteredExceptionalDecisionFinalViewFinal.rows_fromBooleanPackage

/--
La vue finale terminale canonique coïncide aussi avec la table décidable finale
de vue, oubliée vers les couples `(triplet, valeur)`.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinal_fromDecidableTable :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewBooleanPackage_coherence

/--
La vue finale terminale canonique coïncide aussi avec la vue finale canonique
précédente déjà stabilisée en amont.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinal_fromFinalView :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_coherence
    _ =
      identityCenteredExceptionalDecisionFinalView.rows := by
        exact identityCenteredExceptionalDecisionFinalView_coherence.symm

/--
Toute ligne de la vue finale terminale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinal_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionFinalViewFinal_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans la vue finale terminale.
-/
def couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewEntry

/--
Dans le cas Couret, l’entrée documentaire canonique finale terminale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_triplet :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique finale terminale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_cases :
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases

/--
Validation groupée minimale de la vue finale terminale canonique des décisions
sur la famille identité.
-/
theorem exceptionalDecisionFinalViewFinalOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinalViewFinal.rows.length = 21
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
            (fun E => (E.triplet, E.value))
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          identityCenteredExceptionalDecisionFinalView.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionFinalViewFinal_length,
    identityCenteredExceptionalDecisionFinalViewFinal_triplet,
    identityCenteredExceptionalDecisionFinalViewFinal_coherence,
    identityCenteredExceptionalDecisionFinalViewFinal_fromDecidableTable,
    identityCenteredExceptionalDecisionFinalViewFinal_fromFinalView,
    ?_,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_triplet,
    couretIdentityCenteredExceptionalDecisionFinalViewFinalEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionFinalViewFinal_mem_family hp

end

end CouretUnification.Core