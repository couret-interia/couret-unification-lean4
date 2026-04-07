import CouretUnification.Core.ExceptionalDecisionFinalViewOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Couche terminale canonique des décisions sur la famille finie
des 21 triplets centrés sur l’identité.

À partir de ce fichier, on choisit explicitement une représentation terminale
unique de la sortie documentaire :
- une liste de couples `(triplet, valeur de décision)` ;
- sa longueur documentaire ;
- sa projection sur les triplets ;
- son identification à la vue canonique retenue comme référence.

But architectural :
- arrêter la prolifération des couches `Final...Final...` ;
- fixer un point terminal stable ;
- normaliser les couches aval vers cette représentation unique.
-/
structure IdentityCenteredExceptionalDecisionTerminal where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets
  rows_fromFinalView :
    rows = identityCenteredExceptionalDecisionFinalView.rows

/--
Couche terminale canonique minimale :
on choisit comme représentation de référence la vue
`identityCenteredExceptionalDecisionFinalView`.
-/
def identityCenteredExceptionalDecisionTerminal :
    IdentityCenteredExceptionalDecisionTerminal where
  rows := identityCenteredExceptionalDecisionFinalView.rows
  rows_len := identityCenteredExceptionalDecisionFinalView.rows_len
  rows_fst := identityCenteredExceptionalDecisionFinalView.rows_fst
  rows_fromFinalView := rfl

/-- La couche terminale canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionTerminal_length :
    identityCenteredExceptionalDecisionTerminal.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionTerminal.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionTerminal_triplet :
    identityCenteredExceptionalDecisionTerminal.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionTerminal.rows_fst

/--
La couche terminale canonique coïncide bien avec la vue
retenue comme référence terminale.
-/
theorem identityCenteredExceptionalDecisionTerminal_coherence :
    identityCenteredExceptionalDecisionTerminal.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
  exact identityCenteredExceptionalDecisionTerminal.rows_fromFinalView

/--
La couche terminale canonique coïncide aussi avec la vue finale
canonique suivante déjà stabilisée en aval.
-/
theorem identityCenteredExceptionalDecisionTerminal_fromFinalViewFinal :
    identityCenteredExceptionalDecisionTerminal.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
  calc
    identityCenteredExceptionalDecisionTerminal.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
        exact identityCenteredExceptionalDecisionTerminal_coherence
    _ =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_fromFinalView.symm

/--
La couche terminale canonique coïncide aussi avec la vue finale
canonique terminale ultime déjà stabilisée encore plus en aval.
-/
theorem identityCenteredExceptionalDecisionTerminal_fromFinalViewFinalFinal :
    identityCenteredExceptionalDecisionTerminal.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
  calc
    identityCenteredExceptionalDecisionTerminal.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        exact identityCenteredExceptionalDecisionTerminal_fromFinalViewFinal
    _ =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinal_fromFinalView.symm

/--
Toute ligne de la couche terminale porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionTerminal_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionTerminal.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hmem :
      p.1 ∈ identityCenteredExceptionalDecisionTerminal.rows.map Prod.fst := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  simpa [identityCenteredExceptionalDecisionTerminal_triplet] using hmem

/--
Entrée documentaire canonique du cas Couret dans la couche terminale.
-/
def couretIdentityCenteredExceptionalDecisionTerminalEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionFinalViewEntry

/--
Dans le cas Couret, l’entrée documentaire canonique terminale
porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionTerminalEntry_triplet :
    couretIdentityCenteredExceptionalDecisionTerminalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_triplet

/--
Dans le cas Couret, la valeur documentaire canonique terminale
prend bien l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionTerminalEntry_cases :
    couretIdentityCenteredExceptionalDecisionTerminalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionTerminalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionFinalViewEntry_cases

/--
Validation groupée minimale de la couche terminale canonique
des décisions sur la famille identité.
-/
theorem exceptionalDecisionTerminalOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionTerminal.rows.length = 21
      ∧ identityCenteredExceptionalDecisionTerminal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionTerminal.rows =
          identityCenteredExceptionalDecisionFinalView.rows
      ∧ identityCenteredExceptionalDecisionTerminal.rows =
          identityCenteredExceptionalDecisionFinalViewFinal.rows
      ∧ identityCenteredExceptionalDecisionTerminal.rows =
          identityCenteredExceptionalDecisionFinalViewFinalFinal.rows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionTerminal.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionTerminalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionTerminalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionTerminalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionTerminal_length,
    identityCenteredExceptionalDecisionTerminal_triplet,
    identityCenteredExceptionalDecisionTerminal_coherence,
    identityCenteredExceptionalDecisionTerminal_fromFinalViewFinal,
    identityCenteredExceptionalDecisionTerminal_fromFinalViewFinalFinal,
    ?_,
    couretIdentityCenteredExceptionalDecisionTerminalEntry_triplet,
    couretIdentityCenteredExceptionalDecisionTerminalEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionTerminal_mem_family hp

end

end CouretUnification.Core