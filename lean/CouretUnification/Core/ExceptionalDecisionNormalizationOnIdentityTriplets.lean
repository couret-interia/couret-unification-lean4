import CouretUnification.Core.ExceptionalDecisionTerminalOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalSummaryOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalShellOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalDecidableTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalBooleanTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalBooleanPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewSummaryOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewShellOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewDecidableTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewBooleanTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewBooleanPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalSummaryOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalShellOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalDecidableTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalBooleanTableOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalBooleanPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalPackageOnIdentityTriplets
import CouretUnification.Core.ExceptionalDecisionFinalViewFinalFinalSummaryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-
Normalisation terminale de la chaîne documentaire des décisions
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier a un rôle purement architectural :
- fixer `identityCenteredExceptionalDecisionTerminal.rows` comme représentation
  canonique terminale ;
- recoller vers cette représentation les différentes couches `Final...`,
  `FinalView...`, `FinalViewFinal...` et `FinalViewFinalFinal...` ;
- éviter toute poursuite infinie de wrappers extensionnellement équivalents.
-/

/-- La couche `Final` se normalise vers la couche terminale canonique. -/
theorem identityCenteredExceptionalDecisionFinal_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
        exact identityCenteredExceptionalDecisionFinalView_fromFinal.symm
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionTerminal_coherence.symm

/-- Le paquet `Final` se normalise lui aussi vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalPackage_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionFinal.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinal_normalizesToTerminal

/-- Le résumé `Final` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalSummary_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalPackage.finalView.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_coherence
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalPackage_normalizesToTerminal

/-- Le shell `Final` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalShell_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalShell.summary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalShell.summary.rows =
      identityCenteredExceptionalDecisionFinalSummary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalSummary_normalizesToTerminal

/-- La table décidable `Final` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalDecidableTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalShell_normalizesToTerminal

/-- La table booléenne `Final` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalBooleanTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalShell_normalizesToTerminal

/-- Le paquet booléen `Final`, côté booléen, se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_boolean_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalBooleanTable_normalizesToTerminal

/-- Le paquet booléen `Final`, côté décidable, se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalBooleanPackage_decidable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalDecidableTable_normalizesToTerminal

/-- La couche `FinalView` est précisément la référence terminale choisie. -/
theorem identityCenteredExceptionalDecisionFinalView_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  exact identityCenteredExceptionalDecisionTerminal_coherence.symm

/-- Le paquet `FinalView` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewPackage_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewPackage.finalView.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalView_normalizesToTerminal

/-- Le résumé `FinalView` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewSummary_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewSummary.rows =
      identityCenteredExceptionalDecisionFinalView.rows := by
        exact identityCenteredExceptionalDecisionFinalViewSummary_fromFinalView
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalView_normalizesToTerminal

/-- Le shell `FinalView` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewShell_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewShell.summary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewShell.summary.rows =
      identityCenteredExceptionalDecisionFinalViewSummary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewSummary_normalizesToTerminal

/-- La table décidable `FinalView` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalViewDecidableTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewShell_normalizesToTerminal

/-- La table booléenne `FinalView` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalViewBooleanTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewShell_normalizesToTerminal

/-- Le paquet booléen `FinalView`, côté booléen, se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_boolean_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewBooleanTable_normalizesToTerminal

/-- Le paquet booléen `FinalView`, côté décidable, se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewBooleanPackage_decidable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewDecidableTable_normalizesToTerminal

/-- La couche `FinalViewFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinal_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  exact identityCenteredExceptionalDecisionTerminal_fromFinalViewFinal.symm

/-- Le paquet `FinalViewFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalPackage_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_normalizesToTerminal

/-- Le résumé `FinalViewFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalSummary_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalSummary_fromFinalView
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinal_normalizesToTerminal

/-- Le shell `FinalViewFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalShell_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalSummary.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalSummary_normalizesToTerminal

/-- La table décidable `FinalViewFinal` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalShell_normalizesToTerminal

/-- La table booléenne `FinalViewFinal` oubliée vers `(triplet, valeur)` se normalise. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_forgetsToDecisionPairs
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalShell_normalizesToTerminal

/-- La couche `FinalViewFinalFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  exact identityCenteredExceptionalDecisionTerminal_fromFinalViewFinalFinal.symm

/-- Le paquet `FinalViewFinalFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalPackage_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinalPackage.finalView.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
        rfl
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinal_normalizesToTerminal

/-- Le résumé `FinalViewFinalFinal` se normalise vers la couche terminale. -/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_normalizesToTerminal :
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionTerminal.rows := by
  calc
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
      identityCenteredExceptionalDecisionFinalViewFinalFinal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_fromFinalView
    _ =
      identityCenteredExceptionalDecisionTerminal.rows := by
        exact identityCenteredExceptionalDecisionFinalViewFinalFinal_normalizesToTerminal

/--
Validation groupée minimale de la normalisation :
les principales couches documentaires de la tour se réécrivent
toutes vers la représentation terminale canonique.
-/
theorem exceptionalDecisionNormalizationOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionFinal.rows =
        identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalShell.summary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewSummary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewShell.summary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalSummary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalShell.summary.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalDecidableTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalBooleanTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          identityCenteredExceptionalDecisionTerminal.rows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinalSummary.rows =
          identityCenteredExceptionalDecisionTerminal.rows := by
  refine ⟨
    identityCenteredExceptionalDecisionFinal_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalSummary_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalShell_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalDecidableTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalBooleanTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalView_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewSummary_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewShell_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewDecidableTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewBooleanTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinal_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalSummary_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalShell_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalDecidableTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalBooleanTable_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_normalizesToTerminal,
    identityCenteredExceptionalDecisionFinalViewFinalFinalSummary_normalizesToTerminal
  ⟩

end

end CouretUnification.Core