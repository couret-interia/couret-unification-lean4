import CouretUnification.Core.ExceptionalDecisionNormalizationOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Couche de compatibilité documentaire pour les décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

But :
- fixer une API terminale compacte ;
- fournir quelques alias canoniques stables ;
- permettre aux anciens noms `Final...`, `FinalView...`, etc.
  de recoller explicitement à la représentation terminale choisie.
-/

/--
Alias de type canonique : la structure terminale devient la référence stable
pour la suite du développement.
-/
abbrev IdentityCenteredExceptionalDecisionCanonical :=
  IdentityCenteredExceptionalDecisionTerminal

/--
Alias de valeur canonique : représentation terminale stable des décisions
sur la famille identité.
-/
abbrev identityCenteredExceptionalDecisionCanonical :
    IdentityCenteredExceptionalDecisionCanonical :=
  identityCenteredExceptionalDecisionTerminal

/--
Alias canonique de la sortie documentaire finale :
la liste des couples `(triplet, valeur de décision)` portée
par la couche terminale.
-/
abbrev identityCenteredExceptionalDecisionCanonicalRows :
    List (Triplet × ExceptionalDecisionValue) :=
  identityCenteredExceptionalDecisionCanonical.rows

/--
L’alias canonique a bien longueur `21`.
-/
theorem identityCenteredExceptionalDecisionCanonical_length :
    identityCenteredExceptionalDecisionCanonicalRows.length = 21 := by
  exact identityCenteredExceptionalDecisionTerminal_length

/--
L’alias canonique projette bien sur la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonical_triplet :
    identityCenteredExceptionalDecisionCanonicalRows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionTerminal_triplet

/--
Entrée canonique stable du cas Couret dans l’API de compatibilité.
-/
abbrev couretIdentityCenteredExceptionalDecisionCanonicalEntry :
    Triplet × ExceptionalDecisionValue :=
  couretIdentityCenteredExceptionalDecisionTerminalEntry

/--
Dans le cas Couret, l’entrée canonique stable porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionCanonicalEntry_triplet :
    couretIdentityCenteredExceptionalDecisionCanonicalEntry.1 = couretTriplet := by
  exact couretIdentityCenteredExceptionalDecisionTerminalEntry_triplet

/--
Dans le cas Couret, l’entrée canonique stable prend bien
l’une des deux valeurs prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionCanonicalEntry_cases :
    couretIdentityCenteredExceptionalDecisionCanonicalEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionCanonicalEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecisionTerminalEntry_cases

/--
Compatibilité explicite : la couche `Final` se réécrit vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinal_compat :
    identityCenteredExceptionalDecisionFinal.rows =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinal_normalizesToTerminal

/--
Compatibilité explicite : la couche `FinalSummary` se réécrit
vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalSummary_compat :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalSummary_normalizesToTerminal

/--
Compatibilité explicite : la couche `FinalView` se réécrit
vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalView_compat :
    identityCenteredExceptionalDecisionFinalView.rows =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalView_normalizesToTerminal

/--
Compatibilité explicite : la couche `FinalViewFinal` se réécrit
vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinal_compat :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalViewFinal_normalizesToTerminal

/--
Compatibilité explicite : la couche `FinalViewFinalFinal` se réécrit
vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewFinalFinal_compat :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal_normalizesToTerminal

/--
Compatibilité explicite : la table décidable `Final` oubliée vers
`(triplet, valeur)` se réécrit vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalDecidableTable_compat :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalDecidableTable_normalizesToTerminal

/--
Compatibilité explicite : la table booléenne `Final` oubliée vers
`(triplet, valeur)` se réécrit vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalBooleanTable_compat :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalBooleanTable_normalizesToTerminal

/--
Compatibilité explicite : la table décidable `FinalView` oubliée vers
`(triplet, valeur)` se réécrit vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewDecidableTable_compat :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalViewDecidableTable_normalizesToTerminal

/--
Compatibilité explicite : la table booléenne `FinalView` oubliée vers
`(triplet, valeur)` se réécrit vers la couche canonique.
-/
theorem identityCenteredExceptionalDecisionFinalViewBooleanTable_compat :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalDecisionCanonicalRows := by
  exact identityCenteredExceptionalDecisionFinalViewBooleanTable_normalizesToTerminal

/--
Toute ligne de l’API canonique stable porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonical_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalRows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionTerminal_mem_family hp

/--
Validation groupée minimale de la couche de compatibilité :
- l’alias canonique est bien calibré ;
- les principales couches historiques se réécrivent vers lui ;
- le cas Couret recolle bien à l’entrée terminale stable.
-/
theorem exceptionalDecisionCompatibilityOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalRows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalRows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          identityCenteredExceptionalDecisionCanonicalRows
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          identityCenteredExceptionalDecisionCanonicalRows
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          identityCenteredExceptionalDecisionCanonicalRows
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          identityCenteredExceptionalDecisionCanonicalRows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          identityCenteredExceptionalDecisionCanonicalRows
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalRows →
            p.1 ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionCanonicalEntry.1 = couretTriplet
      ∧ (couretIdentityCenteredExceptionalDecisionCanonicalEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionCanonicalEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonical_length,
    identityCenteredExceptionalDecisionCanonical_triplet,
    identityCenteredExceptionalDecisionFinal_compat,
    identityCenteredExceptionalDecisionFinalSummary_compat,
    identityCenteredExceptionalDecisionFinalView_compat,
    identityCenteredExceptionalDecisionFinalViewFinal_compat,
    identityCenteredExceptionalDecisionFinalViewFinalFinal_compat,
    ?_,
    couretIdentityCenteredExceptionalDecisionCanonicalEntry_triplet,
    couretIdentityCenteredExceptionalDecisionCanonicalEntry_cases
  ⟩
  intro p hp
  exact identityCenteredExceptionalDecisionCanonical_mem_family hp

end

end CouretUnification.Core