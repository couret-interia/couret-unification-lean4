import CouretUnification.Core.ExceptionalDecisionRefactorGuideOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Carte locale de dépréciation pour la couche documentaire des décisions
exceptionnelles sur la famille finie des 21 triplets centrés sur l’identité.

But :
- centraliser les anciens points d’entrée encore tolérés ;
- expliciter leur cible canonique recommandée ;
- fournir des lemmes de transition faciles à utiliser par `rw` / `simpa` ;
- préparer une migration progressive sans casser le dépôt.

Politique locale :

- les noms à privilégier désormais sont
  `recommendedExceptionalDecisionAPI`,
  `recommendedExceptionalDecisionRows`,
  `recommendedCouretExceptionalDecisionEntry` ;
- les noms historiques `Final`, `FinalView`, `FinalViewFinal`, etc.
  doivent être considérés comme hérités ;
- ce fichier ne crée aucune nouvelle couche mathématique :
  il ne fait que documenter et relier les anciens noms à la cible canonique.
-/

/--
Nom recommandé pour l’API stable des décisions exceptionnelles.
-/
abbrev exceptionalDecisionPreferredAPI :=
  recommendedExceptionalDecisionAPI

/--
Nom recommandé pour la sortie documentaire stable.
-/
abbrev exceptionalDecisionPreferredRows :
    List (Triplet × ExceptionalDecisionValue) :=
  recommendedExceptionalDecisionRows

/--
Nom recommandé pour l’entrée stable du cas Couret.
-/
abbrev exceptionalDecisionPreferredCouretEntry :
    Triplet × ExceptionalDecisionValue :=
  recommendedCouretExceptionalDecisionEntry

/-- La sortie recommandée a bien longueur `21`. -/
theorem exceptionalDecisionPreferredRows_length :
    exceptionalDecisionPreferredRows.length = 21 := by
  exact recommendedExceptionalDecisionRows_length

/-- La sortie recommandée projette bien sur la famille identité. -/
theorem exceptionalDecisionPreferredRows_triplet :
    exceptionalDecisionPreferredRows.map Prod.fst = identityCenteredTriplets := by
  exact recommendedExceptionalDecisionRows_triplet

/--
Toute ligne de la sortie recommandée porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionPreferredRows_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ exceptionalDecisionPreferredRows) :
    p.1 ∈ identityCenteredTriplets := by
  exact recommendedExceptionalDecisionRows_mem_family hp

/--
Ancien nom historique :
`identityCenteredExceptionalDecisionFinal.rows`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinal_rows_use_recommended :
    identityCenteredExceptionalDecisionFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinal_rows

/--
Ancien nom historique :
`identityCenteredExceptionalDecisionFinalSummary.rows`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalSummary_rows_use_recommended :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalSummary_rows

/--
Ancien nom historique :
`identityCenteredExceptionalDecisionFinalView.rows`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalView_rows_use_recommended :
    identityCenteredExceptionalDecisionFinalView.rows =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalView_rows

/--
Ancien nom historique :
`identityCenteredExceptionalDecisionFinalViewFinal.rows`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalViewFinal_rows_use_recommended :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalViewFinal_rows

/--
Ancien nom historique :
`identityCenteredExceptionalDecisionFinalViewFinalFinal.rows`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_use_recommended :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows

/--
Ancien nom historique :
table décidable `Final`, oubliée vers `(triplet, valeur)`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalDecidableTable_use_recommended :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalDecidableTable

/--
Ancien nom historique :
table booléenne `Final`, oubliée vers `(triplet, valeur)`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalBooleanTable_use_recommended :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalBooleanTable

/--
Ancien nom historique :
table décidable `FinalView`, oubliée vers `(triplet, valeur)`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalViewDecidableTable_use_recommended :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalViewDecidableTable

/--
Ancien nom historique :
table booléenne `FinalView`, oubliée vers `(triplet, valeur)`.

Remplacement recommandé :
`recommendedExceptionalDecisionRows`.
-/
theorem deprecated_identityCenteredExceptionalDecisionFinalViewBooleanTable_use_recommended :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact refactor_identityCenteredExceptionalDecisionFinalViewBooleanTable

/--
Forme `iff` de migration recommandée pour les preuves de membership
sur `Final.rows`.
-/
theorem deprecated_mem_Final_rows_use_recommended
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact refactor_mem_Final_rows

/--
Forme `iff` de migration recommandée pour les preuves de membership
sur `FinalView.rows`.
-/
theorem deprecated_mem_FinalView_rows_use_recommended
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalView.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact refactor_mem_FinalView_rows

/--
Forme `iff` de migration recommandée pour les preuves de membership
sur `FinalViewFinal.rows`.
-/
theorem deprecated_mem_FinalViewFinal_rows_use_recommended
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact refactor_mem_FinalViewFinal_rows

/--
Forme `iff` de migration recommandée pour les preuves de membership
sur `FinalViewFinalFinal.rows`.
-/
theorem deprecated_mem_FinalViewFinalFinal_rows_use_recommended
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact refactor_mem_FinalViewFinalFinal_rows

/--
Ancien nom historique pour l’entrée Couret :
on recommande désormais `recommendedCouretExceptionalDecisionEntry`.
-/
theorem deprecated_couret_entry_use_recommended_triplet :
    recommendedCouretExceptionalDecisionEntry.1 = couretTriplet := by
  exact recommendedCouretExceptionalDecisionEntry_triplet

/--
Ancien nom historique pour l’entrée Couret :
la valeur reste bien dans les deux cas prévus.
-/
theorem deprecated_couret_entry_use_recommended_cases :
    recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact recommendedCouretExceptionalDecisionEntry_cases

/--
Validation groupée minimale de la carte de dépréciation :
- le point d’entrée recommandé est bien calibré ;
- les principaux noms historiques se réécrivent vers lui ;
- les preuves de membership historiques disposent d’une passerelle ;
- le cas Couret recolle bien à l’entrée recommandée stable.
-/
theorem exceptionalDecisionDeprecationMapOnIdentityTriplets_valid :
    recommendedExceptionalDecisionRows.length = 21
      ∧ recommendedExceptionalDecisionRows.map Prod.fst = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinal.rows =
          recommendedExceptionalDecisionRows
      ∧ identityCenteredExceptionalDecisionFinalSummary.rows =
          recommendedExceptionalDecisionRows
      ∧ identityCenteredExceptionalDecisionFinalView.rows =
          recommendedExceptionalDecisionRows
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows =
          recommendedExceptionalDecisionRows
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
          recommendedExceptionalDecisionRows
      ∧ (∀ p, p ∈ recommendedExceptionalDecisionRows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p : Triplet × ExceptionalDecisionValue,
            p ∈ identityCenteredExceptionalDecisionFinal.rows ↔
              p ∈ recommendedExceptionalDecisionRows)
      ∧ (∀ p : Triplet × ExceptionalDecisionValue,
            p ∈ identityCenteredExceptionalDecisionFinalView.rows ↔
              p ∈ recommendedExceptionalDecisionRows)
      ∧ recommendedCouretExceptionalDecisionEntry.1 = couretTriplet
      ∧ (recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    recommendedExceptionalDecisionRows_length,
    recommendedExceptionalDecisionRows_triplet,
    deprecated_identityCenteredExceptionalDecisionFinal_rows_use_recommended,
    deprecated_identityCenteredExceptionalDecisionFinalSummary_rows_use_recommended,
    deprecated_identityCenteredExceptionalDecisionFinalView_rows_use_recommended,
    deprecated_identityCenteredExceptionalDecisionFinalViewFinal_rows_use_recommended,
    deprecated_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_use_recommended,
    ?_,
    ?_,
    ?_,
    deprecated_couret_entry_use_recommended_triplet,
    deprecated_couret_entry_use_recommended_cases
  ⟩
  · intro p hp
    exact recommendedExceptionalDecisionRows_mem_family hp
  · intro p
    exact deprecated_mem_Final_rows_use_recommended
  · intro p
    exact deprecated_mem_FinalView_rows_use_recommended

end

end CouretUnification.Core