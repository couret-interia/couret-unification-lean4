import CouretUnification.Core.ExceptionalDecisionMigrationLemmasOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Guide local de refactorisation pour la couche canonique des décisions
exceptionnelles sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier n’introduit aucune nouvelle structure mathématique.
Son rôle est purement documentaire et ergonomique :

- fixer les noms qu’il faut désormais privilégier ;
- fournir quelques alias de migration stables ;
- enregistrer des schémas de réécriture usuels pour les futurs fichiers ;
- éviter tout retour à une prolifération de couches `Final...Final...`.

Convention de développement recommandée :

- préférer `exceptionalDecisionCanonicalAPI` à toute nouvelle structure ad hoc ;
- préférer `exceptionalDecisionCanonicalRowsOnIdentityTriplets`
  comme sortie documentaire canonique ;
- utiliser les lemmes de migration de ce fichier ou du fichier
  `ExceptionalDecisionMigrationLemmasOnIdentityTriplets`
  avant d’introduire une nouvelle couche historique.
-/

/--
Alias de guide : nom public recommandé pour la structure canonique
des décisions exceptionnelles sur la famille identité.
-/
abbrev RecommendedExceptionalDecisionAPI :=
  ExceptionalDecisionCanonicalAPI

/--
Alias de guide : nom public recommandé pour la valeur canonique
des décisions exceptionnelles sur la famille identité.
-/
abbrev recommendedExceptionalDecisionAPI :
    RecommendedExceptionalDecisionAPI :=
  exceptionalDecisionCanonicalAPI

/--
Alias de guide : nom recommandé pour la sortie documentaire canonique.
-/
abbrev recommendedExceptionalDecisionRows :
    List (Triplet × ExceptionalDecisionValue) :=
  exceptionalDecisionCanonicalRowsOnIdentityTriplets

/--
Alias de guide : nom recommandé pour l’entrée canonique du cas Couret.
-/
abbrev recommendedCouretExceptionalDecisionEntry :
    Triplet × ExceptionalDecisionValue :=
  couretExceptionalDecisionCanonicalEntryOnIdentityTriplets

/-- Le nom recommandé pour la sortie canonique a bien longueur `21`. -/
theorem recommendedExceptionalDecisionRows_length :
    recommendedExceptionalDecisionRows.length = 21 := by
  exact exceptionalDecisionCanonicalRows_length

/-- Le nom recommandé pour la sortie canonique projette bien sur la famille identité. -/
theorem recommendedExceptionalDecisionRows_triplet :
    recommendedExceptionalDecisionRows.map Prod.fst = identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalRows_triplet

/--
Toute ligne de la sortie recommandée porte bien sur un triplet
de la famille identité.
-/
theorem recommendedExceptionalDecisionRows_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ recommendedExceptionalDecisionRows) :
    p.1 ∈ identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalRows_mem_family hp

/--
Schéma de refactorisation recommandé :
`Final.rows` doit être réécrit vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinal_rows :
    identityCenteredExceptionalDecisionFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinal_rows_toCanonical

/--
Schéma de refactorisation recommandé :
`FinalSummary.rows` doit être réécrit vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalSummary_rows :
    identityCenteredExceptionalDecisionFinalSummary.rows =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalSummary_rows_toCanonical

/--
Schéma de refactorisation recommandé :
`FinalView.rows` doit être réécrit vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalView_rows :
    identityCenteredExceptionalDecisionFinalView.rows =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalView_rows_toCanonical

/--
Schéma de refactorisation recommandé :
`FinalViewFinal.rows` doit être réécrit vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalViewFinal_rows :
    identityCenteredExceptionalDecisionFinalViewFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalViewFinal_rows_toCanonical

/--
Schéma de refactorisation recommandé :
`FinalViewFinalFinal.rows` doit être réécrit vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_toCanonical

/--
Schéma de refactorisation recommandé :
la table décidable `Final`, oubliée vers `(triplet, valeur)`,
doit être réécrite vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalDecidableTable :
    identityCenteredExceptionalDecisionFinalDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalDecidableTable_toCanonical

/--
Schéma de refactorisation recommandé :
la table booléenne `Final`, oubliée vers `(triplet, valeur)`,
doit être réécrite vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalBooleanTable :
    identityCenteredExceptionalDecisionFinalBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalBooleanTable_toCanonical

/--
Schéma de refactorisation recommandé :
la table décidable `FinalView`, oubliée vers `(triplet, valeur)`,
doit être réécrite vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalViewDecidableTable :
    identityCenteredExceptionalDecisionFinalViewDecidableTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalViewDecidableTable_toCanonical

/--
Schéma de refactorisation recommandé :
la table booléenne `FinalView`, oubliée vers `(triplet, valeur)`,
doit être réécrite vers la sortie canonique.
-/
theorem refactor_identityCenteredExceptionalDecisionFinalViewBooleanTable :
    identityCenteredExceptionalDecisionFinalViewBooleanTable.map
        (fun E => (E.triplet, E.value)) =
      recommendedExceptionalDecisionRows := by
  exact identityCenteredExceptionalDecisionFinalViewBooleanTable_toCanonical

/--
Forme `iff` recommandée pour migrer les preuves de membership
sur `Final.rows`.
-/
theorem refactor_mem_Final_rows
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact mem_identityCenteredExceptionalDecisionFinal_rows_iff_canonical

/--
Forme `iff` recommandée pour migrer les preuves de membership
sur `FinalView.rows`.
-/
theorem refactor_mem_FinalView_rows
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalView.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact mem_identityCenteredExceptionalDecisionFinalView_rows_iff_canonical

/--
Forme `iff` recommandée pour migrer les preuves de membership
sur `FinalViewFinal.rows`.
-/
theorem refactor_mem_FinalViewFinal_rows
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact mem_identityCenteredExceptionalDecisionFinalViewFinal_rows_iff_canonical

/--
Forme `iff` recommandée pour migrer les preuves de membership
sur `FinalViewFinalFinal.rows`.
-/
theorem refactor_mem_FinalViewFinalFinal_rows
    {p : Triplet × ExceptionalDecisionValue} :
    p ∈ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows ↔
      p ∈ recommendedExceptionalDecisionRows := by
  exact mem_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_iff_canonical

/--
Le cas Couret recolle bien à l’entrée recommandée stable.
-/
theorem recommendedCouretExceptionalDecisionEntry_triplet :
    recommendedCouretExceptionalDecisionEntry.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalEntry_triplet_rw

/--
Le cas Couret recolle bien à l’une des deux valeurs prévues
dans l’API recommandée.
-/
theorem recommendedCouretExceptionalDecisionEntry_cases :
    recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalEntry_cases_rw

/--
Validation groupée minimale du guide de refactorisation :
- la sortie recommandée est bien calibrée ;
- les couches historiques principales se réécrivent vers elle ;
- le cas Couret recolle bien à l’entrée stable recommandée.
-/
theorem exceptionalDecisionRefactorGuideOnIdentityTriplets_valid :
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
      ∧ recommendedCouretExceptionalDecisionEntry.1 = couretTriplet
      ∧ (recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    recommendedExceptionalDecisionRows_length,
    recommendedExceptionalDecisionRows_triplet,
    refactor_identityCenteredExceptionalDecisionFinal_rows,
    refactor_identityCenteredExceptionalDecisionFinalSummary_rows,
    refactor_identityCenteredExceptionalDecisionFinalView_rows,
    refactor_identityCenteredExceptionalDecisionFinalViewFinal_rows,
    refactor_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows,
    ?_,
    recommendedCouretExceptionalDecisionEntry_triplet,
    recommendedCouretExceptionalDecisionEntry_cases
  ⟩
  intro p hp
  exact recommendedExceptionalDecisionRows_mem_family hp

end

end CouretUnification.Core