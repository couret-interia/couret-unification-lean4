import CouretUnification.Core.ExceptionalDecisionDeprecationMapOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Exemples canoniques d’usage de l’API stable des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

But :
- illustrer l’usage direct de `recommendedExceptionalDecisionRows` ;
- montrer comment réécrire les anciennes couches historiques vers l’API canonique ;
- fournir quelques modèles courts pour les futurs refactorings.
-/

/-- Exemple direct : la sortie canonique recommandée a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalExample_length :
    recommendedExceptionalDecisionRows.length = 21 := by
  exact recommendedExceptionalDecisionRows_length

/-- Exemple direct : la projection sur les triplets redonne la famille identité. -/
theorem exceptionalDecisionCanonicalExample_triplet :
    recommendedExceptionalDecisionRows.map Prod.fst = identityCenteredTriplets := by
  exact recommendedExceptionalDecisionRows_triplet

/--
Exemple de migration :
une preuve de membership sur `Final.rows` se transporte immédiatement
vers la sortie canonique recommandée.
-/
theorem exceptionalDecisionCanonicalExample_mem_fromFinal
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinal.rows) :
    p ∈ recommendedExceptionalDecisionRows := by
  exact (deprecated_mem_Final_rows_use_recommended).mp hp

/--
Exemple de migration :
une ligne provenant de `Final.rows` porte bien sur un triplet
de la famille identité après passage à l’API canonique.
-/
theorem exceptionalDecisionCanonicalExample_mem_family_fromFinal
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionFinal.rows) :
    p.1 ∈ identityCenteredTriplets := by
  have hp' : p ∈ recommendedExceptionalDecisionRows := by
    exact (deprecated_mem_Final_rows_use_recommended).mp hp
  exact recommendedExceptionalDecisionRows_mem_family hp'

/--
Exemple de réécriture :
on remplace directement `FinalView.rows` par la sortie canonique,
puis on conclut avec le lemme stable sur la projection.
-/
theorem exceptionalDecisionCanonicalExample_rewrite_FinalView :
    identityCenteredExceptionalDecisionFinalView.rows.map Prod.fst =
      identityCenteredTriplets := by
  rw [deprecated_identityCenteredExceptionalDecisionFinalView_rows_use_recommended]
  exact recommendedExceptionalDecisionRows_triplet

/--
Exemple de réécriture :
on remplace directement `FinalViewFinal.rows` par la sortie canonique,
puis on conclut avec le lemme stable sur la projection.
-/
theorem exceptionalDecisionCanonicalExample_rewrite_FinalViewFinal :
    identityCenteredExceptionalDecisionFinalViewFinal.rows.map Prod.fst =
      identityCenteredTriplets := by
  rw [deprecated_identityCenteredExceptionalDecisionFinalViewFinal_rows_use_recommended]
  exact recommendedExceptionalDecisionRows_triplet

/--
Exemple de réécriture :
on remplace directement `FinalViewFinalFinal.rows` par la sortie canonique,
puis on conclut avec le lemme stable sur la projection.
-/
theorem exceptionalDecisionCanonicalExample_rewrite_FinalViewFinalFinal :
    identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.map Prod.fst =
      identityCenteredTriplets := by
  rw [deprecated_identityCenteredExceptionalDecisionFinalViewFinalFinal_rows_use_recommended]
  exact recommendedExceptionalDecisionRows_triplet

/--
Exemple sur le cas Couret :
l’entrée canonique recommandée porte bien sur le triplet distingué.
-/
theorem exceptionalDecisionCanonicalExample_couret_triplet :
    recommendedCouretExceptionalDecisionEntry.1 = couretTriplet := by
  exact recommendedCouretExceptionalDecisionEntry_triplet

/--
Exemple sur le cas Couret :
la valeur documentaire canonique prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalExample_couret_cases :
    recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      recommendedCouretExceptionalDecisionEntry.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact recommendedCouretExceptionalDecisionEntry_cases

/--
Exemple combiné :
l’entrée canonique recommandée du cas Couret est bien calibrée.
-/
theorem exceptionalDecisionCanonicalExample_couret_entry :
    recommendedCouretExceptionalDecisionEntry.1 = couretTriplet
      ∧
      (recommendedCouretExceptionalDecisionEntry.2 =
          ExceptionalDecisionValue.exceptional
        ∨
       recommendedCouretExceptionalDecisionEntry.2 =
          ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    recommendedCouretExceptionalDecisionEntry_triplet,
    recommendedCouretExceptionalDecisionEntry_cases
  ⟩

/--
Validation groupée minimale des exemples canoniques :
- usage direct de l’API recommandée ;
- transport depuis une couche historique ;
- réécriture des principales vues historiques ;
- cas Couret correctement recollé à l’entrée stable.
-/
theorem exceptionalDecisionCanonicalExamplesOnIdentityTriplets_valid :
    recommendedExceptionalDecisionRows.length = 21
      ∧ recommendedExceptionalDecisionRows.map Prod.fst = identityCenteredTriplets
      ∧ (∀ p : Triplet × ExceptionalDecisionValue,
            p ∈ identityCenteredExceptionalDecisionFinal.rows →
              p ∈ recommendedExceptionalDecisionRows)
      ∧ (∀ p : Triplet × ExceptionalDecisionValue,
            p ∈ identityCenteredExceptionalDecisionFinal.rows →
              p.1 ∈ identityCenteredTriplets)
      ∧ identityCenteredExceptionalDecisionFinalView.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionFinalViewFinalFinal.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ recommendedCouretExceptionalDecisionEntry.1 = couretTriplet
      ∧ (recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          recommendedCouretExceptionalDecisionEntry.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    exceptionalDecisionCanonicalExample_length,
    exceptionalDecisionCanonicalExample_triplet,
    ?_,
    ?_,
    exceptionalDecisionCanonicalExample_rewrite_FinalView,
    exceptionalDecisionCanonicalExample_rewrite_FinalViewFinal,
    exceptionalDecisionCanonicalExample_rewrite_FinalViewFinalFinal,
    exceptionalDecisionCanonicalExample_couret_triplet,
    exceptionalDecisionCanonicalExample_couret_cases
  ⟩
  · intro p hp
    exact exceptionalDecisionCanonicalExample_mem_fromFinal hp
  · intro p hp
    exact exceptionalDecisionCanonicalExample_mem_family_fromFinal hp

end

end CouretUnification.Core