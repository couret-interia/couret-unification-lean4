import CouretUnification.Core.ExceptionalDecisionCanonicalQueryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Exemples canoniques d’usage de la couche de requêtage des décisions
exceptionnelles sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne construit aucune nouvelle couche :
il illustre seulement l’usage direct de l’API de requête canonique.
-/

/-- Exemple direct : la sortie de requête a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalQueryExample_length :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_length

/-- Exemple direct : la projection sur les triplets redonne la famille identité. -/
theorem exceptionalDecisionCanonicalQueryExample_triplet :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_triplet

/--
Exemple direct :
tout triplet de la famille identité admet bien une entrée dans la requête canonique.
-/
theorem exceptionalDecisionCanonicalQueryExample_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_hasEntry_of_mem_family hT

/--
Exemple direct :
une occurrence explicite de la valeur `exceptional`
fournit bien une entrée documentaire.
-/
theorem exceptionalDecisionCanonicalQueryExample_exceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_exceptional_implies_hasEntry hT

/--
Exemple direct :
une occurrence explicite de la valeur `nonExceptional`
fournit bien une entrée documentaire.
-/
theorem exceptionalDecisionCanonicalQueryExample_nonExceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_nonExceptional_implies_hasEntry hT

/--
Exemple de requête :
si un triplet apparaît explicitement comme `exceptional`,
alors il appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalQueryExample_exceptional_implies_family
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T) :
    T ∈ identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalQuery_mem_family
      (p := (T, ExceptionalDecisionValue.exceptional))
      hT

/--
Exemple de requête :
si un triplet apparaît explicitement comme `nonExceptional`,
alors il appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalQueryExample_nonExceptional_implies_family
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T) :
    T ∈ identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalQuery_mem_family
      (p := (T, ExceptionalDecisionValue.nonExceptional))
      hT

/--
Exemple sur le cas Couret :
le triplet distingué admet bien une entrée dans la requête canonique.
-/
theorem exceptionalDecisionCanonicalQueryExample_couret_hasEntry :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet := by
  exact couretExceptionalDecisionCanonicalQuery_hasEntry

/--
Exemple sur le cas Couret :
l’entrée canonique stable porte bien sur le triplet distingué.
-/
theorem exceptionalDecisionCanonicalQueryExample_couret_triplet :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalQuery_triplet

/--
Exemple sur le cas Couret :
l’entrée canonique stable prend bien l’une des deux valeurs prévues.
-/
theorem exceptionalDecisionCanonicalQueryExample_couret_cases :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalQuery_cases

/--
Exemple combiné sur le cas Couret :
on regroupe l’existence d’une entrée et la forme de l’entrée canonique stable.
-/
theorem exceptionalDecisionCanonicalQueryExample_couret_bundle :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet
      ∧ couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
       couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
          ExceptionalDecisionValue.nonExceptional) := by
  exact ⟨
    exceptionalDecisionCanonicalQueryExample_couret_hasEntry,
    exceptionalDecisionCanonicalQueryExample_couret_triplet,
    exceptionalDecisionCanonicalQueryExample_couret_cases
  ⟩

/--
Validation groupée minimale des exemples canoniques de requêtage :
- usage direct de la longueur et de la projection ;
- accès à `hasEntry` depuis la famille ;
- accès à `hasEntry` depuis `exceptional` et `nonExceptional` ;
- cas Couret correctement recollé.
-/
theorem exceptionalDecisionCanonicalQueryExamplesOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalQuery.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T)
      ∧ (∀ T,
            identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T →
              identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T)
      ∧ (∀ T,
            identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T →
              identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T)
      ∧ (∀ T,
            identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T →
              T ∈ identityCenteredTriplets)
      ∧ (∀ T,
            identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T →
              T ∈ identityCenteredTriplets)
      ∧ identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet
      ∧ couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    exceptionalDecisionCanonicalQueryExample_length,
    exceptionalDecisionCanonicalQueryExample_triplet,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    exceptionalDecisionCanonicalQueryExample_couret_hasEntry,
    exceptionalDecisionCanonicalQueryExample_couret_triplet,
    exceptionalDecisionCanonicalQueryExample_couret_cases
  ⟩
  · intro T hT
    exact exceptionalDecisionCanonicalQueryExample_hasEntry_of_mem_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalQueryExample_exceptional_implies_hasEntry hT
  · intro T hT
    exact exceptionalDecisionCanonicalQueryExample_nonExceptional_implies_hasEntry hT
  · intro T hT
    exact exceptionalDecisionCanonicalQueryExample_exceptional_implies_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalQueryExample_nonExceptional_implies_family hT

end

end CouretUnification.Core