import CouretUnification.Core.ExceptionalDecisionCanonicalQueryOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Petite bibliothèque de faits canoniques réutilisables sur la couche de requête
des décisions exceptionnelles sur la famille finie des 21 triplets centrés
sur l’identité.

Ce fichier ne crée aucune nouvelle structure.
Il regroupe seulement des faits courts et réutilisables bâtis directement sur
la couche de requête canonique.
-/

/-- La sortie de requête canonique a bien longueur `21`. -/
theorem exceptionalDecisionCanonicalFacts_length :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_length

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem exceptionalDecisionCanonicalFacts_triplet :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_triplet

/--
Toute ligne de la sortie canonique de requête porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionCanonicalFacts_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_mem_family hp

/--
Toute ligne de la sortie canonique de requête prend bien l’une des deux valeurs
documentaires prévues.
-/
theorem exceptionalDecisionCanonicalFacts_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_value_cases hp

/--
Tout triplet de la famille identité admet bien une entrée documentaire
dans la requête canonique.
-/
theorem exceptionalDecisionCanonicalFacts_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_hasEntry_of_mem_family hT

/--
Une occurrence explicite de la valeur `exceptional`
fournit bien une entrée documentaire.
-/
theorem exceptionalDecisionCanonicalFacts_exceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_exceptional_implies_hasEntry hT

/--
Une occurrence explicite de la valeur `nonExceptional`
fournit bien une entrée documentaire.
-/
theorem exceptionalDecisionCanonicalFacts_nonExceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact identityCenteredExceptionalDecisionCanonicalQuery_nonExceptional_implies_hasEntry hT

/--
Si un triplet apparaît explicitement comme `exceptional`,
alors il appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalFacts_exceptional_implies_family
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T) :
    T ∈ identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalQuery_mem_family
      (p := (T, ExceptionalDecisionValue.exceptional))
      hT

/--
Si un triplet apparaît explicitement comme `nonExceptional`,
alors il appartient bien à la famille identité.
-/
theorem exceptionalDecisionCanonicalFacts_nonExceptional_implies_family
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T) :
    T ∈ identityCenteredTriplets := by
  exact
    identityCenteredExceptionalDecisionCanonicalQuery_mem_family
      (p := (T, ExceptionalDecisionValue.nonExceptional))
      hT

/--
Toute occurrence explicite `exceptional` porte automatiquement
une valeur documentaire bien formée.
-/
theorem exceptionalDecisionCanonicalFacts_exceptional_value_cases :
    ExceptionalDecisionValue.exceptional = ExceptionalDecisionValue.exceptional
      ∨
      ExceptionalDecisionValue.exceptional = ExceptionalDecisionValue.nonExceptional := by
  exact Or.inl rfl

/--
Toute occurrence explicite `nonExceptional` porte automatiquement
une valeur documentaire bien formée.
-/
theorem exceptionalDecisionCanonicalFacts_nonExceptional_value_cases :
    ExceptionalDecisionValue.nonExceptional = ExceptionalDecisionValue.exceptional
      ∨
      ExceptionalDecisionValue.nonExceptional = ExceptionalDecisionValue.nonExceptional := by
  exact Or.inr rfl

/--
Cas Couret : le triplet distingué admet bien une entrée dans la requête canonique.
-/
theorem couretExceptionalDecisionCanonicalFacts_hasEntry :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet := by
  exact couretExceptionalDecisionCanonicalQuery_hasEntry

/--
Cas Couret : l’entrée canonique stable porte bien sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalFacts_triplet :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalQuery_triplet

/--
Cas Couret : l’entrée canonique stable prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalFacts_cases :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalQuery_cases

/--
Cas Couret : le triplet distingué appartient bien à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalFacts_family :
    couretTriplet ∈ identityCenteredTriplets := by
  exact couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale de la bibliothèque de faits canoniques :
- calibrage de la sortie de requête ;
- faits de famille et d’existence d’entrée ;
- propagation depuis `exceptional` et `nonExceptional` ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalFactsOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalQuery.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ p, p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
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
            ExceptionalDecisionValue.nonExceptional)
      ∧ couretTriplet ∈ identityCenteredTriplets := by
  refine ⟨
    exceptionalDecisionCanonicalFacts_length,
    exceptionalDecisionCanonicalFacts_triplet,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalFacts_hasEntry,
    couretExceptionalDecisionCanonicalFacts_triplet,
    couretExceptionalDecisionCanonicalFacts_cases,
    couretExceptionalDecisionCanonicalFacts_family
  ⟩
  · intro p hp
    exact exceptionalDecisionCanonicalFacts_mem_family hp
  · intro p hp
    exact exceptionalDecisionCanonicalFacts_value_cases hp
  · intro T hT
    exact exceptionalDecisionCanonicalFacts_hasEntry_of_mem_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalFacts_exceptional_implies_hasEntry hT
  · intro T hT
    exact exceptionalDecisionCanonicalFacts_nonExceptional_implies_hasEntry hT
  · intro T hT
    exact exceptionalDecisionCanonicalFacts_exceptional_implies_family hT
  · intro T hT
    exact exceptionalDecisionCanonicalFacts_nonExceptional_implies_family hT

end

end CouretUnification.Core