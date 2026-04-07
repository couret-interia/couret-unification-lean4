import CouretUnification.Core.ExceptionalDecisionCanonicalAPIOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Consommateur canonique des décisions exceptionnelles sur la famille finie
des 21 triplets centrés sur l’identité.

Ce fichier ne construit aucune nouvelle couche documentaire.
Il montre au contraire comment consommer directement l’API canonique stable :

- `exceptionalDecisionCanonicalAPI`
- `exceptionalDecisionCanonicalRowsOnIdentityTriplets`
- `couretExceptionalDecisionCanonicalEntryOnIdentityTriplets`

Il sert de gabarit pour les futurs fichiers “métier” du dépôt.
-/

/--
Nom local pratique pour la sortie documentaire canonique consommée
par les fichiers aval.
-/
abbrev exceptionalDecisionConsumerRowsOnIdentityTriplets :
    List (Triplet × ExceptionalDecisionValue) :=
  exceptionalDecisionCanonicalRowsOnIdentityTriplets

/-- Le consommateur canonique voit bien une sortie de longueur `21`. -/
theorem exceptionalDecisionCanonicalConsumer_length :
    exceptionalDecisionConsumerRowsOnIdentityTriplets.length = 21 := by
  exact exceptionalDecisionCanonicalAPI_length

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem exceptionalDecisionCanonicalConsumer_triplet :
    exceptionalDecisionConsumerRowsOnIdentityTriplets.map Prod.fst =
      identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalAPI_triplet

/--
Toute ligne consommée par l’API canonique porte bien sur un triplet
de la famille identité.
-/
theorem exceptionalDecisionCanonicalConsumer_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets) :
    p.1 ∈ identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalAPI_mem_family hp

/--
Tout triplet de la famille identité admet bien une entrée documentaire
dans la sortie canonique consommée.
-/
theorem exceptionalDecisionCanonicalConsumer_hasEntry
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ∃ v : ExceptionalDecisionValue,
      (T, v) ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets := by
  have hmem :
      T ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets.map Prod.fst := by
    rw [exceptionalDecisionCanonicalConsumer_triplet]
    exact hT
  rcases List.mem_map.mp hmem with ⟨p, hp, hpT⟩
  cases p with
  | mk t v =>
      simp at hpT
      cases hpT
      exact ⟨v, by simpa using hp⟩

/--
Toute ligne consommée par l’API canonique porte une valeur
dans les deux cas prévus par le type de décision.
-/
theorem exceptionalDecisionCanonicalConsumer_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (_hp : p ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  cases h : p.2 <;> simp

/--
Entrée canonique consommée du cas Couret.
-/
abbrev couretExceptionalDecisionConsumerEntryOnIdentityTriplets :
    Triplet × ExceptionalDecisionValue :=
  couretExceptionalDecisionCanonicalEntryOnIdentityTriplets

/--
Dans le cas Couret, l’entrée canonique consommée porte bien
sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalConsumer_triplet :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_triplet

/--
Dans le cas Couret, l’entrée canonique consommée prend bien
l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalConsumer_cases :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalEntryOnIdentityTriplets_cases

/--
Dans le cas Couret, la sortie canonique consommée contient bien
une entrée documentaire pour le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalConsumer_hasEntry :
    ∃ v : ExceptionalDecisionValue,
      (couretTriplet, v) ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets := by
  exact exceptionalDecisionCanonicalConsumer_hasEntry
    couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale du consommateur canonique :
- la sortie est bien calibrée ;
- tout triplet de la famille identité possède une entrée ;
- toute entrée appartient bien à la famille ;
- le cas Couret recolle bien à l’entrée canonique stable.
-/
theorem exceptionalDecisionCanonicalConsumerOnIdentityTriplets_valid :
    exceptionalDecisionConsumerRowsOnIdentityTriplets.length = 21
      ∧ exceptionalDecisionConsumerRowsOnIdentityTriplets.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ p, p ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets →
            p.1 ∈ identityCenteredTriplets)
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ v : ExceptionalDecisionValue,
              (T, v) ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets)
      ∧ (∀ p, p ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets →
            p.2 = ExceptionalDecisionValue.exceptional
              ∨
              p.2 = ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional)
      ∧ (∃ v : ExceptionalDecisionValue,
            (couretTriplet, v) ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets) := by
  refine ⟨
    exceptionalDecisionCanonicalConsumer_length,
    exceptionalDecisionCanonicalConsumer_triplet,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalConsumer_triplet,
    couretExceptionalDecisionCanonicalConsumer_cases,
    couretExceptionalDecisionCanonicalConsumer_hasEntry
  ⟩
  · intro p hp
    exact exceptionalDecisionCanonicalConsumer_mem_family hp
  · intro T hT
    exact exceptionalDecisionCanonicalConsumer_hasEntry hT
  · intro p hp
    exact exceptionalDecisionCanonicalConsumer_value_cases hp

end

end CouretUnification.Core