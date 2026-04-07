import CouretUnification.Core.ExceptionalDecisionCanonicalConsumerOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Couche canonique minimale de requêtage des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier consomme directement l’API canonique stable et expose
quelques prédicats de requête simples :
- existence d’une entrée pour un triplet ;
- présence explicite de la valeur `exceptional` ;
- présence explicite de la valeur `nonExceptional`.

Il n’introduit aucune nouvelle tour documentaire.
-/

/--
Prédicat canonique de requête :
un triplet admet une entrée documentaire dans la sortie canonique.
-/
def exceptionalDecisionCanonicalHasEntry
    (T : Triplet) : Prop :=
  ∃ v : ExceptionalDecisionValue,
    (T, v) ∈ exceptionalDecisionConsumerRowsOnIdentityTriplets

/--
Prédicat canonique de requête :
le triplet apparaît explicitement avec la valeur `exceptional`.
-/
def exceptionalDecisionCanonicalIsExceptional
    (T : Triplet) : Prop :=
  (T, ExceptionalDecisionValue.exceptional) ∈
    exceptionalDecisionConsumerRowsOnIdentityTriplets

/--
Prédicat canonique de requête :
le triplet apparaît explicitement avec la valeur `nonExceptional`.
-/
def exceptionalDecisionCanonicalIsNonExceptional
    (T : Triplet) : Prop :=
  (T, ExceptionalDecisionValue.nonExceptional) ∈
    exceptionalDecisionConsumerRowsOnIdentityTriplets

/--
Version décidable calculatoire du prédicat d’existence d’entrée.
-/
def exceptionalDecisionCanonicalHasEntryDecidable
    (T : Triplet) :
    Decidable (exceptionalDecisionCanonicalHasEntry T) := by
  classical
  infer_instance

/--
Version décidable calculatoire du prédicat `exceptional`.
-/
def exceptionalDecisionCanonicalIsExceptionalDecidable
    (T : Triplet) :
    Decidable (exceptionalDecisionCanonicalIsExceptional T) := by
  classical
  infer_instance

/--
Version décidable calculatoire du prédicat `nonExceptional`.
-/
def exceptionalDecisionCanonicalIsNonExceptionalDecidable
    (T : Triplet) :
    Decidable (exceptionalDecisionCanonicalIsNonExceptional T) := by
  classical
  infer_instance

/--
Objet canonique minimal de requêtage branché sur la sortie stable.
-/
structure IdentityCenteredExceptionalDecisionCanonicalQuery where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  hasEntry : Triplet → Prop
  hasEntry_spec :
    ∀ T, hasEntry T =
      (∃ v : ExceptionalDecisionValue, (T, v) ∈ rows)

  isExceptional : Triplet → Prop
  isExceptional_spec :
    ∀ T, isExceptional T =
      (((T, ExceptionalDecisionValue.exceptional) ∈ rows))

  isNonExceptional : Triplet → Prop
  isNonExceptional_spec :
    ∀ T, isNonExceptional T =
      (((T, ExceptionalDecisionValue.nonExceptional) ∈ rows))

/--
Requête canonique minimale :
on branche directement les prédicats de requête sur la sortie canonique stable.
-/
def identityCenteredExceptionalDecisionCanonicalQuery :
    IdentityCenteredExceptionalDecisionCanonicalQuery where
  rows := exceptionalDecisionConsumerRowsOnIdentityTriplets
  rows_len := exceptionalDecisionCanonicalConsumer_length
  rows_fst := exceptionalDecisionCanonicalConsumer_triplet

  hasEntry := exceptionalDecisionCanonicalHasEntry
  hasEntry_spec := by intro _; rfl

  isExceptional := exceptionalDecisionCanonicalIsExceptional
  isExceptional_spec := by intro _; rfl

  isNonExceptional := exceptionalDecisionCanonicalIsNonExceptional
  isNonExceptional_spec := by intro _; rfl

/-- La sortie de la requête canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalQuery_length :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalQuery.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalQuery_triplet :
    identityCenteredExceptionalDecisionCanonicalQuery.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalQuery.rows_fst

/--
Tout triplet de la famille identité admet bien une entrée dans la requête canonique.
-/
theorem identityCenteredExceptionalDecisionCanonicalQuery_hasEntry_of_mem_family
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact exceptionalDecisionCanonicalConsumer_hasEntry hT

/--
Une occurrence explicite de la valeur `exceptional` fournit bien une entrée.
-/
theorem identityCenteredExceptionalDecisionCanonicalQuery_exceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact ⟨ExceptionalDecisionValue.exceptional, hT⟩

/--
Une occurrence explicite de la valeur `nonExceptional` fournit bien une entrée.
-/
theorem identityCenteredExceptionalDecisionCanonicalQuery_nonExceptional_implies_hasEntry
    {T : Triplet}
    (hT : identityCenteredExceptionalDecisionCanonicalQuery.isNonExceptional T) :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry T := by
  exact ⟨ExceptionalDecisionValue.nonExceptional, hT⟩

/--
Toute entrée de la requête canonique porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionCanonicalQuery_mem_family
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows) :
    p.1 ∈ identityCenteredTriplets := by
  exact exceptionalDecisionCanonicalConsumer_mem_family hp

/--
Toute entrée de la requête canonique prend bien l’une des deux valeurs prévues.
-/
theorem identityCenteredExceptionalDecisionCanonicalQuery_value_cases
    {p : Triplet × ExceptionalDecisionValue}
    (hp : p ∈ identityCenteredExceptionalDecisionCanonicalQuery.rows) :
    p.2 = ExceptionalDecisionValue.exceptional
      ∨
      p.2 = ExceptionalDecisionValue.nonExceptional := by
  exact exceptionalDecisionCanonicalConsumer_value_cases hp

/--
Cas Couret : le triplet distingué admet bien une entrée dans la requête canonique.
-/
theorem couretExceptionalDecisionCanonicalQuery_hasEntry :
    identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet := by
  exact
    identityCenteredExceptionalDecisionCanonicalQuery_hasEntry_of_mem_family
      couretTriplet_mem_identityCenteredTriplets

/--
Cas Couret : l’entrée canonique stable porte bien sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalQuery_triplet :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet := by
  exact couretExceptionalDecisionCanonicalConsumer_triplet

/--
Cas Couret : l’entrée canonique stable prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalQuery_cases :
    couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretExceptionalDecisionCanonicalConsumer_cases

/--
Validation groupée minimale de la couche canonique de requête
sur la famille identité.
-/
theorem exceptionalDecisionCanonicalQueryOnIdentityTriplets_valid :
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
      ∧ identityCenteredExceptionalDecisionCanonicalQuery.hasEntry couretTriplet
      ∧ couretExceptionalDecisionConsumerEntryOnIdentityTriplets.1 = couretTriplet
      ∧ (couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionConsumerEntryOnIdentityTriplets.2 =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalQuery_length,
    identityCenteredExceptionalDecisionCanonicalQuery_triplet,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalQuery_hasEntry,
    couretExceptionalDecisionCanonicalQuery_triplet,
    couretExceptionalDecisionCanonicalQuery_cases
  ⟩
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalQuery_mem_family hp
  · intro p hp
    exact identityCenteredExceptionalDecisionCanonicalQuery_value_cases hp
  · intro T hT
    exact identityCenteredExceptionalDecisionCanonicalQuery_hasEntry_of_mem_family hT

end

end CouretUnification.Core