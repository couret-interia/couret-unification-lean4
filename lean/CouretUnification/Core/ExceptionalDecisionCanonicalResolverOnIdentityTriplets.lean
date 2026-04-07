import CouretUnification.Core.ExceptionalDecisionCanonicalBridgeOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-!
Résolveur canonique minimal des décisions exceptionnelles
sur la famille finie des 21 triplets centrés sur l’identité.

Ce fichier ne crée aucune nouvelle tour documentaire.
Il fournit simplement une interface de résolution à partir du bridge canonique :
pour tout `T ∈ identityCenteredTriplets`, on extrait une entrée canonique
résolue `(T, v)` dans la sortie stable.
-/

/--
Entrée canonique résolue sur la famille identité.
-/
structure IdentityCenteredExceptionalDecisionCanonicalResolvedEntry where
  triplet : Triplet
  inFamily : triplet ∈ identityCenteredTriplets
  value : ExceptionalDecisionValue
  mem_rows :
    (triplet, value) ∈ identityCenteredExceptionalDecisionCanonicalBridge.rows

/--
Résolution canonique d’un triplet de la famille identité :
on extrait une valeur documentaire à partir du bridge canonique.
-/
def resolveExceptionalDecisionCanonicalOnIdentityTriplets
    (T : Triplet)
    (hT : T ∈ identityCenteredTriplets) :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry where
  triplet := T
  inFamily := hT
  value :=
    Classical.choose
      (identityCenteredExceptionalDecisionCanonicalBridge_hasEntry_of_mem_family hT)
  mem_rows :=
    Classical.choose_spec
      (identityCenteredExceptionalDecisionCanonicalBridge_hasEntry_of_mem_family hT)

/--
Résolveur canonique minimal branché sur le bridge stable.
-/
structure IdentityCenteredExceptionalDecisionCanonicalResolver where
  rows : List (Triplet × ExceptionalDecisionValue)
  rows_len : rows.length = 21
  rows_fst : rows.map Prod.fst = identityCenteredTriplets

  resolve :
    ∀ T, T ∈ identityCenteredTriplets →
      IdentityCenteredExceptionalDecisionCanonicalResolvedEntry

  resolve_spec :
    ∀ T hT,
      (resolve T hT).triplet = T
        ∧
      ((resolve T hT).triplet, (resolve T hT).value) ∈ rows

/--
Résolveur canonique minimal :
on réutilise directement le bridge canonique et la fonction de résolution.
-/
def identityCenteredExceptionalDecisionCanonicalResolver :
    IdentityCenteredExceptionalDecisionCanonicalResolver where
  rows := identityCenteredExceptionalDecisionCanonicalBridge.rows
  rows_len := identityCenteredExceptionalDecisionCanonicalBridge.rows_len
  rows_fst := identityCenteredExceptionalDecisionCanonicalBridge.rows_fst

  resolve := resolveExceptionalDecisionCanonicalOnIdentityTriplets

  resolve_spec := by
    intro T hT
    constructor
    · rfl
    · exact
        (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).mem_rows

/-- Le résolveur canonique a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionCanonicalResolver_length :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.length = 21 := by
  exact identityCenteredExceptionalDecisionCanonicalResolver.rows_len

/-- La projection sur les triplets redonne bien la famille identité. -/
theorem identityCenteredExceptionalDecisionCanonicalResolver_triplet :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.map Prod.fst =
      identityCenteredTriplets := by
  exact identityCenteredExceptionalDecisionCanonicalResolver.rows_fst

/--
La résolution canonique recolle bien au triplet demandé.
-/
theorem resolveExceptionalDecisionCanonicalOnIdentityTriplets_triplet
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet = T := by
  rfl

/--
La résolution canonique conserve bien l’appartenance à la famille identité.
-/
theorem resolveExceptionalDecisionCanonicalOnIdentityTriplets_inFamily
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet ∈
      identityCenteredTriplets := by
  simpa using
    (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).inFamily

/--
L’entrée résolue appartient bien à la sortie du bridge canonique.
-/
theorem resolveExceptionalDecisionCanonicalOnIdentityTriplets_mem_rows
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ((resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).triplet,
      (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value) ∈
        identityCenteredExceptionalDecisionCanonicalBridge.rows := by
  exact
    (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).mem_rows

/--
La valeur extraite par résolution est bien l’une des deux valeurs prévues.
-/
theorem resolveExceptionalDecisionCanonicalOnIdentityTriplets_value_cases
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value =
        ExceptionalDecisionValue.exceptional
      ∨
      (resolveExceptionalDecisionCanonicalOnIdentityTriplets T hT).value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    identityCenteredExceptionalDecisionCanonicalBridge_value_cases
      (resolveExceptionalDecisionCanonicalOnIdentityTriplets_mem_rows hT)

/--
Cas Couret : entrée canonique résolue.
-/
def couretExceptionalDecisionCanonicalResolvedEntry :
    IdentityCenteredExceptionalDecisionCanonicalResolvedEntry :=
  resolveExceptionalDecisionCanonicalOnIdentityTriplets
    couretTriplet
    couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue porte bien sur le triplet distingué.
-/
theorem couretExceptionalDecisionCanonicalResolvedEntry_triplet :
    couretExceptionalDecisionCanonicalResolvedEntry.triplet = couretTriplet := by
  exact
    resolveExceptionalDecisionCanonicalOnIdentityTriplets_triplet
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, l’entrée résolue appartient bien à la famille identité.
-/
theorem couretExceptionalDecisionCanonicalResolvedEntry_inFamily :
    couretExceptionalDecisionCanonicalResolvedEntry.triplet ∈
      identityCenteredTriplets := by
  exact
    resolveExceptionalDecisionCanonicalOnIdentityTriplets_inFamily
      couretTriplet_mem_identityCenteredTriplets

/--
Dans le cas Couret, la valeur résolue prend bien l’une des deux valeurs prévues.
-/
theorem couretExceptionalDecisionCanonicalResolvedEntry_cases :
    couretExceptionalDecisionCanonicalResolvedEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretExceptionalDecisionCanonicalResolvedEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact
    resolveExceptionalDecisionCanonicalOnIdentityTriplets_value_cases
      couretTriplet_mem_identityCenteredTriplets

/--
Validation groupée minimale du résolveur canonique :
- calibrage de la sortie ;
- résolution correcte de tout triplet de la famille ;
- spécialisation correcte au cas Couret.
-/
theorem exceptionalDecisionCanonicalResolverOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionCanonicalResolver.rows.length = 21
      ∧ identityCenteredExceptionalDecisionCanonicalResolver.rows.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT).triplet = T)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            ((identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT).triplet,
             (identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT).value) ∈
              identityCenteredExceptionalDecisionCanonicalResolver.rows)
      ∧ (∀ T, ∀ hT : T ∈ identityCenteredTriplets,
            (identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT).value =
                ExceptionalDecisionValue.exceptional
              ∨
              (identityCenteredExceptionalDecisionCanonicalResolver.resolve T hT).value =
                ExceptionalDecisionValue.nonExceptional)
      ∧ couretExceptionalDecisionCanonicalResolvedEntry.triplet = couretTriplet
      ∧ couretExceptionalDecisionCanonicalResolvedEntry.triplet ∈ identityCenteredTriplets
      ∧ (couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretExceptionalDecisionCanonicalResolvedEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionCanonicalResolver_length,
    identityCenteredExceptionalDecisionCanonicalResolver_triplet,
    ?_,
    ?_,
    ?_,
    couretExceptionalDecisionCanonicalResolvedEntry_triplet,
    couretExceptionalDecisionCanonicalResolvedEntry_inFamily,
    couretExceptionalDecisionCanonicalResolvedEntry_cases
  ⟩
  · intro T hT
    exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_triplet hT
  · intro T hT
    simpa using resolveExceptionalDecisionCanonicalOnIdentityTriplets_mem_rows hT
  · intro T hT
    exact resolveExceptionalDecisionCanonicalOnIdentityTriplets_value_cases hT

end

end CouretUnification.Core