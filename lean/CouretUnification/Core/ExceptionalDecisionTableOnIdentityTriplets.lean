import CouretUnification.Core.ExceptionalDecisionOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Table documentaire purement locale des décisions canoniques
sur la famille finie des 21 triplets centrés sur l’identité.

À chaque triplet de `identityCenteredTriplets`, on associe
sa décision canonique ponctuelle déjà construite.
-/
def identityCenteredExceptionalDecisionTable :
    List IdentityCenteredExceptionalDecision :=
  identityCenteredTriplets.attach.map
    (fun T =>
      canonicalIdentityCenteredExceptionalDecision
        T.1
        T.2)

/-- La table documentaire des décisions canoniques a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionTable_length :
    identityCenteredExceptionalDecisionTable.length = 21 := by
  simp [identityCenteredExceptionalDecisionTable, identityCenteredTriplets_length]

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalDecisionTable_triplet :
    identityCenteredExceptionalDecisionTable.map
        (fun D => D.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionTable
  simp [canonicalIdentityCenteredExceptionalDecision]

/--
Projection documentaire minimale de la table des décisions :
on oublie les preuves et on ne garde que les couples
`(triplet, valeur de décision)`.
-/
def identityCenteredExceptionalDecisionValueTable :
    List (Triplet × ExceptionalDecisionValue) :=
  identityCenteredExceptionalDecisionTable.map
    (fun D => (D.triplet, D.value))

/-- La table des couples `(triplet, décision)` a bien longueur `21`. -/
theorem identityCenteredExceptionalDecisionValueTable_length :
    identityCenteredExceptionalDecisionValueTable.length = 21 := by
  simp [identityCenteredExceptionalDecisionValueTable,
    identityCenteredExceptionalDecisionTable_length]

/-- La projection sur les triplets redonne encore la famille finie source. -/
theorem identityCenteredExceptionalDecisionValueTable_triplet :
    identityCenteredExceptionalDecisionValueTable.map Prod.fst =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalDecisionValueTable
  rw [List.map_map]
  have hfun :
      (Prod.fst ∘
        fun D : IdentityCenteredExceptionalDecision =>
          (D.triplet, D.value)) =
        (fun D : IdentityCenteredExceptionalDecision => D.triplet) := by
    funext D
    rfl
  rw [hfun]
  exact identityCenteredExceptionalDecisionTable_triplet

/--
Toute décision présente dans la table porte bien sur un triplet
de la famille identité.
-/
theorem identityCenteredExceptionalDecisionTable_mem_family
    {D : IdentityCenteredExceptionalDecision}
    (hD : D ∈ identityCenteredExceptionalDecisionTable) :
    D.triplet ∈ identityCenteredTriplets := by
  have hmem :
      D.triplet ∈ identityCenteredExceptionalDecisionTable.map (fun E => E.triplet) := by
    exact List.mem_map.mpr ⟨D, hD, rfl⟩
  simpa [identityCenteredExceptionalDecisionTable_triplet] using hmem

/--
Tout triplet de la famille identité admet bien une entrée
dans la table documentaire des décisions canoniques.
-/
theorem identityCenteredExceptionalDecisionTable_hasEntry
    {T : Triplet}
    (hT : T ∈ identityCenteredTriplets) :
    ∃ D ∈ identityCenteredExceptionalDecisionTable, D.triplet = T := by
  unfold identityCenteredExceptionalDecisionTable
  refine ⟨canonicalIdentityCenteredExceptionalDecision T hT, ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨⟨T, hT⟩, ?_, rfl⟩
  simp

/--
Toute entrée de la table des décisions canoniques recolle bien
avec la partition canonique.
-/
theorem identityCenteredExceptionalDecisionTable_mem_partition
    {D : IdentityCenteredExceptionalDecision}
    (_hD : D ∈ identityCenteredExceptionalDecisionTable) :
    D.triplet ∈ identityCenteredExceptionalPartition.exceptionalPart
      ∨
      D.triplet ∈ identityCenteredExceptionalPartition.nonExceptionalPart := by
  exact D.mem_partition

/--
Cas Couret : entrée canonique de la table des décisions.
-/
def couretIdentityCenteredExceptionalDecisionTableEntry :
    IdentityCenteredExceptionalDecision :=
  couretIdentityCenteredExceptionalDecision

/--
Dans le cas Couret, l’entrée canonique de la table porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalDecisionTableEntry_triplet :
    couretIdentityCenteredExceptionalDecisionTableEntry.triplet =
      couretTriplet := by
  exact couretIdentityCenteredExceptionalDecision_triplet

/--
Dans le cas Couret, l’entrée canonique de la table appartient bien
à la famille identité.
-/
theorem couretIdentityCenteredExceptionalDecisionTableEntry_inFamily :
    couretIdentityCenteredExceptionalDecisionTableEntry.triplet ∈
      identityCenteredTriplets := by
  exact couretIdentityCenteredExceptionalDecision_inFamily

/--
Dans le cas Couret, l’entrée canonique de la table prend bien
l’une des deux valeurs de décision prévues.
-/
theorem couretIdentityCenteredExceptionalDecisionTableEntry_cases :
    couretIdentityCenteredExceptionalDecisionTableEntry.value =
        ExceptionalDecisionValue.exceptional
      ∨
      couretIdentityCenteredExceptionalDecisionTableEntry.value =
        ExceptionalDecisionValue.nonExceptional := by
  exact couretIdentityCenteredExceptionalDecision_cases

/--
Validation groupée minimale de la table documentaire des décisions canoniques
sur la famille identité.
-/
theorem exceptionalDecisionTableOnIdentityTriplets_valid :
    identityCenteredExceptionalDecisionTable.length = 21
      ∧ identityCenteredExceptionalDecisionTable.map
          (fun D => D.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalDecisionValueTable.length = 21
      ∧ identityCenteredExceptionalDecisionValueTable.map Prod.fst =
          identityCenteredTriplets
      ∧ (∀ T, T ∈ identityCenteredTriplets →
            ∃ D ∈ identityCenteredExceptionalDecisionTable, D.triplet = T)
      ∧ (∀ D, D ∈ identityCenteredExceptionalDecisionTable →
            D.triplet ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalDecisionTableEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalDecisionTableEntry.triplet ∈
          identityCenteredTriplets
      ∧ (couretIdentityCenteredExceptionalDecisionTableEntry.value =
            ExceptionalDecisionValue.exceptional
          ∨
          couretIdentityCenteredExceptionalDecisionTableEntry.value =
            ExceptionalDecisionValue.nonExceptional) := by
  refine ⟨
    identityCenteredExceptionalDecisionTable_length,
    identityCenteredExceptionalDecisionTable_triplet,
    identityCenteredExceptionalDecisionValueTable_length,
    identityCenteredExceptionalDecisionValueTable_triplet,
    ?_,
    ?_,
    couretIdentityCenteredExceptionalDecisionTableEntry_triplet,
    couretIdentityCenteredExceptionalDecisionTableEntry_inFamily,
    couretIdentityCenteredExceptionalDecisionTableEntry_cases
  ⟩
  · intro T hT
    exact identityCenteredExceptionalDecisionTable_hasEntry hT
  · intro D hD
    exact identityCenteredExceptionalDecisionTable_mem_family hD

end

end CouretUnification.Core